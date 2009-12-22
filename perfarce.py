# Mercurial extension to push to and pull from Perforce depots.
#
# Copyright 2009 Frank Kingswood <frank@kingswood-consulting.co.uk>
#
# This software may be used and distributed according to the terms of the
# GNU General Public License version 2, incorporated herein by reference.

'''Push to or pull from Perforce depots

This extension modifies the remote repository handling so that repository
paths that resemble
    p4://p4server[:port]/clientname
cause operations on the named p4 client specification on the p4 server.
The client specification must already exist on the server before using
this extension. Making changes to the client specification Views causes
problems when synchronizing the repositories, and should be avoided.

Four built-in commands are overridden:

    hg outgoing: If the destination repository name starts with p4:// then this
                 reports files affected by the revision(s) that are in the
                 local repository but not in the p4 depot.

    hg push:     Now can export changes from the local repository to the p4
                 depot. If no revision is specified then all changes since the
                 last p4 changelist are pushed. In either case, all revisions
                 to be pushed are foled into a single p4 changelist. Optionally
                 the resulting changelist is submitted to the p4 server,
                 controlled by the --submit option to push, or by setting
                    --config perfarce.submit=True
                 If the option
                    --config perfarce.keep=False
                 is False then after a successful submit the files in the
                 p4 workarea will be deleted.

    hg pull:     Now can import changes from the p4 depot, automatically
                 creating merges of changelists submitted by hg push.
                 If the option
                    --config perfarce.keep=False
                 is False then the import does not leave files in the p4
                 workarea, otherwise the p4 workarea will be updated
                 with the new files.

    hg incoming: If the source repository name starts with p4:// then this
                 reports changes in the p4 depot that are not yet in the
                 local repository.

Two additional commands are implemented:

    hg p4submit:   Submit a changelist to the p4 depot, then pull the latest
                   changes from the p4 depot. 

    hg p4identify: Show the most recent revision that was imported from p4.
'''

from mercurial import cmdutil, commands, context, extensions, hg, util
from mercurial.i18n import _
from hgext.convert.p4 import loaditer

from hgext.convert.hg import mercurial_sink
from hgext.convert.convcmd import converter

import marshal, tempfile, os, re

def uisetup(ui):
    '''monkeypatch pull and push for p4:// support'''
    
    extensions.wrapcommand(commands.table, 'pull', pull)
    p = extensions.wrapcommand(commands.table, 'push', push)
    p[1].append(('', 'submit', None, 'for p4:// destination submit new changelist to server'))
    extensions.wrapcommand(commands.table, 'incoming', incoming)
    extensions.wrapcommand(commands.table, 'outgoing', outgoing)

# --------------------------------------------------------------------------

class p4client:

    def __init__(self, ui, repo, path):
        'initialize a p4client class from the remote path'

        try:
            assert path.startswith('p4://')

            self.ui = ui
            self.repo = repo
            self.server = None
            self.client = None
            self.root = None
            self.keep = ui.configbool('perfarce', 'keep', True)

            # caches
            self.wherecache = {}
            self.p4stat = None
            self.p4statdirty = False

            # helpers to parse p4 output
            self.re_type = re.compile('([a-z]+)?(text|binary|symlink|apple|resource|unicode|utf\d+)(\+\w+)?$')
            self.re_keywords = re.compile(r'\$(Id|Header|Date|DateTime|Change|File|Revision|Author):[^$\n]*\$')
            self.re_keywords_old = re.compile('\$(Id|Header):[^$\n]*\$')
            self.re_hgid = re.compile('{{mercurial (([0-9a-f]{40})(:([0-9a-f]{40}))?)}}')
            self.re_number = re.compile('.+ ([0-9]+) .+')
            self.actions = { 'edit':'M', 'add':'A', 'delete':'R', 'branch':'A', 'integrate':'M' }

            self.authors = {}

            s, c = path[5:].split('/')
            if ':' not in s:
                s = '%s:1666' % s
            self.server = s
            if c:
                d = self.runs('client -o "%s"' % c)
                for n in ['Root'] + ['AltRoots%d' % i for i in range(9)]:
                    if n in d and os.path.isdir(d[n]):
                        self.root = util.pconvert(d[n])
                        break
                self.client=c
        except:
            raise util.Abort(_('not a p4 repository'))

    
    def close(self):
        'clean up any client state'
        if self.p4statdirty:
            self._writep4stat()


    def latest(self):
        '''Find the most recent changelist which has the p4 extra data which
        gives the p4 changelist it was converted from'''
        for rev in xrange(len(self.repo)-1, -1, -1):
            ctx = self.repo[rev]
            extra = ctx.extra()
            if 'p4' in extra:
                return ctx.node(), int(extra['p4'])
        raise util.Abort(_('no p4 changelist revision found'))


    def decodetype(self, p4type):
        'decode p4 type name into mercurial mode string and keyword substitution regex'

        mode = ''
        keywords = None
        p4type = self.re_type.match(p4type)
        if p4type:
            flags = (p4type.group(1) or '') + (p4type.group(3) or '')
            if 'x' in flags:
                mode = 'x'
            if p4type.group(2) == 'symlink':
                mode = 'l'
            if 'ko' in flags:
                keywords = re_keywords_old
            elif 'k' in flags:
                keywords = re_keywords
        return mode, keywords

    SUBMITTED = 'submitted'
    def getpending(self, node):
        '''return p4 submission state for node: SUBMITTED, a changelist
        number if pending or None if not in a changelist'''
        if self.p4stat is None:
            self._readp4stat()
        return self.p4stat.get(node, None)

    def setpending(self, node, state):
        '''set p4 submission state for node: SUBMITTED, a changelist
        number if pending or None if not in a changelist'''
        r = self.getpending(node)
        if r != state:
            self.p4statdirty = True
            if state is None:
                del self.p4stat[node]
            else:
                self.p4stat[node] = state

    def getpendingdict(self):
        'return p4 submission state dictionary'
        if self.p4stat is None:
            self._readp4stat()
        return self.p4stat

    def _readp4stat(self):
        'read .hg/p4stat file'
        self.p4stat = {}
        try:
            for line in self.repo.opener('p4stat', 'r', text=True):
                line = line.strip().split(' ',1)
                if line[1].startswith('s'):
                    state = self.SUBMITTED
                else:
                    state = int(line[1])
                self.p4stat[line[0]] = state
        except:
            self.ui.note('error reading p4stat')
        self.ui.debug('read p4stat=%r\n' % self.p4stat)
        self.p4statdirty = False

    def _writep4stat(self):
        'write .hg/p4stat file'
        fd = self.repo.opener('p4stat', 'w', text=True)
        for n in self.p4stat:
            fd.write('%s %s\n' % (n, self.p4stat[n]))
        fd.close()
        self.p4statdirty = False
        self.ui.debug('write p4stat=%r\n' % self.p4stat)


    def run(self, cmd, abort=True):
        'Run a P4 command and yield the objects returned'

        c = ['p4', '-G']
        if self.server:
            c.append('-p')
            c.append(self.server)
        if self.client:
            c.append('-c')
            c.append(self.client)
        c.append(cmd)
        cmd = ' '.join(c)

        if self.ui.debugflag: self.ui.debug('> %s\n'%cmd)
        old=os.getcwd()
        try:
            if self.root:
                os.chdir(self.root)
            for d in loaditer(util.popen(cmd, mode='rb')):
                if self.ui.debugflag: self.ui.debug('< %r\n'%d)
                code = d.get('code')
                data = d.get('data')
                if code is not None and data is not None:
                    if abort and code == 'error':
                        raise util.Abort(d['generic'], 'p4: %s' % data)
                    elif code == 'info':
                        self.ui.note('p4: %s\n' % data)
                yield d
        finally:
            os.chdir(old)


    def runs(self, cmd, abort=True):
        'Run a P4 command and return first object, or False if more, or None'
        r = None
        for d in self.run(cmd, abort):
            if r is None:
                r = d
            else:
                r = False
        return r


    def describe(self, change, files=None):
        'Return p4 changelist description and optionally the files affected'

        desc = user = date = None
        d = self.runs('describe -s %d' % change)
        desc = d['desc']
        user = d['user']
        if user in self.authors:
            user = self.authors[user]
        date = (int(d['time']), 0)     # p4 uses UNIX epoch

        if files:
            files = []
            i = 0
            while ('depotFile%d' % i) in d and ('rev%d' % i) in d:
                df = d['depotFile%d' % i]
                if df in self.wherecache:
                    lf = self.wherecache[df]
                else:
                    where = self.runs('where "%s"' % df, abort=False)
                    if where['code'] == 'error':
                        if where['data'].endswith('file(s) not in client view.\n'):
                            i += 1
                            continue
                        else:
                            raise util.Abort(where['data'])
                    lf = where['path']
                    lf = util.pconvert(lf)
                    if lf.startswith('%s/' % self.root):
                        lf = lf[len(self.root) + 1:]
                    else:
                        raise util.Abort(_('invalid p4 local path %s') % lf)
                    self.wherecache[df] = lf
                action = self.actions[d['action%d' % i]]
                files.append((df, lf, d['rev%d' % i], d['type%d' % i], action))
                i += 1

        return desc, user, date, files


    def getfile(self, filet, change):
        'Return contents of a file in the p4 depot at the given change number'
        
        mode, keywords = self.decodetype(filet[3])

        if self.keep:

            self.runs('sync "%s"@%s' % (filet[0], change), abort=False)
            fn = os.sep.join([self.root, filet[1]])
            fn = util.localpath(fn)
            if mode == 'l':
                contents = os.readlink(fn)
            else:
                contents = file(fn, 'rb').read()
        else:
            contents = []
            for d in self.run('print "%s"@%s' % (filet[0], change)):
                code = d['code']
                if code == 'text' or code == 'binary':
                    contents.append(d['data'])

            contents = ''.join(contents)
            if mode == 'l' and contents.endswith('\n'):
                contents = contents[:-1]

        if keywords:
            contents = keywords.sub('$\\1$', contents)

        return mode, contents


    @staticmethod
    def pullcommon(original, ui, repo, source, **opts):
        'Shared code for pull and incoming'

        source, revs, checkout = hg.parseurl(ui.expandpath(source or 'default'), opts.get('rev'))

        try:
            client = p4client(ui, repo, source)
        except:
            return True, original(ui, repo, source, **opts)

        if len(repo):
            p4rev, p4id = client.latest()
        else:
            p4rev = None
            p4id = 0

        changes = []
        for d in client.run('changes -s submitted -L ...@%d,#head' % p4id):
            c = int(d['change'])
            if c != p4id:
                changes.append(c)
        changes.sort()

        # we create a temporary converter sink here to get the author mapping
        sink = mercurial_sink(ui, repo.root)
        cvt = converter(ui, None, sink, sink.revmapfile(), {})
        authorfile = sink.authorfile()
        if authorfile and os.path.exists(authorfile):
            cvt.readauthormap(authorfile)
        client.authors = cvt.authors

        return False, (client, p4rev, p4id, changes)


    @staticmethod
    def pushcommon(out, original, ui, repo, dest, **opts):
        'Shared code for push and outgoing'

        dest, revs, co = hg.parseurl(ui.expandpath(dest or 'default-push',
                                                   dest or 'default'), opts.get('rev'))
        try:
            client = p4client(ui, repo, dest)
        except:
            return True, original(ui, repo, dest, **opts)

        p4rev, p4id = client.latest()
        ctx1 = repo[p4rev]
        rev = opts.get('rev')

        if rev:
            n1, n2 = cmdutil.revpair(repo, rev)
            if n2:
                ctx1 = repo[n1]
                ctx2 = repo[n2]
            else:
                ctx2 = repo[n1]
                ctx1 = ctx2.parents()[0]
        else:
            ctx2 = repo['tip']
        
        nodes = repo.changelog.nodesbetween([ctx1.node()], [ctx2.node()])[0][1:]

        # trim off nodes at either end that have already been pushed
        for end in [0, -1]:
            while nodes:
                n = repo[nodes[end]]
                pending = client.getpending(n.hex())
                if (out and pending > 0) or pending == client.SUBMITTED:
                    del nodes[end]
                else:
                    break

        # check that remaining nodes have not already been pushed
        for n in nodes:
            n = repo[n]
            fail = False
            pending = client.getpending(n.hex())
            if (out and pending > 0) or pending == client.SUBMITTED:
                fail = True
            for ctx3 in n.children():
                extra = ctx3.extra()
                if 'p4' in extra:
                    fail = True
                    break
            if fail:
                raise util.Abort(_('can not push, changeset %s is already in p4' % n))

        # find changed files
        if not nodes:
            mod = add = rem = None
        else:
            mod, add, rem = repo.status(node1=ctx1.node(), node2=ctx2.node())[:3]
        
        if not (mod or add or rem):
            ui.status(_('no changes found\n'))
            return True, 0

        # create description
        desc = []
        for n in nodes:
            desc.append(repo[n].description())

        if len(nodes) > 1:
            h = [repo[nodes[0]].hex()]
        else:
            h = []
        h.append(repo[nodes[-1]].hex())

        desc='\n* * *\n'.join(desc) + '\n\n{{mercurial %s}}\n' % (':'.join(h))

        return False, (client, p4rev, p4id, nodes, ctx2, desc, mod, add, rem)


    def parsenodes(self, desc):
        'find revisions in p4 changelist description'
        m = self.re_hgid.search(desc)
        nodes = None
        if m:
            try:
                nodes = self.repo.changelog.nodesbetween(
                    [self.repo[m.group(2)].node()], [self.repo[m.group(4) or m.group(2)].node()])[0]
            except:
                ui.note(_('ignoring hg revision range %s from p4\n' % m.group(1)))
        return nodes


    def submit(self, nodes, change, files):
        '''submit one changelist to p4, mark nodes in p4stat and optionally 
        delete the files added or modified in the p4 workarea'''

        cl = None
        for d in self.run('submit -c %s' % change):
            if d['code'] == 'error':
                raise util.Abort(_('Error submitting p4 change %s: %s') % (change, d['data']))
            cl = d.get('submittedChange', cl)

        for n in nodes:
            self.setpending(self.repo[n].hex(), self.SUBMITTED)

        self.ui.note(_('submitted changelist %s\n') % cl)

        if files and not self.keep:
            # delete the files in the p4 client directory
            for f in files:
                out = os.path.join(self.root, f)
                try:
                    mode = os.stat(out)[0]
                    mode |= (mode & 0444) >> 1
                    self.ui.note(_('deleting: %s\n') % out)
                    os.chmod(out, mode)
                    os.unlink(out)
                except:
                    pass


# --------------------------------------------------------------------------

def incoming(original, ui, repo, source='default', **opts):
    '''show changes that would be pulled from the p4 source repository'''

    done, r = p4client.pullcommon(original, ui, repo, source, **opts)
    if done:
        return r

    client, p4rev, p4id, changes = r
    for c in changes:
        desc, user, date, files = client.describe(c, files=ui.verbose)

        ui.write(_('changelist:  %d\n') % c)
        # ui.write(_('branch:      %s\n') % branch)
        # ui.write(_('tag:         %s\n') % tag)
        # ui.write(_('parent:      %d:%s\n') % parent)
        ui.write(_('user:        %s\n') % user)
        ui.write(_('date:        %s\n') % util.datestr(date))
        if ui.verbose:
            ui.write(_('files:       %s\n') % ' '.join(f[1] for f in files))

        if desc:
            if ui.verbose:
                ui.write(_('description:\n'))
                ui.write(desc)
                ui.write('\n')
            else:
                ui.write(_('summary:     %s\n') % desc.splitlines()[0])

        ui.write('\n')
    client.close()


def pull(original, ui, repo, source=None, **opts):
    '''Wrap the pull command to look for p4 paths, import changelists'''

    done, r = p4client.pullcommon(original, ui, repo, source, **opts)
    if done:
        return r

    client, p4rev, p4id, changes = r
    revcache = {}
    c = 0

    def getfilectx(repo, memctx, fn):
        'callback to read file data'
        mode, contents = client.getfile(revcache[fn], c)
        return context.memfilectx(fn, contents, 'l' in mode, 'x' in mode, None)

    for c in changes:
        desc, user, date, files = client.describe(c, files=True)

        revcache = dict((f[1],f) for f in files)

        nodes = client.parsenodes(desc)
        if nodes:
            parent = nodes[-1]
        else:
            parent = None

        ctx = context.memctx(repo, (p4rev, parent), desc, 
                             [f[1] for f in files], getfilectx,
                             user, date, {'p4':c})

        if nodes:
            for n in nodes:
                client.setpending(repo[n].hex(), None)

        p4rev = repo.commitctx(ctx)
        ctx = repo[p4rev]
        ui.note(_('added changeset %d:%s\n') % (ctx.rev(), ctx))

    client.close()


# --------------------------------------------------------------------------

def outgoing(original, ui, repo, dest=None, **opts):
    '''Wrap the outgoing command to look for p4 paths, report changes'''
    done, r = p4client.pushcommon(True, original, ui, repo, dest, **opts)
    if done:
        return r
    client, p4rev, p4id, nodes, ctx2, desc, mod, add, rem = r

    ui.write(desc)
    ui.write('\naffected files:\n')
    cwd = repo.getcwd()
    for char, files in zip('MAR', (mod, add, rem)):
        for f in files:
            ui.write('%s %s\n' % (char, repo.pathto(f, cwd)))
    ui.write('\n')
    client.close()


def push(original, ui, repo, dest=None, **opts):
    '''Wrap the push command to look for p4 paths, create p4 changelist'''

    done, r = p4client.pushcommon(False, original, ui, repo, dest, **opts)
    if done:
        return r
    client, p4rev, p4id, nodes, ctx2, desc, mod, add, rem = r

    # sync to the last revision pulled/converted
    if client.keep:
        k = ''
    else:
        k = '-k'
    client.runs('sync %s @%d' % (k, p4id), abort=False)

    # attempt to reuse an existing changelist
    use = ''
    for d in client.run('changes -s pending -L'):
        if d['desc'] == desc:
            use = d['change']

    # get changelist data, and update it
    changelist = client.runs('change -o %s' % use)
    changelist['Description'] = desc

    fn = None
    try:
        # write changelist data to a temporary file
        fd, fn = tempfile.mkstemp(prefix='hg-p4-')
        fp = os.fdopen(fd, 'wb')
        marshal.dump(changelist, fp)
        fp.close()

        # update p4 changelist
        d = client.runs('change -i <"%s"' % fn)
        data = d['data']
        if d['code'] == 'info':
            ui.status('p4: %s\n' % data)
            if not use:
                m = client.re_number.match(data)
                if m:
                    use = m.group(1)
        else:
            raise util.Abort(_('Error creating p4 change: %s') % data)

    finally:
        try:
            if fn: os.unlink(fn)
        except: 
            pass

    if not use:
        raise util.Abort(_('Did not get changelist number from p4'))

    # revert any other changes to the files
    ui.note(_('reverting: %s\n') % ', '.join(mod+add+rem))
    client.runs('revert %s' % (' '.join('"%s"'%f for f in mod + add + rem)), abort=False)

    # now add/edit/delete the files
    if mod:
        ui.note(_('opening for edit: %s\n') % ' '.join(mod))
        client.runs('edit -c %s %s' % (use, ' '.join('"%s"'%f for f in mod)))

    if mod or add:
        ui.note(_('Retrieving file contents...\n'))
        m = cmdutil.match(repo, mod+add, opts={})
        for abs in ctx2.walk(m):
            out = os.path.join(client.root, abs)
            if ui.debugflag: ui.debug(_('writing: %s\n') % out)
            util.makedirs(os.path.dirname(out))
            fp = cmdutil.make_file(repo, out, ctx2.node(), pathname=abs)
            data = ctx2[abs].data()
            fp.write(data)
            fp.close()

    if add:
        ui.note(_('opening for add: %s\n') % ' '.join(add))
        client.runs('add -c %s %s' % (use, ' '.join('"%s"'%f for f in add)))

    if rem:
        ui.note(_('opening for delete: %s\n') % ' '.join(rem))
        client.runs('delete -c %s %s' % (use, ' '.join('"%s"'%f for f in rem)))

    # submit the changelist to perforce if --submit was given
    if opts['submit'] or ui.configbool('perfarce', 'submit', default=False):
        client.submit(nodes, use, mod + add)
    else:
        for n in nodes:
            client.setpending(repo[n].hex(), int(use))
        ui.note(_('pending changelist %s\n') % use)

    client.close()


# --------------------------------------------------------------------------

def submit(ui, repo, change=None, dest=None, **opts):
    '''do a p4 submit and update the repository state'''

    dest, revs, co = hg.parseurl(ui.expandpath(dest or 'default-push',
                                               dest or 'default'))
    
    client = p4client(ui, repo, dest)
    if change:
        change = int(change)
    else:
        changes = {}
        pending = client.getpendingdict()
        for i in pending:
            i = pending[i]
            if isinstance(i,int):
                changes[i] = True
        changes = changes.keys()
        if len(changes) == 0:
            raise util.Abort(_('no pending changelists to submit'))
        elif len(changes) > 1:
            changes.sort()
            raise util.Abort(_('more than one changelist to submit: %s') % ' '.join(str(i) for i in changes))
        change = changes[0]

    desc, user, date, files = client.describe(change, files=True)
    nodes = client.parsenodes(desc)

    client.submit(nodes, change, files)
    client.close()


def pending(ui, repo, dest=None, **opts):
    'report changelists already pushed and pending for submit in p4'

    dest, revs, co = hg.parseurl(ui.expandpath(dest or 'default-push',
                                               dest or 'default'))
    
    client = p4client(ui, repo, dest)

    changes = {}
    pending = client.getpendingdict()
    for i in pending:
        j = pending[i]
        if isinstance(j,int):
            if j in changes:
                changes[j].append(i)
            else:
                changes[j] = [i]
    keys = changes.keys()
    keys.sort()

    for i in keys:
        ui.write('%d %s\n' % (i, ' '.join(changes[i])))

    client.close()


def identify(ui, repo, *args, **opts):
    '''show p4 and hg revisions

    With no revision, print a summary of the most recent revision
    in the repository that was converted from p4.
    Otherwise, find the p4 changelist for the revision given.
    '''

    rev = opts.get('rev')
    if rev:
        ctx = repo[rev]
        extra = ctx.extra()
        if 'p4' not in extra:
            raise util.Abort(_('no p4 changelist revision found'))
        changelist = int(extra['p4'])
    else:
        client = p4client(ui, repo, 'p4:///')
        p4rev, changelist = client.latest()
        ctx = repo[p4rev]

    num = opts.get('num')
    doid = opts.get('id')
    dop4 = opts.get('p4')
    default = not (num or doid or dop4)
    output = []

    if default or dop4:
        output.append(str(changelist))
    if num:
        output.append(str(ctx.rev()))
    if default or doid:
        output.append(str(ctx))

    ui.write("%s\n" % ' '.join(output))
    

cmdtable = {
    # 'command-name': (function-call, options-list, help-string)
    'p4submit': 
        (   submit,
            [ ],
            'hg p4submit changelist [p4://server/client]'),
    'p4pending': 
        (   pending,
            [ ],
            'hg p4pending [p4://server/client]'),
    'p4identify': 
        (   identify,
            [ ('r', 'rev', '',   _('identify the specified revision')),
              ('n', 'num', None, _('show local revision number')),
              ('i', 'id',  None, _('show global revision id')),
              ('p', 'p4',  None, _('show p4 revision number')),
            ],
            'hg p4identify [-inp] [-r REV]'
        )
}
