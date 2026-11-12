"""Require a clean controller at its configured upstream's live branch tip."""
import subprocess


def pushed_commit(root):
    def git(*args):
        return subprocess.check_output(['git', *args], cwd=root, text=True).strip()
    if git('status', '--porcelain'):
        raise ValueError('Dirty controller source')
    commit = git('rev-parse', 'HEAD')
    branch = git('symbolic-ref', '--quiet', '--short', 'HEAD')
    remote = git('config', '--get', 'branch.' + branch + '.remote')
    ref = git('config', '--get', 'branch.' + branch + '.merge')
    if not remote or remote == '.' or not ref.startswith('refs/heads/'):
        raise ValueError('Controller needs a configured remote branch')
    # A local refs/remotes/* value is not proof of what the remote currently has.
    rows = git('ls-remote', '--exit-code', '--heads', '--', remote, ref).splitlines()
    if rows != [commit + '\t' + ref]:
        raise ValueError('Controller HEAD is not the live pushed branch tip')
    return commit
