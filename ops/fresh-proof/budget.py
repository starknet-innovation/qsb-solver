"""Durable admission accounting; no provider calls or automatic refunds.

Money is integer USD microdollars. A reservation is retained across crashes and
unknown outcomes. Completion consumes its full allowance, conservatively avoiding
refunds based on incomplete provider billing. This is not an AWS invoice cap.
"""
from contextlib import contextmanager
import hashlib
import json
from pathlib import Path
import sqlite3
import uuid

MAXIMUM = 200_000_000
HEADROOM = 20_000_000


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False)


def positive(value):
    if type(value) is not int or value <= 0:
        raise ValueError('positive integer microdollars required')
    return value


def identity(value):
    if not isinstance(value, str) or str(uuid.UUID(value)) != value:
        raise ValueError('canonical UUID required')
    return value


class Budget:
    def __init__(self, path, campaign):
        if Path(path).is_symlink():
            raise ValueError('ledger symlink forbidden')
        self.path = Path(path).resolve(strict=True)
        self.campaign = canonical(campaign)
        stat = self.path.stat()
        self.file_identity = (stat.st_dev, stat.st_ino)
        with self.transaction() as db:
            row = db.execute('SELECT binding, maximum, headroom FROM campaign').fetchall()
            if row != [(self.campaign, MAXIMUM, HEADROOM)]:
                raise ValueError('budget authorization or campaign mismatch')

    @classmethod
    def create(cls, path, campaign):
        path = Path(path)
        if not isinstance(campaign, dict) or set(campaign) != {'campaignId', 'requestHash', 'candidateSource', 'imageDigest'}:
            raise ValueError('exact public campaign binding required')
        identity(campaign['campaignId'])
        for key, length in [('requestHash', 64), ('candidateSource', 40), ('imageDigest', 64)]:
            value = campaign[key]
            if not isinstance(value, str) or len(value) != length or any(c not in '0123456789abcdef' for c in value):
                raise ValueError('invalid campaign binding')
        # Never initialize over a previous ledger, even an incomplete one.
        with path.open('xb'):
            pass
        path.chmod(0o600)
        db = sqlite3.connect(path)
        try:
            db.execute('PRAGMA synchronous=FULL')
            db.executescript('''
              CREATE TABLE campaign(binding TEXT NOT NULL, maximum INTEGER NOT NULL, headroom INTEGER NOT NULL);
              CREATE TABLE intents(id TEXT PRIMARY KEY, request TEXT NOT NULL, amount INTEGER NOT NULL CHECK(amount>0),
                state TEXT NOT NULL CHECK(state IN ('reserved','attached','settled')),
                resource TEXT, evidence TEXT);
              CREATE UNIQUE INDEX one_unsettled ON intents((1)) WHERE state != 'settled';
            ''')
            db.execute('INSERT INTO campaign VALUES(?,?,?)', (canonical(campaign), MAXIMUM, HEADROOM))
            db.commit()
        finally:
            db.close()
        return cls(path, campaign)

    def check_file(self):
        stat = self.path.lstat()
        if self.path.is_symlink() or (stat.st_dev, stat.st_ino) != self.file_identity:
            raise ValueError('ledger file replaced; stop and reconcile')

    @contextmanager
    def transaction(self):
        # mode=rw prevents a typo from silently creating a replacement ledger.
        self.check_file()
        db = sqlite3.connect(self.path.as_uri() + '?mode=rw', uri=True, timeout=15)
        try:
            db.execute('PRAGMA synchronous=FULL')
            db.execute('BEGIN IMMEDIATE')
            self.check_file()
            if db.execute('SELECT binding, maximum, headroom FROM campaign').fetchall() != [(self.campaign, MAXIMUM, HEADROOM)]:
                raise ValueError('budget authorization or campaign changed')
            yield db
            self.check_file()
            db.commit()
        except BaseException:
            db.rollback()
            raise
        finally:
            db.close()

    def reserve(self, intent, public_request, allowance):
        identity(intent)
        positive(allowance)
        frozen = canonical(public_request)
        with self.transaction() as db:
            if db.execute('SELECT 1 FROM intents WHERE id=?', (intent,)).fetchone():
                raise ValueError('intent exists; reconcile instead of resubmitting')
            if db.execute("SELECT 1 FROM intents WHERE state!='settled'").fetchone():
                raise ValueError('unsettled intent blocks replacement')
            used = db.execute('SELECT COALESCE(SUM(amount),0) FROM intents').fetchone()[0]
            if used + allowance + HEADROOM > MAXIMUM:
                raise ValueError('budget admission limit exceeded')
            db.execute('INSERT INTO intents VALUES(?,?,?,\'reserved\',NULL,NULL)', (intent, frozen, allowance))
        # Return only after the transaction commits; caller may now prepare paid
        # infrastructure exactly once. Exceptions never refund or erase intent.
        return dict(intent=intent, requestSha256=hashlib.sha256(frozen.encode()).hexdigest(), allowanceMicroUsd=allowance)

    def attach(self, intent, public_request, resource):
        if not isinstance(resource, dict) or set(resource) != {'instanceId', 'volumeIds', 'clientToken'}:
            raise ValueError('exact resource binding required')
        if resource['clientToken'] != intent or not isinstance(resource['instanceId'], str) or not resource['instanceId'].startswith('i-'):
            raise ValueError('resource identity mismatch')
        if not isinstance(resource['volumeIds'], list) or not resource['volumeIds'] or any(not isinstance(v, str) or not v.startswith('vol-') for v in resource['volumeIds']):
            raise ValueError('root volumes required')
        with self.transaction() as db:
            row = db.execute('SELECT request,state FROM intents WHERE id=?', (intent,)).fetchone()
            if row != (canonical(public_request), 'reserved'):
                raise ValueError('request mismatch or resource already attached')
            db.execute("UPDATE intents SET state='attached',resource=? WHERE id=?", (canonical(resource), intent))

    def settle(self, intent, evidence):
        # Caller must independently gather this provider evidence. No absence-only
        # or elapsed-time settlement for an unknown launch is supported.
        with self.transaction() as db:
            row = db.execute('SELECT state,resource FROM intents WHERE id=?', (intent,)).fetchone()
            if not row or row[0] != 'attached':
                raise ValueError('only an attached resource can settle')
            resource = json.loads(row[1])
            required = {'instanceId','instanceState','volumeIds','volumesRemaining','securityGroupsRemaining','schedulesRemaining','functionsRemaining','rolesRemaining','instanceProfilesRemaining','receiptSha256'}
            if not isinstance(evidence, dict) or set(evidence) != required:
                raise ValueError('complete cleanup evidence required')
            if evidence['instanceId'] != resource['instanceId'] or evidence['instanceState'] != 'terminated' or evidence['volumeIds'] != resource['volumeIds']:
                raise ValueError('cleanup resource mismatch')
            if any(type(evidence[k]) is not int or evidence[k] != 0 for k in required if k.endswith('Remaining')):
                raise ValueError('cleanup not confirmed')
            digest = evidence['receiptSha256']
            if not isinstance(digest, str) or len(digest) != 64 or any(c not in '0123456789abcdef' for c in digest):
                raise ValueError('cleanup receipt digest required')
            db.execute("UPDATE intents SET state='settled',evidence=? WHERE id=?", (canonical(evidence), intent))
            # Entire allowance remains charged. No optimistic estimate refunds.

    def snapshot(self):
        with self.transaction() as db:
            rows = db.execute('SELECT id,amount,state FROM intents ORDER BY rowid').fetchall()
        used = sum(r[1] for r in rows)
        return dict(maximumMicroUsd=MAXIMUM, headroomMicroUsd=HEADROOM,
                    committedMicroUsd=used, availableMicroUsd=MAXIMUM-HEADROOM-used,
                    unresolved=[r[0] for r in rows if r[2] != 'settled'])
