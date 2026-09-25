"""Atomic proof progression in the existing cost ledger; no provider/solver calls.

The caller must invoke the pinned evidence verifier and validate host provenance.
A JSON receipt is not itself GPU attestation. No CLI or automatic launch path.
"""
import hashlib
import json
from budget import canonical, identity


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


class Journal:
    def __init__(self, budget):
        self.budget = budget

    def initialize(self, fixture_hash, manifest_hash, request_id):
        identity(request_id)
        if json.loads(self.budget.campaign)['campaignId'] != request_id:
            raise ValueError('wrong campaign')
        for value in (fixture_hash, manifest_hash):
            if not isinstance(value, str) or len(value) != 64 or any(c not in '0123456789abcdef' for c in value):
                raise ValueError('frozen public hashes required')
        with self.budget.transaction() as db:
            if db.execute('SELECT 1 FROM intents').fetchone():
                raise ValueError('initialize proof before any budget reservations')
            # Deliberately no IF NOT EXISTS: initialization is never reset/resume.
            db.execute('CREATE TABLE proof_state(singleton INTEGER PRIMARY KEY CHECK(singleton=1), binding TEXT NOT NULL, stage TEXT NOT NULL, next_attempt INTEGER NOT NULL, solutions TEXT NOT NULL)')
            db.execute('CREATE TABLE proof_sessions(token TEXT PRIMARY KEY, batch_id TEXT UNIQUE NOT NULL, batch TEXT NOT NULL, state TEXT NOT NULL, command_id TEXT, receipt TEXT)')
            db.execute('CREATE TABLE proof_coverage(stage TEXT NOT NULL, context TEXT NOT NULL, attempt INTEGER NOT NULL, work_range TEXT NOT NULL, token TEXT NOT NULL, PRIMARY KEY(stage,context,attempt))')
            db.execute('INSERT INTO proof_state VALUES(1,?,\'pinning\',0,\'{}\')',
                       (canonical(dict(fixtureSha256=fixture_hash,manifestHash=manifest_hash,requestId=request_id)),))

    def register(self, token, batch_raw, validate_batch):
        identity(token)
        batch = json.loads(batch_raw)
        request = validate_batch(batch)
        with self.budget.transaction() as db:
            row = db.execute('SELECT state FROM intents WHERE id=?',(token,)).fetchone()
            if row != ('reserved',) or db.execute('SELECT 1 FROM operations WHERE intent=? AND mode=\'launch\'',(token,)).fetchone():
                raise ValueError('register before launch against reserved budget')
            if db.execute("SELECT 1 FROM proof_sessions WHERE state!='published'").fetchone():
                raise ValueError('unresolved proof session')
            binding, stage, attempt, solutions = db.execute('SELECT binding,stage,next_attempt,solutions FROM proof_state').fetchone()
            binding=json.loads(binding);solutions=json.loads(solutions)
            if stage not in ('pinning','round1','round2') or request.get('stage')!=stage or request.get('attempt')!=attempt:
                raise ValueError('wrong stage or next range')
            if request.get('manifestHash')!=binding['manifestHash']:
                raise ValueError('wrong manifest')
            if stage!='pinning' and any(request.get(k)!=solutions['pinning'][k] for k in ('sequence','locktime')):
                raise ValueError('wrong verified pin context')
            db.execute('INSERT INTO proof_sessions VALUES(?,?,?,\'registered\',NULL,NULL)',
                       (token,batch['batchId'],batch_raw.decode()))

    def close_capacity_rejection(self, token):
        """Only independently reconciled explicit rejections can release a batch."""
        with self.budget.transaction() as db:
            resource=db.execute('SELECT state,resource,evidence FROM intents WHERE id=?',(token,)).fetchone()
            session=db.execute('SELECT state FROM proof_sessions WHERE token=?',(token,)).fetchone()
            if not resource or resource[0]!='settled' or resource[1] is not None or session!=('registered',):
                raise ValueError('only reconciled unallocated rejection can close')
            evidence=json.loads(resource[2] or '{}')
            if evidence.get('rejection',{}).get('code')!='InsufficientInstanceCapacity' or evidence['rejection'].get('clientToken')!=token:
                raise ValueError('explicit capacity rejection required')
            db.execute("UPDATE proof_sessions SET state='published',receipt=? WHERE token=?",(canonical(evidence),token))

    def claim_command(self, token):
        """Commit before exactly one host send-command; an unknown send blocks."""
        with self.budget.transaction() as db:
            if db.execute('SELECT state FROM intents WHERE id=?',(token,)).fetchone()!=('attached',):
                raise ValueError('allocated resource required')
            changed=db.execute("UPDATE proof_sessions SET state='command-intent' WHERE token=? AND state='registered'",(token,)).rowcount
            if changed!=1:raise ValueError('command already attempted or missing session')

    def attach_command(self, token, command_id):
        identity(command_id)
        with self.budget.transaction() as db:
            changed=db.execute("UPDATE proof_sessions SET command_id=?,state='command-attached' WHERE token=? AND state='command-intent' AND command_id IS NULL",(command_id,token)).rowcount
            if changed!=1:raise ValueError('unknown or already attached command')

    def publish(self, token, command_id, verify_evidence, work_range):
        """Verifier callback re-reads frozen collection/fixture and checks provenance.

        Runs under the owner transaction so stage/command cannot change during
        verification. Never pass an unvalidated user/provider verdict callback.
        """
        with self.budget.transaction() as db:
            session=db.execute('SELECT batch,state,command_id FROM proof_sessions WHERE token=?',(token,)).fetchone()
            if not session or session[1:]!=('command-attached',command_id):
                raise ValueError('unresolved or already published command')
            resource=db.execute('SELECT state,resource,evidence FROM intents WHERE id=?',(token,)).fetchone()
            if not resource or resource[0]!='settled' or resource[1] is None:
                raise ValueError('allocated session must be independently cleaned and settled')
            batch=json.loads(session[0]);request=batch['request']
            binding,stage,next_attempt,solutions=db.execute('SELECT binding,stage,next_attempt,solutions FROM proof_state').fetchone()
            binding=json.loads(binding);solutions=json.loads(solutions)
            if request['stage']!=stage or request['attempt']!=next_attempt:raise ValueError('stale publication')
            verdict=verify_evidence(session[0].encode(),json.loads(resource[1]),command_id)
            if any(verdict.get(k)!=v for k,v in binding.items()) or verdict.get('batchId')!=batch['batchId'] or verdict.get('stage')!=stage or verdict.get('parameterSha256')!=request['parameterSha256']:
                raise ValueError('unbound CPU evidence')
            if verdict.get('grantsRangeCredit') is not False:raise ValueError('invalid verification authority')
            rows=verdict['rows']
            if not isinstance(rows,list) or len(rows)>batch['maxAttempts']:raise ValueError('invalid row count')
            context=digest(canonical(dict(stage=stage,parameterSha256=request['parameterSha256'],manifestHash=binding['manifestHash'])).encode())
            hit=None
            for offset,row in enumerate(rows):
                attempt=next_attempt+offset
                if row.get('attempt')!=attempt or row.get('workRange')!=work_range(stage,attempt):raise ValueError('noncontiguous coverage')
                eligible=row.get('wholeRangeEligible')
                if eligible is True and row.get('cpuVerdict') is None:
                    db.execute('INSERT INTO proof_coverage VALUES(?,?,?,?,?)',(stage,context,attempt,canonical(row['workRange']),token))
                elif eligible is False and offset==len(rows)-1 and isinstance(row.get('cpuVerdict'),dict):
                    hit=row['cpuVerdict']
                else:raise ValueError('inconsistent candidate coverage')
            solution=verdict.get('verifiedSolution')
            if solution is not None:
                if hit!=solution or hit.get('valid') is not True:raise ValueError('unbound solution')
                if stage=='pinning':
                    if type(hit.get('sequence')) is not int or not 0x80000000<=hit['sequence']<=0xffffffff or type(hit.get('locktime')) is not int or not 500000000<=hit['locktime']<1744600000:raise ValueError('invalid pin solution')
                else:
                    indices=hit.get('indices')
                    if not isinstance(indices,list) or len(indices)!=9 or any(type(i) is not int or not 0<=i<150 for i in indices) or indices!=sorted(set(indices)):raise ValueError('invalid subset solution')
                solutions[stage]=solution
                stage={'pinning':'round1','round1':'round2','round2':'solved'}[stage];next_attempt=0
            elif hit is not None:
                # DER-only or otherwise incomplete hit is never silently skipped.
                raise ValueError('candidate requires explicit reconciliation')
            else:
                next_attempt+=len(rows)
            db.execute('UPDATE proof_state SET stage=?,next_attempt=?,solutions=? WHERE singleton=1',(stage,next_attempt,canonical(solutions)))
            db.execute("UPDATE proof_sessions SET state='published',receipt=? WHERE token=?",(canonical(verdict),token))
            return dict(stage=stage,nextAttempt=next_attempt,coverageAdded=sum(row['wholeRangeEligible'] is True for row in rows))

    def snapshot(self):
        with self.budget.transaction() as db:
            binding,stage,attempt,solutions=db.execute('SELECT binding,stage,next_attempt,solutions FROM proof_state').fetchone()
            return dict(binding=json.loads(binding),stage=stage,nextAttempt=attempt,solutions=json.loads(solutions),
                        completedRanges=db.execute('SELECT COUNT(*) FROM proof_coverage').fetchone()[0])
