# Public serving-assessment evidence

See the [assessment](../../2026-11-13-serving-validation.md) for identities, counts,
timing boundaries, costs, cleanup and applicability limits. Original provider
receipts and operator configuration remain outside Git. Their sealed hashes bind
this public export; the export itself is not a provider signature or attestation.

`native-units.json` contains all 148 native requests (one preflight plus 147 solve
submissions), each successful output and its consumer CPU decisions. Opaque unit
labels normalize the provider inventory. The three public problem payloads are
deduplicated in `problems.json`: replace the single `{{problem:HASH}}` token in
`requestUtf8Template` with that dictionary entry to recover the exact original
request bytes and SHA-256. `responseUtf8` retains the exact successful response
bytes. Cancellations have no completed response and receive no completion credit.
The input objects contain only public synthetic work; no seed, wallet or funded
output is supplied to a worker.

`consumer-audit.json` retains packet derivation and startup model/driver observations.
`independent-cpu.json` retains upstream/backend identity and every emitted candidate's
independent verdict. `offline-consensus.json` distinguishes native and checker
source identities, and contains the one positive and twelve negative Core results.
The matching `.stdin` files are exact interpreter inputs; the `.hex` file is the
unfunded public transaction. `checker-followup.json` explains the retained original
checker failure and corrected assessment without relabeling native evidence.
`cost-and-cleanup.json` reports estimates, independent reconciliation and deliberately
retained resources; provider billing was not queried.

Verify the complete public package and rehydrated payloads from this directory:

```sh
python3 - <<'PY'
import hashlib, json, pathlib
p = pathlib.Path('.')
sha = lambda b: hashlib.sha256(b).hexdigest()
m = json.loads((p / 'manifest.json').read_text())
for name, expected in m['files'].items():
    assert sha((p / name).read_bytes()) == expected, name
problems = json.loads((p / 'problems.json').read_text())
units = json.loads((p / 'native-units.json').read_text())
assert len(units) == 148
for u in units:
    token = '{{problem:' + u['problemRef'] + '}}'
    assert u['requestUtf8Template'].count(token) == 1
    raw = u['requestUtf8Template'].replace(token, problems[u['problemRef']])
    assert sha(raw.encode()) == u['requestSha256']
    if 'responseUtf8' in u:
        assert sha(u['responseUtf8'].encode()) == u['responseSha256']
        assert json.loads(u['responseUtf8'])['inputSha256'] == u['requestSha256']
assert sum('responseUtf8' in u for u in units) == 109
assert sum(u.get('coordinatorCancellation', False) for u in units) == 39
print('All public files and 148 request / 109 response identities verified')
PY
```

No cloud execution or paid work is needed to inspect or check this package.
