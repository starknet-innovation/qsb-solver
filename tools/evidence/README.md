# Offline source comparison

`compare_sources.py` compares saved complete recursive Git tree responses and
rehashes a local import against its SHA-256 lock. It makes no network requests,
executes no imported code, and does not allocate hardware.

```
python3 tools/evidence/compare_sources.py \
  --before BASE_TREE.json --after UPSTREAM_TREE.json \
  --lock vendor/challenge/provenance.json --root vendor/challenge
```

For the adapted subset, use `worker/optimized/source-lock.json`, root
`research/optimized-subset`, and `--prefix candidates`.

Both snapshots must explicitly report `truncated: false`. The tool includes
additions, removals and file-mode changes; it never uses GitHub's capped commit
comparison file list. Snapshot retrieval and commit-to-tree authentication remain
the caller's responsibility. Byte equality is reported separately from lock
validity. A nonzero exit indicates invalid input or a missing/changed locked file;
differences from upstream are expected for intentional adaptations.

This is source-identity evidence only. It does not establish compatible behavior,
complete range coverage, executed binary identity, physical hardware, performance
or permission to publish an image. Additional files outside a lock are not
audited by the lock comparison; inspect actual build inputs separately.

Tests: `python3 -m unittest discover -s tests -p test_source_evidence.py -v`.
