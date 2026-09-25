# Source and redistribution notices

- Historical candidate import: Layr-Labs/quantum-safe-bitcoin-challenge commit `2791ed0588f5014ccd688d48ba5502df2879f2f1`. The upstream top-level license is preserved at `vendor/challenge/LICENSE`; per-component COPYING notices, including GPLv3 notices, remain under candidates. Do not infer a single license for every component from the top-level file.
- Modified optimized subset: repaired `1650caf53a32b0ea16aae9e490ebbf5a8686d632` lineage, imported from qsb-app commit `aa163de` with its existing source lock, top-level Apache-2.0 LICENSE and embedded notices. Its `GPUMath.h` and `GPUHash.h` retain Jean Luc PONS copyright and GNU GPL notices; the top-level Apache file does not replace those notices. The verbatim GPLv3 text preserved at `vendor/challenge/candidates/subset/COPYING` is also packaged with the optimized image, without changing the locked solver source. Local adaptations include tail SHA caching, exact exceptional recovery, checked CUDA/OpenSSL handling and output publication. See its README and source files.
- Python worker/adaptation/build files were moved from qsb-app with existing notices. No new blanket license supersedes upstream terms.
- CUDA base images and Runpod SDK retain their own terms. Source is distributed alongside the image by the tagged repository; corresponding adapted historical source and notices are also included inside the image under `/opt/qsb/source` and `/opt/qsb/licenses`.

Redistribution approval was explicitly confirmed by the user on 2026-09-25. This repository does not represent that statement as independent legal analysis, an upstream endorsement, or production certification.

## Image notice locations

The historical image preserves the adapted candidate include trees and their
`COPYING` files under `/opt/qsb/source/{pinning,subset}`. Apache and both original
GPLv3 texts, plus this notice, are copied explicitly to `/opt/qsb/licenses`.
The adaptation script and Dockerfile are included under `/opt/qsb/source/build`.

The experimental optimized image retains its source and embedded notices under
`/opt/qsb-validation/candidate/source`, and packages its Apache LICENSE, the
preserved subset GPLv3 text and this notice under `/opt/qsb-validation/licenses`.
Its build script, Dockerfile and source lock are under
`/opt/qsb-validation/source-build`. The queue stage inherits these files.

CI compares the historical image's license and selected copyright-notice files
byte for byte with repository inputs. The same offline check can run against an
optimized image using `python3 tests/test_license_packaging.py --image IMAGE
--profile optimized`. These are packaging checks, not a legal opinion or an
assertion that every redistribution obligation has been independently reviewed.
