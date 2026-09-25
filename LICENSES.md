# Source and redistribution notices

- Historical candidate import: Layr-Labs/quantum-safe-bitcoin-challenge commit `2791ed0588f5014ccd688d48ba5502df2879f2f1`. The upstream top-level license is preserved at `vendor/challenge/LICENSE`; per-component COPYING notices, including GPLv3 notices, remain under candidates. Do not infer a single license for every component from the top-level file.
- Modified optimized subset: repaired `1650caf53a32b0ea16aae9e490ebbf5a8686d632` lineage, imported from qsb-app commit `aa163de` with its existing source lock, Apache-2.0 LICENSE and embedded notices. Local adaptations include tail SHA caching, exact exceptional recovery, checked CUDA/OpenSSL handling and output publication. See its README and source files.
- Python worker/adaptation/build files were moved from qsb-app with existing notices. No new blanket license supersedes upstream terms.
- CUDA base images and Runpod SDK retain their own terms. Source is distributed alongside the image by the tagged repository; corresponding adapted historical source and notices are also included inside the image under `/opt/qsb/source` and `/opt/qsb/licenses`.

Redistribution approval was explicitly confirmed by the user on 2026-09-25. This repository does not represent that statement as independent legal analysis, an upstream endorsement, or production certification.
