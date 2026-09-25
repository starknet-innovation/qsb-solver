# Fresh sm86 offline funding fixture

Status: HOLD. A new fixture exists; **the optimized search and withdrawal proof
have not run**. This does not establish a solved transaction or miner inclusion.

Request `ea06c087-b04c-496a-9325-0c801cda08ae` was funded by unmodified Core30.2
inside Docker with network disabled, a read-only root and dropped capabilities.
Core executables matched the locally cached release archive byte-for-byte.
The fresh local regtest transaction is
`d1e3cf78a6476f65cf2796dea58f1e69d45837002f4ab077782c8da2a703d481`.
A separate owned offline Core process confirmed the 100,000-satoshi QSB output
and10,000-satoshi helper output both unspent with one confirmation. Frozen
withdrawal output is90,000satoshis and fee20,000satoshis, all regtest only.

The first read-only postcheck completed its output checks but mishandled Core's
plain-text stop response. Its parser was corrected and only the read-only
postcheck repeated; funding was not repeated. Both containers were removed.

Pinning parameters were independently exported from six frozen public CPU files
matching app commit848751c082c2b70dfd11c7542525bbd2162819dd. The JSON receipt
binds the reference, public manifest, request and parameter hashes. No historical
pin or coverage was imported. Subset parameters await the new verified pin.

The local campaign ledger was initialized once with USD200 maximum admission,
USD20 contingency, USD0 committed and no unresolved intents. It is conservative
admission accounting, not an AWS-enforced invoice limit. No GPU session was
allocated for this fixture. Private wallet/recovery and Core wallet files remain
local and are excluded from published evidence and future GPU payloads.

Remaining gates include native component and matched-performance validation,
reviewed host execution/collection with durable CPU-bound range accounting,
full fresh final-image search, one-time local signing and unchanged Core
withdrawal verification, final review and reviewed release publication. The
candidate remains on hold and mainnet remains disabled.
