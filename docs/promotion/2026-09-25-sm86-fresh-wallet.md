# Fresh sm86 local-wallet preparation

Status: HOLD; wallet/commitments prepared and public request validated, **not
funded, searched, signed or mined**. No mainnet transaction is authorized here.

The one-shot generator at c06bb3c created a new local disposable wallet and fresh
QSB config-A commitments for request `ea06c087-b04c-496a-9325-0c801cda08ae`.
The strict existing offline fixture validator accepted `fixtureChain=regtest`,
the nested SegWit public helper binding, full public commitment schema, DER
signatures and reconstructed 9,923-byte script. The mainnet-formatted address is
only an offline schema convention and must never receive mainnet funding.

Private key and recovery remain local in a new0700 directory with0600 files;
permissions were verified through metadata only. Nothing private was printed,
uploaded or committed. Independent review inspected the generator and public
reference hashes, not private material. Three focused generator tests pass.

The JSON receipt records separate raw-file and canonical-request hashes; they
are intentionally different encodings. Neither substitutes for a later frozen
funding manifest. Previous sm89 wallet/coverage and spent fixtures remain separate.

Next: prepare a new offline Core funding fixture, freeze its public manifest and
CPU reference, and bind the execution/budget/coverage campaign. Native component
and matched-performance gates, actual collected execution, full fresh proof,
final review and release publication remain incomplete. Local request validation
is not proof of a solved withdrawal or external miner inclusion.
