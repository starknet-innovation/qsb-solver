# Fresh sm86 proof cost admission — preparation only

The user authorized at most USD200 for the fresh proof's compute and associated
infrastructure, separately from the USD100 mainnet BTC pilot. No fresh sm86
search has started. `budget.py` is an admission primitive, **not yet connected to
the launch controller**. It does not authorize a caller to allocate resources.

Each transaction checks the original file identity and campaign authorization,
rejecting a replaced ledger even through an existing handle. The ledger binds a campaign UUID, frozen request hash, candidate source and image
digest. It uses integer USD microdollars, a USD200 authorization and USD20 retained
headroom. An immediate SQLite transaction creates a unique intent and reserves its
full allowance before returning. One unsettled intent blocks all replacements.
Crashes and unknown provider outcomes retain their reservation. Successful cleanup
consumes the full allowance; there are no automatic or optimistic refunds.

The caller must independently gather provider cleanup evidence for the exact
attached instance and root volumes. Structural checks require termination and no
remaining volume, security group, schedule, function, role or instance profile.
The primitive validates bindings, not the truth of caller-supplied cloud evidence.
An unknown or explicit rejected submission cannot currently settle without an
attached resource; a dedicated reconciled rejection path is still needed.

Eleven tests exercise racing reservations, crash/reopen preservation, exact budget
boundaries, fixed authorization, frozen requests, late attachment and invalid
cleanup evidence. These are local SQLite tests, not paid execution tests.

Before the fresh proof can start, integrate a single authoritative ledger and
exclusive controller ownership into the paid prepare/launch path. Require a fresh
verified price quote, a conservative full-session allowance covering startup,
idle/shutdown, storage, IPv4, transfer and control-plane charges, and prearmed
independent cleanup. Bind resource scope and deadline to the intent; never accept
an arbitrary caller-selected allowance as sufficient authorization. Unknown
outcomes must reconcile by token and tags without another launch. Retained
resources or missing/stale pricing must block admission.

This mechanism can limit admitted work against conservatively reserved funds.
It cannot guarantee an AWS invoice ceiling during provider failures or delayed
termination. Headroom and independent cleanup are necessary, not a provider-side
billing cap. Never describe the USD200 limit as already operationally enforced.
