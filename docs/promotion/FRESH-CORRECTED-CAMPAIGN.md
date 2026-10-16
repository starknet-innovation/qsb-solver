# Fresh corrected proof: bounded campaign admission

User authorization for this campaign is **24 aggregate GPU-hours, $30 all-in,
one GPU**. The old bounded experiment and both spent withdrawal fixtures stay
closed. `ops/aws-gpu-execution/fresh_campaign.py` creates a fresh one-shot plan;
it does not call AWS or automatically start a search. Use only new state outside
Git and do not reuse any historical marker/token. A fresh independently verified
cleanup receipt is required before preparing this campaign.

The planner reserves all 24 GPU-hours plus 80 GiB default-performance gp3 storage,
one public IPv4 and a minimum $2 fixed network/control allowance. Using quoted
$1.123/hour compute, $0.005/hour IPv4 and $0.088/GiB-month gp3 (conservative
720-hour month), the reservation is $29.306667. Rates must be supplied as fresh,
hash-bound external public evidence. A more expensive quote fails admission;
the code does not lower a reserve or increase the cap to fit.

After arming, deadlines never move: the host shutdown timer is 23 hours, the
independent token-scoped cleanup Lambda/Scheduler is 23 hours 15 minutes, and the
aggregate reservation expires at 24 hours. Launch must occur within five minutes
of arming, so delayed setup consumes useful runtime. The remaining time reserves
termination latency. Only one RunInstances request can be recorded; uncertain
responses require reconciliation, not replacement. No second GPU is permitted.

This is a reservation at quoted tariffs, not a guarantee of AWS invoice precision
or instantaneous termination. The operator must monitor actual resource state,
terminate promptly on completion/failure, and escalate unresolved shutdown
before the reserve expires. No cleanup success is inferred from a stop request.

An external prepare evidence JSON contains `caller`, `priorGpuCleanupVerified`,
`priorCleanupReceiptSha256` and `quote`. The quote contains decimal-string fields
`computeUsdPerHour`, `publicIpv4UsdPerHour`, `gp3UsdPerGiBMonth`,
`fixedControlNetworkReserveUsd`, plus integer `observedAt` and the exact public
price-receipt `sourceEvidenceSha256`. Operator configuration continues through
`QSB_AWS_OPERATOR_CONFIG`; no credentials enter the plan.

```sh
python3 ops/aws-gpu-execution/fresh_campaign.py prepare --state /new/state.json --evidence /public/prepare.json
python3 ops/aws-gpu-execution/fresh_campaign.py prepared --state /new/state.json --evidence /public/prepare-receipts.json
python3 ops/aws-gpu-execution/fresh_campaign.py arm --state /new/state.json
python3 ops/aws-gpu-execution/fresh_campaign.py launch --state /new/state.json --evidence /public/live-preflight.json
```

Each command writes a plan only. Follow the existing MCP planner's exact ordered
API execution/readback contract, with the fixed new campaign deadlines. Persist
provider IDs and root volume identity before setup. The source must be committed,
pushed and clean before even creating the plan. Never retry a failed/uncertain
paid call or extend a deadline.

**Search execution is a separate gate.** Before launch, the prepared stage
controller must durably record pin context, exact range intents, completed
coverage and CPU-verified hits; reject unknown/submitted work as complete; preserve
uncertain outcomes; and stop/checkpoint before `computeDeadline`. Only public
fixture/export JSON may be uploaded. Keep all wallet/recovery/Core fixture
material local. A solved public result still needs independent CPU and unchanged
Core validation. This planner neither implements that search ledger nor certifies
a withdrawal; without a reviewed stage controller the campaign is not executable.
