# Verified TLS replacement publication

The exact qualified OCI archive was copied without rebuilding in run 43220125543.
Independent readback matches its index, platform and config and verifies the
original build attestation both from the registry bundle and GitHub API, requiring
source cfd99e3844698f59679e4c15cf567db2976b9ffc, the dedicated qualification branch,
workflow and run 43205074943 on a GitHub-hosted runner. Anonymous registry reads pass.

The released descriptor equals the independently verified build proposal's solver
object and the released contract equals both repositories. Downloaded release assets
and split archive parts match provider digest metadata; the archive SHA matches
the original signed build. Registry digests identify the immutable artifact.

Qualification uses retained native evidence only for identical compute components
and fresh installed TLS/S3 tests. No fresh native GPU execution or timing is claimed.
All 20 Critical matches remain visible; see the preceding review package.
Enrollment in existing qsb-app PR #150 remains separate from serving or deployment.

The original decision/build/native packages are unchanged; this is a new readback.
