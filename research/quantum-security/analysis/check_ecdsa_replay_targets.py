"""Exhibit two distinct ECDSA messages for one fixed signature and public key.

The scalars are deliberately public disposable values. This is an algebraic
secp256k1 check, not a Bitcoin transaction, a SHA256d preimage, or a spend.
It shows why a same-key replay event cannot be restricted to digest collisions.
"""

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--app-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    app = args.app_root.resolve()
    root = Path(__file__).resolve().parents[1]
    sys.path.insert(0, str(app / "worker/cpu"))
    import secp256k1 as ec

    pinned = json.loads((root / "evidence/source-inventory.json").read_text())
    source_hash = hashlib.sha256((app / "worker/cpu/secp256k1.py").read_bytes()).hexdigest()
    assert source_hash == pinned["app"]["files"]["worker/cpu/secp256k1.py"]
    assert ec.P == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
    assert ec.N == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
    assert ec.P < 2 * ec.N

    # Q=xG and R=kG. ECDSA verification uses x(R) modulo the group order.
    # R and -R have the same x-coordinate, but their equations use two
    # different z values for this same (r,s,Q).
    x, k, s = 7, 3, 11
    pub = ec.point_mul(x, ec.G)
    point = ec.point_mul(k, ec.G)
    r = point[0] % ec.N
    z_positive = (s * k - r * x) % ec.N
    z_negative = (-s * k - r * x) % ec.N
    assert z_positive != z_negative
    assert ec.ecdsa_verify(pub, z_positive, r, s)
    assert ec.ecdsa_verify(pub, z_negative, r, s)
    assert ec.ecdsa_recover(r, s, z_positive, point[1] % 2) == pub
    assert ec.ecdsa_recover(r, s, z_negative, 1 - point[1] % 2) == pub

    # The app's two-parity recovery helper only reconstructs x=r. Verification
    # can also use x=r+N when that value is below P and lies on the curve.
    # For this public algebraic fixture z=0; no SHA256d preimage is claimed.
    alternate_r, alternate_s, alternate_z = 2, 1, 0
    alternate_x = ec.N + alternate_r
    assert alternate_x < ec.P
    alternate_rhs = (pow(alternate_x, 3, ec.P) + ec.B) % ec.P
    alternate_y = pow(alternate_rhs, (ec.P + 1) // 4, ec.P)
    assert pow(alternate_y, 2, ec.P) == alternate_rhs
    alternate_point = (alternate_x, alternate_y)
    alternate_pub = ec.point_mul(ec.modinv(alternate_r, ec.N), alternate_point)
    assert ec.ecdsa_verify(alternate_pub, alternate_z, alternate_r, alternate_s)
    app_recovered = [ec.ecdsa_recover(alternate_r, alternate_s, alternate_z, parity)
                     for parity in (0, 1)]
    assert all(candidate != alternate_pub for candidate in app_recovered)

    report = {
        "scope": "public disposable secp256k1 algebra; no transaction or SHA256d preimage",
        "pinned_source_revision": pinned["app"]["revision"],
        "observed_app_head": subprocess.check_output(
            ["git", "-C", str(app), "rev-parse", "HEAD"], text=True).strip(),
        "secp256k1_sha256": source_hash,
        "field_prime_hex": f"{ec.P:064x}",
        "group_order_hex": f"{ec.N:064x}",
        "field_prime_lt_twice_order": True,
        "public_fixture_scalars": {"x": x, "k": k, "s": s},
        "r_hex": f"{r:064x}",
        "signature_hex": ec.encode_der_sig(r, s, sighash=1).hex(),
        "public_key_hex": ec.compress_pubkey(pub).hex(),
        "message_scalar_positive_hex": f"{z_positive:064x}",
        "message_scalar_negative_hex": f"{z_negative:064x}",
        "messages_distinct": True,
        "both_ecdsa_verify": True,
        "both_recover_same_key": True,
        "alternate_x_fixture": {
            "scope": "ECDSA scalar z=0 only; no SHA256d preimage or Bitcoin transaction",
            "r": alternate_r,
            "s": alternate_s,
            "message_scalar": alternate_z,
            "recovery_x_hex": f"{alternate_x:064x}",
            "recovery_y_hex": f"{alternate_y:064x}",
            "public_key_hex": ec.compress_pubkey(alternate_pub).hex(),
            "signature_hex": ec.encode_der_sig(alternate_r, alternate_s, sighash=1).hex(),
            "ecdsa_verify": True,
            "app_two_parities_recover_this_key": False,
        },
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in (
        "messages_distinct", "both_ecdsa_verify", "both_recover_same_key")}, indent=2))


if __name__ == "__main__":
    main()
