"""Differentially test Lean's DER predicate against pinned Core 27.2.

The isolated bare lock is CHECKSIG; DROP; TRUE. Under the recorded VERIFY_ALL
flags, a malformed nonempty signature aborts CHECKSIG, while an ECDSA failure
after successful syntax parsing leaves a Boolean that DROP discards. Empty
signatures are Core's documented special case. This tests parser behavior on
the listed corpus, not all byte strings or the complete QSB lock.
"""

import argparse
import hashlib
import json
import random
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def der(r: bytes, s: bytes, hashtype: int = 3) -> bytes:
    return bytes((0x30, len(r) + len(s) + 4, 0x02, len(r))) + r + bytes(
        (0x02, len(s))) + s + bytes((hashtype,))


def corpus() -> list[tuple[str, bytes]]:
    cases: list[tuple[str, bytes]] = []
    for rlen in range(1, 13):
        slen = 13 - rlen
        r = b"\x01" + b"\x11" * (rlen - 1)
        s = b"\x01" + b"\x22" * (slen - 1)
        cases.append((f"canonical_r{rlen}", der(r, s)))
        if rlen > 1:
            cases.append((f"r_sign_pad_r{rlen}", der(
                b"\x00\x80" + b"\x11" * (rlen - 2), s)))
        if slen > 1:
            cases.append((f"s_sign_pad_r{rlen}", der(
                r, b"\x00\x80" + b"\x22" * (slen - 2))))

    base = bytearray(der(b"\x01", b"\x01" + b"\x22" * 11))
    mutations = {
        "wrong_sequence_tag": (0, 0x31),
        "wrong_total_length": (1, 0x10),
        "wrong_r_tag": (2, 0x03),
        "zero_r_length": (3, 0),
        "oversized_r_length": (3, 13),
        "negative_r": (4, 0x81),
        "wrong_s_tag": (5, 0x03),
        "zero_s_length": (6, 0),
        "wrong_s_length": (6, 11),
        "negative_s": (7, 0x81),
    }
    for name, (position, value) in mutations.items():
        sig = base.copy()
        sig[position] = value
        cases.append((name, bytes(sig)))
    padded_r = bytearray(der(b"\x01\x11", b"\x01" + b"\x22" * 10))
    padded_r[4] = 0
    cases.append(("excess_r_padding", bytes(padded_r)))
    padded_s = base.copy()
    padded_s[7] = 0
    cases.append(("excess_s_padding", bytes(padded_s)))
    for hashtype in (0, 1, 2, 0x80, 0x83, 0xff):
        cases.append((f"hashtype_{hashtype:02x}", der(
            b"\x01", b"\x01" + b"\x22" * 11, hashtype)))
    cases.extend((
        ("empty_special_case", b""),
        ("valid_minimum_9", der(b"\x01", b"\x01")),
        ("too_short_8", der(b"\x01", b"\x01")[:-1]),
        ("valid_maximum_73", der(b"\x01" + b"\x11" * 32,
                                  b"\x01" + b"\x22" * 32)),
        ("too_long_74", der(b"\x01" + b"\x11" * 33,
                             b"\x01" + b"\x22" * 32)),
    ))
    rng = random.Random("QSB DER parser differential public corpus")
    cases.extend((f"random20_{i:02d}", rng.randbytes(20))
                 for i in range(16))
    assert len({name for name, _ in cases}) == len(cases)
    return cases


def lean_results(cases: list[tuple[str, bytes]]) -> list[tuple[bool, bool]]:
    source = "import QSB.DERSyntax\n" + "".join(
        "#eval QSB.DERSyntax.valid [" + ", ".join(str(b) for b in sig) +
        "]\n#eval QSB.DERSyntax.verifyAllEncoding [" +
        ", ".join(str(b) for b in sig) + "]\n" for _, sig in cases)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=ROOT,
                                     delete=True) as temp:
        temp.write(source)
        temp.flush()
        run = subprocess.run(["lake", "env", "lean", temp.name], cwd=ROOT,
                             text=True, capture_output=True, timeout=120)
    if run.returncode:
        raise RuntimeError(run.stdout + run.stderr)
    lines = run.stdout.splitlines()
    if len(lines) != 2 * len(cases) or any(line not in ("true", "false")
                                      for line in lines):
        raise RuntimeError(f"unexpected Lean output: {run.stdout!r}")
    return [(lines[2 * i] == "true", lines[2 * i + 1] == "true")
            for i in range(len(cases))]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--app-root", type=Path, required=True)
    parser.add_argument("--native-root", type=Path, required=True)
    parser.add_argument("--image", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    sys.path.insert(0, str(args.app_root / "worker/cpu"))
    import bitcoin_tx as bt
    import secp256k1 as ec

    cases = corpus()
    lean = lean_results(cases)
    tx = bt.Transaction(version=1, locktime=0)
    tx.add_input(bt.TxIn(b"\x44" * 32, 0, b"", 0xFFFFFFFE))
    tx.add_input(bt.TxIn(b"\x55" * 32, 0, b"", 0xFFFFFFFE))
    tx.add_output(bt.TxOut(90000, b"\x51"))
    pubkey = ec.compress_pubkey(ec.G)
    lock = bytes((0xAC, 0x75, 0x51))  # CHECKSIG; DROP; TRUE
    native = args.native_root.resolve()
    observed = []
    for (name, sig), (syntax_valid, encoding_valid) in zip(
            cases, lean, strict=True):
        tx.inputs[1].script_sig = bt.push_data(sig) + bt.push_data(pubkey)
        raw_tx = tx.serialize()
        payload = f"{raw_tx.hex()}\n2\n1000\n51\n100000\n{lock.hex()}\n"
        run = subprocess.run([
            "docker", "run", "--rm", "--network", "none", "--read-only",
            "--cap-drop=ALL", "--security-opt=no-new-privileges",
            "--platform=linux/arm64", "-i", "-v", f"{native}:/native:ro",
            args.image, "/native/qsb-consensus"],
            input=payload, text=True, capture_output=True, timeout=30)
        if run.returncode not in (0, 1):
            raise RuntimeError(f"Core unavailable for {name}: {run.stderr}")
        accepted = (run.returncode == 0 and
                    run.stdout.strip() == "core-27.2-api2-all-inputs-valid")
        expected = encoding_valid
        observed.append({"name": name, "signature_hex": sig.hex(),
                         "lean_valid": syntax_valid,
                         "lean_verify_all_encoding": encoding_valid,
                         "core_accepted": accepted,
                         "expected": expected,
                         "raw_tx_sha256": hashlib.sha256(raw_tx).hexdigest()})
        if accepted != expected:
            raise AssertionError(observed[-1])
    report = {
        "scope": "isolated bare CHECKSIG; DROP; TRUE parser corpus, not QSB lock",
        "core_flags": "bitcoinconsensus_SCRIPT_FLAGS_VERIFY_ALL",
        "source_revision": subprocess.check_output(
            ["git", "-C", str(args.app_root), "rev-parse", "HEAD"],
            text=True).strip(),
        "image": args.image,
        "native_executable_sha256": hashlib.sha256(
            (native / "qsb-consensus").read_bytes()).hexdigest(),
        "native_library_sha256": hashlib.sha256(
            (native / "libbitcoinconsensus.so.0").read_bytes()).hexdigest(),
        "case_count": len(observed),
        "matching_count": sum(c["core_accepted"] == c["expected"]
                              for c in observed),
        "cases": observed,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"case_count": report["case_count"],
                      "matching_count": report["matching_count"]}, indent=2))


if __name__ == "__main__":
    main()
