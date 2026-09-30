"""Explore Config A stack provenance with a disposable byte witness.

This is diagnostic code. Signature outcomes are supplied booleans, so a
successful trace is not Bitcoin consensus acceptance or a forgery.
"""
import argparse
import hashlib
import json
import random
import sys
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class Cell:
    value: bytes
    origin: str


def parse_num(raw):
    if len(raw) > 4:
        raise ValueError("ScriptNum exceeds four bytes")
    if not raw:
        return 0
    magnitude = int.from_bytes(raw, "little") & ~(128 << (8 * (len(raw) - 1)))
    return -magnitude if raw[-1] & 128 else magnitude


def encode_num(value):
    if value == 0:
        return b""
    negative = value < 0
    magnitude = abs(value)
    out = magnitude.to_bytes((magnitude.bit_length() + 7) // 8, "little")
    if out[-1] & 128:
        return out + (b"\x80" if negative else b"\0")
    if negative:
        return out[:-1] + bytes([out[-1] | 128])
    return out


def parse_script(script, bt):
    names = {bt.OP_DUP: "dup", bt.OP_OVER: "over", bt.OP_SWAP: "swap",
             bt.OP_ROLL: "roll", bt.OP_MIN: "min", bt.OP_ADD: "add",
             bt.OP_HASH160: "hash160", bt.OP_SHA256_OP: "sha256",
             bt.OP_EQUALVERIFY: "equalverify", bt.OP_CHECKSIGVERIFY: "checksigverify",
             bt.OP_CHECKMULTISIG: "checkmultisig"}
    ops = []
    i = 0
    while i < len(script):
        op = script[i]
        i += 1
        if op == 0:
            ops.append(("push", b""))
        elif 0x51 <= op <= 0x60:
            ops.append(("push", bytes([op - 0x50])))
        elif 1 <= op <= 75:
            ops.append(("push", script[i:i + op]))
            i += op
        else:
            ops.append((names[op], None))
    assert i == len(script) and len(ops) == 880
    return ops


def run(ops, stack, bt, outcomes, stop=None):
    stack = list(stack)
    outcomes = list(outcomes)
    count = 0
    comparisons = []
    for pc, (op, arg) in enumerate(ops[:stop]):
        if op != "push":
            count += 1
        if count > 201:
            return {"failure": pc, "reason": "opcode count", "stack": stack,
                    "comparisons": comparisons}
        try:
            if op == "push":
                assert len(arg) <= 520
                stack.insert(0, Cell(arg, f"lock:{pc}"))
            elif op == "dup":
                stack.insert(0, stack[0])
            elif op == "over":
                stack.insert(0, stack[1])
            elif op == "swap":
                stack[0], stack[1] = stack[1], stack[0]
            elif op == "roll":
                n = parse_num(stack.pop(0).value)
                assert n >= 0
                stack.insert(0, stack.pop(n))
            elif op in ("min", "add"):
                x, y = stack.pop(0), stack.pop(0)
                value = min(parse_num(x.value), parse_num(y.value)) if op == "min" else parse_num(x.value) + parse_num(y.value)
                stack.insert(0, Cell(encode_num(value), f"{op}({x.origin},{y.origin})"))
            elif op == "hash160":
                x = stack.pop(0)
                stack.insert(0, Cell(bt.hash160(x.value), f"hash160({x.origin})"))
            elif op == "sha256":
                x = stack.pop(0)
                stack.insert(0, Cell(hashlib.sha256(x.value).digest(), f"sha256({x.origin})"))
            elif op == "equalverify":
                x, y = stack.pop(0), stack.pop(0)
                comparisons.append((pc, x.origin, y.origin, x.value == y.value))
                assert x.value == y.value
            elif op == "checksigverify":
                stack.pop(0), stack.pop(0)
                assert outcomes.pop(0)
            elif op == "checkmultisig":
                n = parse_num(stack[0].value)
                assert 0 <= n <= 20 and count + n <= 201
                m = parse_num(stack[n + 1].value)
                assert 0 <= m <= n
                assert stack[n + m + 2].value == b""
                stack = [Cell(b"\x01" if outcomes.pop(0) else b"", f"cms:{pc}")] + stack[n + m + 3:]
                count += n
            assert len(stack) <= 1000
        except (AssertionError, IndexError, ValueError) as error:
            return {"failure": pc, "reason": f"{op}: {error}", "stack": stack,
                    "comparisons": comparisons}
    return {"failure": None, "stack": stack, "ops": count,
            "comparisons": comparisons, "outcomes": outcomes}


def make_fixture(app_root):
    sys.path.insert(0, str(app_root / "worker/cpu"))
    import bitcoin_tx as bt
    import secp256k1 as ec

    builder = bt.QSBScriptBuilder(150, 8, 1, 7, 2, hash_mode="sha256")
    rng = random.Random("QSB security analysis: PUBLIC DISPOSABLE TEST MATERIAL")
    old = bt.os.urandom
    try:
        bt.os.urandom = rng.randbytes
        builder.generate_keys()
    finally:
        bt.os.urandom = old

    def nonce_sig(label):
        k = int.from_bytes(hashlib.sha256(label + b"_nonce").digest(), "big") % ec.N
        r = ec.point_mul(k, ec.G)[0] % ec.N
        s = max(1, int.from_bytes(hashlib.sha256(label + b"_s").digest()[:16], "big") % (ec.N // 2))
        return ec.encode_der_sig(r, s, sighash=1)

    script = builder.build_full_script(*(nonce_sig(x) for x in
        (b"qsb_pin", b"qsb_r0", b"qsb_r1")))
    ops = parse_script(script, bt)
    indices = builder.compute_witness_indices({0: list(range(9)), 1: list(range(9))})
    witness = []
    for ri in (1, 0):
        for role in ("puzzle", "nonce"):
            witness.append(Cell(hashlib.sha256(f"round-{ri}-{role}".encode()).digest(), f"witness:round{ri}:{role}"))
        witness.extend(Cell(builder.dummy_sigs[ri][j], f"witness:round{ri}:pub{j}")
                       for j in range(8, -1, -1))
        count = 8 if ri == 0 else 7
        witness.extend(Cell(builder.hors_secrets[ri][j], f"witness:round{ri}:pre{j}")
                       for j in range(count - 1, -1, -1))
        witness.extend(Cell(encode_num(value), f"witness:round{ri}:idx{j}")
                       for j, value in reversed(list(enumerate(indices[ri]))))
    for role in ("puzzle", "nonce"):
        witness.append(Cell(hashlib.sha256(f"pin-{role}".encode()).digest(), f"witness:pin:{role}"))
    witness.reverse()
    source_hash = hashlib.sha256((app_root / "worker/cpu/bitcoin_tx.py").read_bytes()).hexdigest()
    expected = json.loads((Path(__file__).resolve().parents[1] / "evidence/layout-map.json").read_text())
    assert source_hash == expected["builder_sha256"]
    assert hashlib.sha256(script).hexdigest() == expected["script_sha256"]
    return bt, ops, witness


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--app-root", type=Path, required=True)
    parser.add_argument("--probe", choices=("canonical", "external"), default="canonical")
    args = parser.parse_args()
    bt, ops, witness = make_fixture(args.app_root)
    if args.probe == "external":
        witness[2] = Cell(encode_num(152), "probe:index152")
        witness.insert(3, Cell(bt.hash160(b"\x0a"), "probe:external-commitment"))
    result = run(ops, witness, bt, [True, True, True, False, True, True])
    print(json.dumps({k: v for k, v in result.items() if k != "stack"}, indent=2))
    print("stack top:", [(x.origin, x.value.hex()) for x in result["stack"][:8]])


if __name__ == "__main__":
    main()
