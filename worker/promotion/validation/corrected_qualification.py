"""Bounded corrected-script native qualification; never funds or credits work.

prepare runs the hash-pinned qsb-app CPU reference; run only executes explicit
hash-pinned artifacts. A derivative trace is not a final-binary coverage proof.
"""
import argparse
import base64
import hashlib
import json
import math
from pathlib import Path
import re
import subprocess
import sys
import time

VERSION = "qsb-config-a-cmsverify-v1"
TOTAL = math.comb(150, 9)
TRACE = re.compile(r"^TRACE_SUB indices=([0-9,]+) recid=([01]) hash=([0-9a-f]{64})$", re.M)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def unrank(rank):
    if not 0 <= rank < TOTAL:
        raise ValueError("rank out of domain")
    result, lo = [], 0
    for k in range(9, 0, -1):
        for value in range(lo, 150):
            count = math.comb(149-value, k-1)
            if rank < count:
                result.append(value); lo = value+1; break
            rank -= count
    return result


def verify_trace(log, expected):
    found = {}
    lines = [line for line in log.splitlines() if line.startswith("TRACE_SUB")]
    for line in lines:
        match = TRACE.fullmatch(line)
        if not match:
            raise ValueError("malformed trace")
        indices, recid, digest = match.groups()
        key = indices+":"+recid
        if key in found:
            raise ValueError("duplicate trace lane")
        found[key] = digest
    if found != expected:
        raise ValueError("missing, extra or mismatching CPU/GPU hash")
    return len(found)


def prepare(app, fixture, output):
    provenance = json.loads((fixture/"provenance.json").read_text())
    if provenance["scriptVersion"] != VERSION:
        raise ValueError("wrong fixture version")
    for name, digest in provenance["files"].items():
        if sha(fixture/name) != digest:
            raise ValueError("fixture mismatch: "+name)
    for name, digest in provenance["sourceFiles"].items():
        if sha(app/name) != digest:
            raise ValueError("reference source mismatch: "+name)
    sys.path.insert(0, str(app/"public/qsb"))
    from bitcoin_tx import Transaction, TxIn, TxOut, find_and_delete
    from secp256k1 import ecdsa_recover, compress_pubkey
    state = json.loads((fixture/"public-state.json").read_text())
    txdata = json.loads((fixture/"gpu_pinning_params.json").read_text())["spending_tx"]
    cases = []
    for round_number in (1, 2):
        for sequence, locktime in ((0x80000000, 500000000), (0xffffffff, 1744599999)):
            tx = Transaction(version=txdata["version"], locktime=locktime)
            for label in ("extra_input", "qsb_input"):
                item = txdata[label]
                tx.add_input(TxIn(bytes.fromhex(item["txid"]), item["vout"], b"",
                                  sequence if label == "qsb_input" else item["sequence"]))
            out = txdata["output"]
            tx.add_output(TxOut(out["value"], bytes.fromhex(out["script_pubkey"])))
            for start in (0, 63, 127, TOTAL-4):
                expected = {}
                for rank in range(start, start+4):
                    indices = unrank(rank)
                    sig = state["round_sigs"][round_number-1]
                    script = find_and_delete(bytes.fromhex(state["full_script_hex"]), bytes.fromhex(sig["sig"]))
                    for index in indices:
                        script = find_and_delete(script, bytes.fromhex(state["dummy_sigs"][round_number-1][149-index]))
                    z = tx.sighash(txdata["qsb_input_index"], script, txdata["sighash_type"])
                    for recid in (0, 1):
                        point = ecdsa_recover(sig["r"], sig["s"], z, recid)
                        if point is None:
                            raise ValueError("exceptional fixture requires separate trace adapter")
                        key = ",".join(map(str,indices))+":"+str(recid)
                        expected[key] = hashlib.sha256(compress_pubkey(point)).hexdigest()
                cases.append(dict(name=f"r{round_number}-{sequence}-{start}", round=round_number,
                                  sequence=sequence, locktime=locktime, start=start, count=4,
                                  params=base64.b64encode((fixture/f"digest_r{round_number}.bin").read_bytes()).decode(), expected=expected))
    plan = dict(scriptVersion=VERSION, provenanceSha256=sha(fixture/"provenance.json"),
                referenceSources=provenance["sourceFiles"], cases=cases,
                pinningParams=base64.b64encode((fixture/"pinning.bin").read_bytes()).decode(),
                limits="128 recovered-key hashes; subset trace derivative plus exact-binary smokes; no pinning hash differential, real-hit or fresh withdrawal proof")
    with output.open("x") as stream:
        json.dump(plan, stream, indent=2); stream.write("\n")


def validate_trace_receipt(receipt_path, binaries):
    receipt = json.loads(receipt_path.read_text())
    if receipt.get("architecture") != "sm_86":
        raise ValueError("sm86 trace required")
    if receipt.get("unmodifiedBinarySha256") != binaries["subset"][1]:
        raise ValueError("trace source build does not match exact binary")
    if receipt.get("files", {}).get("trace-subset") != binaries["trace"][1]:
        raise ValueError("trace receipt binary mismatch")
    for name, digest in receipt.get("files", {}).items():
        if name not in ("trace-subset", "trace.diff") or sha(receipt_path.parent/name) != digest:
            raise ValueError("trace receipt artifact mismatch")
    if set(receipt.get("files", {})) != {"trace-subset", "trace.diff"}:
        raise ValueError("trace inventory mismatch")
    return receipt


def run(plan_path, plan_hash, binaries, output, trace_receipt, baseline=None):
    from benchmark import execute
    from run_edge_audit import run as run_pinning
    if sha(plan_path) != plan_hash:
        raise ValueError("plan identity mismatch")
    plan = json.loads(plan_path.read_text())
    if plan["scriptVersion"] != VERSION or len(plan["cases"]) != 16:
        raise ValueError("wrong plan inventory/version")
    for path, digest in binaries.values():
        if not re.fullmatch("[0-9a-f]{64}", digest) or sha(path) != digest:
            raise ValueError("binary identity mismatch")
    if baseline is not None and (not re.fullmatch("[0-9a-f]{64}", baseline[1]) or sha(baseline[0]) != baseline[1]):
        raise ValueError("baseline identity mismatch")
    receipt = validate_trace_receipt(trace_receipt, binaries)
    gpu = subprocess.check_output(["nvidia-smi", "--query-gpu=name,uuid,driver_version", "--format=csv,noheader"], text=True).strip()
    if len(gpu.splitlines()) != 1:
        raise ValueError("exactly one GPU required")
    result = dict(status="RUNNING", planSha256=plan_hash, gpu=gpu,
                  traceReceipt=receipt, binaries={k:v[1] for k,v in binaries.items()}, ranges=[], pinning=[], performance=[], baselineSha256=baseline[1] if baseline else None, freshWithdrawal=False)
    # Exclusive creation prevents accidentally overwriting an earlier paid run.
    with output.open("x") as stream:
        json.dump(result, stream)
    deadline = time.monotonic()+600
    try:
        for case in plan["cases"]:
            rows = {}
            for kind in ("trace", "subset"):
                row = execute(binaries[kind][0], case, case["count"], case["start"], deadline)
                if row["hit"]:
                    raise ValueError("unexpected real hit requires separate CPU verification; no credit")
                if kind == "trace":
                    row["cpuHashesVerified"] = verify_trace(row["log"], case["expected"])
                rows[kind] = row
            result["ranges"].append(dict(name=case["name"], **rows))
        for sequence, locktime in ((0x80000000,500000000),(0xffffffff,1744599999)):
            row = run_pinning(binaries["pinning"][0], plan["pinningParams"],
                             ["0","1","0","single_hash",f"seq_start={sequence}","seq_count=1",f"lt_start={locktime}","lt_count=1"],deadline)
            result["pinning"].append(dict(sequence=sequence,locktime=locktime,**row))
            if row["exit"] or "Done:" not in row["log"] or "QSB_RANGE_INCOMPLETE" in row["log"] or row["hits"]:
                raise ValueError("pinning smoke failed or real hit needs CPU verification")
        if baseline is not None:
            for round_number in (1, 2):
                case = next(c for c in plan["cases"] if c["round"] == round_number and c["start"] == 0)
                for sample in range(3):
                    order = [("baseline", baseline[0]), ("candidate", binaries["subset"][0])]
                    if sample % 2:
                        order.reverse()
                    for label, binary in order:
                        row = execute(binary, case, 1 << 28, 0, deadline)
                        result["performance"].append(dict(round=round_number, sample=sample, binary=label, **row))
                        if row["hit"]:
                            raise ValueError("benchmark hit requires CPU verification; no credit")
        result["status"] = "BOUNDED_NATIVE_PASS"
    except Exception as exc:
        result["status"] = "FAILED"; result["error"] = str(exc)
        raise
    finally:
        temporary = output.with_suffix(output.suffix+".tmp")
        temporary.write_text(json.dumps(result,indent=2)+"\n"); temporary.replace(output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="mode", required=True)
    p = sub.add_parser("prepare")
    for name in ("app", "fixtures", "output"):
        p.add_argument("--"+name, type=Path, required=True)
    p = sub.add_parser("run")
    p.add_argument("--plan", type=Path, required=True); p.add_argument("--plan-sha256", required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--trace-receipt", type=Path, required=True)
    p.add_argument("--baseline", type=Path)
    p.add_argument("--baseline-sha256")
    for name in ("trace", "subset", "pinning"):
        p.add_argument("--"+name, type=Path, required=True)
        p.add_argument("--"+name+"-sha256", required=True)
    args = parser.parse_args()
    if args.mode == "prepare":
        prepare(args.app.resolve(), args.fixtures.resolve(), args.output.resolve())
    else:
        if bool(args.baseline) != bool(args.baseline_sha256):
            parser.error("baseline path and hash must be supplied together")
        run(args.plan, args.plan_sha256,
            {n:(getattr(args,n).resolve(),getattr(args,n+"_sha256")) for n in ("trace","subset","pinning")},args.output,args.trace_receipt, (args.baseline.resolve(),args.baseline_sha256) if args.baseline else None)


if __name__ == "__main__":
    main()
