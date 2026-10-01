"""Validate collected table-only evidence; never awards solver/range credit."""
import argparse
import hashlib
import json
import math
from pathlib import Path
import re
import statistics

COMPLETE = "Exact full-table differential and independent OpenSSL samples passed; receipt saved."
TOOLS = ("normal", "memcheck", "racecheck", "synccheck")
COUNTS = {"geometry": 15, "records_per_table": 1048576,
          "full_tables_compared": 4, "exceptional_inputs": 30,
          "openssl_samples_per_table": 252}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def strict_json(raw):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, "duplicate JSON key")
            result[key] = value
        return result

    def invalid(value):
        raise ValueError("nonfinite JSON number: " + value)

    return json.loads(raw, object_pairs_hook=pairs, parse_constant=invalid)


def validate(files, binary_sha256, image, command_exit):
    require(type(command_exit) is int and command_exit == 0, "host command failed")
    require(re.fullmatch(r"[0-9a-f]{64}", binary_sha256), "invalid expected binary hash")
    require(files["exit-code.txt"].strip() == "0", "gate failed")
    require(re.fullmatch(r"ghcr.io/starknet-innovation/qsb-solver@sha256:[0-9a-f]{64}", image), "unpinned runtime")
    require(files["runtime.txt"].strip() == image, "runtime mismatch")
    require(files["binary.sha256"].split() == [binary_sha256, "table-gate"], "binary mismatch")
    gpu_lines = files["gpu.txt"].strip().splitlines()
    require(len(gpu_lines) == 1, "expected one GPU")
    gpu_fields = [field.strip() for field in gpu_lines[0].split(",")]
    require(len(gpu_fields) == 3 and all(gpu_fields) and gpu_fields[1].startswith("GPU-"), "incomplete GPU identity")
    gpu_name = gpu_fields[0]
    require(gpu_name == "NVIDIA A10G", "unexpected GPU")
    require("QSB_COLLECTION_ERROR" not in files.get("gate.log", ""), "collection error")
    reports = {}
    for name in TOOLS:
        row = strict_json(files[name + ".json"])
        require(type(row) is dict and row.get("status") == "passed", "report failed")
        for key, expected in COUNTS.items():
            require(type(row.get(key)) is int and row[key] == expected, "wrong " + key)
        require(row.get("gpu") == gpu_name, "GPU report mismatch")
        hashes = row.get("table_sha256")
        require(type(hashes) is list and len(hashes) == 3 and
                all(type(h) is str and re.fullmatch(r"[0-9a-f]{64}", h) for h in hashes), "invalid table hashes")
        require(row.get("timingExecuted") is (name == "normal"), "timing mode mismatch")
        samples = row.get("samples")
        require(type(samples) is list and len(samples) == (14 if name == "normal" else 0), "incomplete samples")
        for index, sample in enumerate(samples):
            pair, order = divmod(index, 2)
            require(type(sample) is dict, "invalid sample")
            require(type(sample.get("pair")) is int and sample["pair"] == pair and
                    type(sample.get("order")) is int and sample["order"] == order, "sample order mismatch")
            require(sample.get("binary") == ("candidate" if (pair + order) % 2 else "baseline"), "pair identity mismatch")
            for key in ("kernel_ms", "construction_ms"):
                value = sample.get(key)
                require(type(value) in (int, float) and math.isfinite(value) and value > 0,
                        "nonpositive or nonfinite timing; cannot compute ratio")
        log = files[name + ".log"]
        require(log.count(COMPLETE) == 1, "missing/duplicate completion marker")
        if name != "normal":
            require("COMPUTE-SANITIZER" in log, "missing sanitizer banner")
            expected = ("========= RACECHECK SUMMARY: 0 hazards displayed (0 errors, 0 warnings)"
                        if name == "racecheck" else "========= ERROR SUMMARY: 0 errors")
            summaries = [line.strip() for line in log.splitlines() if "SUMMARY:" in line]
            require(summaries == [expected], name + " missing, ambiguous or nonzero summary")
        reports[name] = row
    require(all(r["table_sha256"] == reports["normal"]["table_sha256"] for r in reports.values()), "cross-run table mismatch")
    ratios = {}
    for metric in ("kernel_ms", "construction_ms"):
        pairs = reports["normal"]["samples"]
        values = []
        for index in range(0, 14, 2):
            pair = {s["binary"]: s[metric] for s in pairs[index:index + 2]}
            ratio = pair["candidate"] / pair["baseline"]
            require(math.isfinite(ratio) and ratio > 0, "unrepresentable timing ratio")
            values.append(ratio)
        ratios[metric] = {"candidateOverBaseline": values, "median": statistics.median(values),
                          "minimum": min(values), "maximum": max(values)}
    return {"status": "table-gate-passed", "binarySha256": binary_sha256, "runtime": image,
            "tableSha256": reports["normal"]["table_sha256"], "pairedTimeRatios": ratios,
            "solverSpeedupEstablished": False, "grantsRangeCredit": False,
            "scope": "mixed15 public table differential and OpenSSL samples; instrumented table timings only"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("results", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--binary-sha256", required=True)
    parser.add_argument("--image", required=True)
    parser.add_argument("--command-exit", required=True, type=int)
    args = parser.parse_args()
    names = ["exit-code.txt", "runtime.txt", "binary.sha256", "gpu.txt", "gate.log"]
    names += [name + suffix for name in TOOLS for suffix in (".json", ".log")]
    raw = {name: (args.results / name).read_bytes() for name in names}
    result = validate({name: data.decode("utf-8") for name, data in raw.items()},
                      args.binary_sha256, args.image, args.command_exit)
    result["evidenceSha256"] = {name: hashlib.sha256(data).hexdigest() for name, data in raw.items()}
    with args.output.open("x") as stream:
        json.dump(result, stream, indent=2, allow_nan=False)
        stream.write("\n")


if __name__ == "__main__":
    main()
