"""Test-only Core 27.2 ABI adapter for arbitrary input counts.

Reads one JSON object on stdin with ``transaction_hex`` and ordered
``spent_outputs`` (each with ``script_pubkey_hex`` and ``value``). It calls the
pinned libbitcoinconsensus API version 2 for every input and prints its raw
valid/error results. Run inside the same Linux image as the pinned two-input
wrapper with the pinned library mounted at /native. No RPC or broadcast path.

The ctypes layout and flag values mirror Core v27.2's
src/script/bitcoinconsensus.h. This adapter is finite-test instrumentation,
not a source-level proof or an alternative consensus implementation.
"""

import ctypes
import json
import sys


LIBRARY = "/native/libbitcoinconsensus.so.0"
VERIFY_ALL = (1 << 0) | (1 << 2) | (1 << 4) | (1 << 9) | (1 << 10) | (1 << 11) | (1 << 17)


class UTXO(ctypes.Structure):
    _fields_ = [
        ("scriptPubKey", ctypes.POINTER(ctypes.c_ubyte)),
        ("scriptPubKeySize", ctypes.c_uint),
        ("value", ctypes.c_int64),
    ]


def byte_array(data: bytes):
    return (ctypes.c_ubyte * len(data)).from_buffer_copy(data)


def main() -> None:
    request = json.load(sys.stdin)
    transaction = bytes.fromhex(request["transaction_hex"])
    outputs = request["spent_outputs"]
    assert transaction and outputs
    assert all(0 <= output["value"] <= 2100000000000000 for output in outputs)
    scripts = [bytes.fromhex(output["script_pubkey_hex"]) for output in outputs]
    script_arrays = [byte_array(script) for script in scripts]
    spent = (UTXO * len(outputs))(*[
        UTXO(script_array, len(script), output["value"])
        for script_array, script, output in zip(script_arrays, scripts, outputs)
    ])
    tx_array = byte_array(transaction)

    # The official 27.2 library is normally loaded by the statically linked
    # C++ wrapper. Python must expose libstdc++ RTTI symbols first.
    ctypes.CDLL("libstdc++.so.6", mode=ctypes.RTLD_GLOBAL)
    library = ctypes.CDLL(LIBRARY)
    library.bitcoinconsensus_version.argtypes = []
    library.bitcoinconsensus_version.restype = ctypes.c_uint
    version = library.bitcoinconsensus_version()
    assert version == 2, version
    verify = library.bitcoinconsensus_verify_script_with_spent_outputs
    verify.argtypes = [
        ctypes.POINTER(ctypes.c_ubyte), ctypes.c_uint, ctypes.c_int64,
        ctypes.POINTER(ctypes.c_ubyte), ctypes.c_uint,
        ctypes.POINTER(UTXO), ctypes.c_uint, ctypes.c_uint, ctypes.c_uint,
        ctypes.POINTER(ctypes.c_int),
    ]
    verify.restype = ctypes.c_int
    results = []
    for index, (script_array, script, output) in enumerate(
            zip(script_arrays, scripts, outputs)):
        error = ctypes.c_int(-1)
        valid = verify(script_array, len(script), output["value"],
                       tx_array, len(transaction), spent, len(outputs),
                       index, VERIFY_ALL, ctypes.byref(error))
        results.append({"valid": valid == 1, "error": error.value})
    print(json.dumps({"api_version": version, "flags": VERIFY_ALL,
                      "inputs": results}, sort_keys=True))


if __name__ == "__main__":
    main()
