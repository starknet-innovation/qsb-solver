"""Deterministic public scalar edges for the source-locked OpenSSL point audit."""
import hashlib
from pathlib import Path
import struct
import sys

N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
MASK = (1 << 256) - 1


def scalars():
    values = {0, 1, 2, N-1, N, N+1, MASK}
    # Include scalar-word, sign/recode and reduction boundaries on both sides.
    for bit in range(256):
        for delta in (-1, 0, 1):
            values.add(((1 << bit) + delta) & MASK)
            values.add((N - (1 << bit) + delta) & MASK)
    for i in range(4096):
        values.add(int.from_bytes(hashlib.sha256(b'qsb-promotion-curve-v1:' + str(i).encode()).digest(), 'big'))
    return sorted(values)


def encode(values):
    # point_case: k[4], u[3], v[3], signs[2], digits[14], 144 bytes.
    return struct.pack('<I', len(values)) + b''.join(v.to_bytes(32, 'little') + bytes(112) for v in values)


if __name__ == '__main__':
    data = encode(scalars())
    Path(sys.argv[1]).write_bytes(data)
    print(f'{len(scalars())} scalar cases; SHA256 {hashlib.sha256(data).hexdigest()}')
