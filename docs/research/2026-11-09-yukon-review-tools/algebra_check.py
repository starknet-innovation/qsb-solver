"""Numeric check of two identities quoted in upstream comments. Checks the algebra only, not the CUDA code."""
import random
M = 0xffffffff
ror = lambda x, n: ((x >> n) | (x << (32 - n))) & M
rnd = random.Random(20261109)
for _ in range(200000):
    x = rnd.getrandbits(32)
    assert ror(x,6)^ror(x,11)^ror(x,25) == ror(x ^ ror(x,5) ^ ror(x,19), 6)      # S1
    assert ror(x,2)^ror(x,13)^ror(x,22) == ror(x ^ ror(x,11) ^ ror(x,20), 2)     # S0
for x in (0, 1, M, 0x80000000, 0x7fffffff):
    assert ror(x,6)^ror(x,11)^ror(x,25) == ror(x ^ ror(x,5) ^ ror(x,19), 6)
    assert ror(x,2)^ror(x,13)^ror(x,22) == ror(x ^ ror(x,11) ^ ror(x,20), 2)
p = 2**256 - 2**32 - 977
for _ in range(2000):
    x = [rnd.randrange(1, p) for _ in range(16)]
    P8 = [x[j]*x[j+8] % p for j in range(8)]
    c = [x[i^8]*P8[(i&7)^4] % p for i in range(16)]; P4 = [P8[j]*P8[j+4] % p for j in range(4)]
    d = [c[i]*P4[(i&3)^2] % p for i in range(16)];   P2 = [P4[j]*P4[j+2] % p for j in range(2)]
    E = [d[i]*P2[(i&1)^1] % p for i in range(16)];   root = P2[0]*P2[1] % p
    rinv = pow(root, -1, p)
    assert all(rinv*E[i] % p * x[i] % p == 1 for i in range(16))
print("ok: Sigma identities (200,005 words each), wave-top inverse formula (2,000 blocks of 16)")
