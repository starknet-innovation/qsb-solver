"""Repeatedly preprocess; on each #error naming a QSB_/ZLAB_ switch as the offender (first token), set it to 0 and retry."""
import re, subprocess, sys
src, stubs = sys.argv[1], sys.argv[2]
flags = sys.argv[3:]
added = []
for _ in range(40):
    p = subprocess.run(["clang", "-E", "-x", "c++", "-std=c++17", "-D__CUDA_ARCH__=860", "-D__CUDACC__", "-I", stubs, *flags, *added, src],
                       stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
    errs = [l for l in p.stderr.splitlines() if " error: " in l]
    if not errs:
        print("PASS with extra:", " ".join(added) or "(none)"); break
    e = errs[0]; msg = e.split(" error: ", 1)[1]
    m = re.match(r'"?((?:QSB|ZLAB)_[A-Z0-9_]+)', msg)
    loc = re.search(r"([\w./]+:\d+):\d+: error", e).group(1).split("candidates/subset/")[-1]
    print(f"  {loc}: {msg[:150]}")
    if not m or f"-D{m.group(1)}=0" in added + flags:
        print("STOP: cannot resolve automatically"); break
    added.append(f"-D{m.group(1)}=0")
