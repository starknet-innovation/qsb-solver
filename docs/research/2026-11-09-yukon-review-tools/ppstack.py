"""Print the enclosing preprocessor-conditional stack for lines matching a regex."""
import re, sys
path, pat = sys.argv[1], re.compile(sys.argv[2])
mode = sys.argv[3] if len(sys.argv) > 3 else "all"   # "def" = only #define lines
stack = []; seen = {}
lines = open(path, errors="replace").read().split("\n")
i = 0
while i < len(lines):
    l = lines[i]; n = i + 1
    while l.endswith("\\") and i + 1 < len(lines):
        i += 1; l = l[:-1] + lines[i]
    m = re.match(r"\s*#\s*(if|ifdef|ifndef|elif|else|endif)\b(.*)", l)
    if m:
        k, rest = m.group(1), re.sub(r"/\*.*", "", m.group(2)).strip()[:110]
        if k in ("if", "ifdef", "ifndef"): stack.append([f"{k} {rest}"])
        elif k == "elif" and stack: stack[-1].append(f"elif {rest}")
        elif k == "else" and stack: stack[-1].append("else")
        elif k == "endif" and stack: stack.pop()
    if pat.search(l) and (mode == "all" or re.match(r"\s*#\s*define", l)):
        key = " >> ".join(" | ".join(s[-2:]) if len(s) > 1 else s[0] for s in stack)
        seen.setdefault(key, []).append(n)
    i += 1
for k, v in seen.items():
    print(f"  L{v[0]}{'..L%d' % v[-1] if len(v) > 1 else ''} (x{len(v)}): {k or '<top level>'}")
