#!/usr/bin/env bash
# Print the slowest compiled project modules found in the given lake -v logs.
cat "$@" 2>/dev/null | grep -oE 'Built ContinuousFlexibility[A-Za-z0-9_.]* \([^)]*\)' |
  python3 -c '
import re, sys
rows = {}
for line in sys.stdin:
    m = re.match(r"Built (\S+) \((.*)\)", line.strip())
    if not m: continue
    s = sum(float(v) * {"h": 3600, "m": 60, "s": 1, "ms": 0.001}[u]
            for v, u in re.findall(r"([0-9.]+)(ms|h|m|s)", m.group(2)))
    rows[m.group(1)] = max(s, rows.get(m.group(1), 0))
top = sorted(rows.items(), key=lambda kv: -kv[1])[:15]
print(f"compiled project modules: {len(rows)}; slowest:")
for name, s in top:
    print(f"  {s/60:6.1f} min  {name}")
'
