import re, sys
# Compare per-module build times of two `lake build -v` logs.
pat = re.compile(r'Built (RiemannMasullo\.[\w.]+) \(([0-9.]+)(ms|s|m)\)')
def load(p):
    d = {}
    for l in open(p, encoding='utf-8', errors='replace'):
        m = pat.search(l)
        if m:
            v = float(m.group(2)) * {'ms': 0.001, 's': 1, 'm': 60}[m.group(3)]
            d[m.group(1)] = v
    return d
a, b = load(sys.argv[1]), load(sys.argv[2])
common = sorted(set(a) & set(b))
ta, tb = sum(a[k] for k in common), sum(b[k] for k in common)
print(f'{len(common)} modules in both: base {ta:.0f}s, abbrev {tb:.0f}s, saved {ta-tb:.0f}s ({100*(ta-tb)/ta:.1f}%)')
rows = sorted(common, key=lambda k: a[k] - b[k], reverse=True)
print('largest savings:')
for k in rows[:12]:
    print(f'  {a[k]:6.1f}s -> {b[k]:6.1f}s  ({a[k]-b[k]:+6.1f}s)  {k}')
print('largest regressions:')
for k in rows[-5:]:
    print(f'  {a[k]:6.1f}s -> {b[k]:6.1f}s  ({a[k]-b[k]:+6.1f}s)  {k}')
