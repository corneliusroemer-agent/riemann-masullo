"""Critical path of a `lake build -v` log: the chain of imports with the largest total module time.

    python3 critical_path.py <repo root> <build log>

Modules that the log did not rebuild count as 0 s. Also prints, for the slowest modules, the
longest chain through each and how much the full path would shrink if that module took 0 s.
"""
import re
import sys
from pathlib import Path

root, log = Path(sys.argv[1]), sys.argv[2]
pat = re.compile(r'Built (RiemannMasullo\.[\w.]+) \(([0-9.]+)(ms|s|m)\)')
times = {}
for line in open(log, encoding='utf-8', errors='replace'):
    m = pat.search(line)
    if m:
        times[m.group(1)] = float(m.group(2)) * {'ms': 0.001, 's': 1, 'm': 60}[m.group(3)]

imp = re.compile(r'^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(RiemannMasullo[\w.]*)', re.M)
deps = {}
for f in (root / 'RiemannMasullo').rglob('*.lean'):
    mod = '.'.join(f.relative_to(root).with_suffix('').parts)
    head = f.read_text(encoding='utf-8', errors='replace')[:20000]
    deps[mod] = [d for d in imp.findall(head) if d != mod]


def longest(times):
    memo = {}

    def go(m):  # longest chain ending at m (m included)
        if m in memo:
            return memo[m]
        memo[m] = (0.0, [])          # cycle guard
        best = (0.0, [])
        for d in deps.get(m, []):
            c = go(d)
            if c[0] > best[0]:
                best = c
        memo[m] = (best[0] + times.get(m, 0.0), best[1] + [m])
        return memo[m]

    return max((go(m) for m in deps), key=lambda c: c[0]), go


(total, path), go = longest(times)
print(f'{len(times)} modules timed, sum {sum(times.values()):.0f} s; critical path {total:.0f} s, {len(path)} modules:')
for m in path:
    if times.get(m, 0) >= 1:
        print(f'  {times[m]:6.1f} s  {m}')
print('\nif one module took 0 s, the critical path would be:')
for m, t in sorted(times.items(), key=lambda kv: -kv[1])[:12]:
    (t2, _), _ = longest({**times, m: 0.0})
    print(f'  {t:6.1f} s  {m:60s} -> {t2:5.0f} s ({t2 - total:+.0f} s)')

# what-if: drop import edges given as extra arguments "A>B" (A no longer imports B)
for spec in sys.argv[3:]:
    a, b = spec.split('>')
    a, b = 'RiemannMasullo.' + a, 'RiemannMasullo.' + b
    deps[a] = [d for d in deps.get(a, []) if d != b]
if sys.argv[3:]:
    (t3, p3), _ = longest(times)
    print(f'\nwithout {sys.argv[3:]}: critical path {t3:.0f} s ({t3 - total:+.0f} s), ends ' +
          ' > '.join(m.split('.', 1)[1] for m in p3 if times.get(m, 0) >= 10))
