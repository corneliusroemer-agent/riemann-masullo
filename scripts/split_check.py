"""Everything a module split still needs, from `SplitDeps.lean` output and the split branch's imports.

    python3 split_check.py <splitdeps.tsv> <split branch root> Mod:cut:NewFirstMod ...
"""
import re
import sys
from collections import defaultdict
from pathlib import Path

tsv, root = sys.argv[1], Path(sys.argv[2])
splits = {}
for spec in sys.argv[3:]:
    mod, cut, first = spec.split(':')
    splits[mod] = (int(cut), first)

line_of, mod_of = {}, {}
uses = defaultdict(set)          # (module, part) -> {(const, constmodule, private)}
ext = defaultdict(set)           # module -> {const}
for row in open(tsv, encoding='utf-8'):
    f = row.rstrip('\n').split('\t')
    if f[0] == 'DEF':
        line_of[f[1]], mod_of[f[1]] = int(f[3]), f[2]
    elif f[0] == 'USE':
        uses[(f[1], int(f[2]))].add((f[3], f[4], f[5] == 'true'))
    elif f[0] == 'EXT':
        ext[f[1]].add(f[3])


def part(c):
    line = line_of.get(c, 0)
    return None if line == 0 else (1 if line <= splits[mod_of[c]][0] else 2)


def home(c):
    """The module that holds constant c after the split."""
    p = part(c)
    return splits[mod_of[c]][1] if p == 1 else mod_of[c]


# import graph of the split branch: module -> [(imported, public)]
imp = re.compile(r'^(public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(RiemannMasullo[\w.]*)\s*$', re.M)
graph = {}
for f in (root / 'RiemannMasullo').rglob('*.lean'):
    m = '.'.join(f.relative_to(root).with_suffix('').parts)
    graph[m] = [(i, bool(p)) for p, i in imp.findall(f.read_text(encoding='utf-8', errors='replace')[:20000])]


def visible(m):
    """Modules whose public declarations m sees: its imports and, from each, the public imports on."""
    seen, todo = set(), [i for i, _ in graph.get(m, [])]
    while todo:
        x = todo.pop()
        if x in seen:
            continue
        seen.add(x)
        todo += [i for i, pub in graph.get(x, []) if pub]
    return seen


unknown = sorted(c for c in line_of if line_of[c] == 0)
if unknown:
    print(f'{len(unknown)} constants without a source line (left out):', ', '.join(unknown[:8]))

for mod, (cut, first) in splits.items():
    for p, name in ((1, first), (2, mod)):
        need_public, need_import, wrong_part = set(), set(), set()
        vis = visible(name)
        for (m, line), us in uses.items():
            if m != mod or line == 0 or (1 if line <= cut else 2) != p:
                continue
            for c, cm, private in us:
                if cm == mod:                       # within the original file
                    q = part(c)
                    if q == 1 and p == 2 and private:
                        need_public.add(c)
                    if q == 2 and p == 1:
                        wrong_part.add(c)
                    continue
                if cm in splits:                    # another split module
                    h = home(c)
                    if h not in vis and h != name:
                        need_import.add(f'{h} (for {c})')
                    if private:
                        need_public.add(c)
                    continue
                if private:
                    need_public.add(f'{c}  [{cm}]')
                elif cm not in vis and cm != name:
                    need_import.add(cm)
        print(f'\n== {name}')
        for label, s in (('make public', need_public), ('add import', need_import),
                         ('uses the second part', wrong_part)):
            for x in sorted(s):
                print(f'  {label}: {x}')

print('\n== other modules')
for m, cs in sorted(ext.items()):
    vis = visible(m)
    missing = sorted({home(c) for c in cs if part(c) and home(c) not in vis and home(c) != m})
    if missing:
        print(f'  {m}: add import {", ".join(missing)}  (uses e.g. {sorted(cs)[0]})')
