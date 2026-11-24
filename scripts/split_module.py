"""Split a section file in two after a top-level `end <Section>` line.

    python3 split_module.py <file> <cut line> <new first-part module> <new first-part docstring title>

The first part becomes a new file next to the original; the original keeps its module name and
the rest, and imports the first part publicly, so modules that import it see everything as
before. The new file gets the original imports with `import all` turned into plain `import`
(AGENTS.md: no new `import all`). The second part repeats the directives that are in force at
the cut: top-level `open`, `set_option`, `variable`, `universe` and `local notation` lines.
"""
import re
import sys
from pathlib import Path

path, cut, first_mod, title = Path(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
lines = path.read_text(encoding='utf-8').split('\n')
assert lines[0] == 'module'
header_end = next(i for i, l in enumerate(lines) if l.startswith('@[expose] public noncomputable section'))
doc_start = next(i for i, l in enumerate(lines) if l.startswith('/-!'))
imports = lines[1:doc_start]
doc = lines[doc_start:header_end]
assert re.match(r'^end \w+', lines[cut - 1]), lines[cut - 1]

# directives at depth 0 (inside `namespace RiemannMasullo` only) between the header and the cut
stack, carried, i = [], [], header_end + 1
while i < cut:
    l = lines[i]
    m = re.match(r'^(section|namespace|noncomputable section)\b\s*(\S*)', l)
    if m:
        stack.append(m.group(2))
    elif re.match(r'^end\b', l) and stack:
        stack.pop()
    elif stack in ([], ['RiemannMasullo']) and re.match(r'^(open|set_option|variable|universe|local notation)\b', l) \
            and not l.rstrip().endswith(' in'):
        block = [l]
        while i + 1 < cut and lines[i + 1].startswith((' ', '\t')) and lines[i + 1].strip():
            i += 1
            block.append(lines[i])
        carried.extend(block)
    i += 1
assert stack == ['RiemannMasullo'], stack

# top-level `local instance <name>` of the first part: the second part switches them on again
stack, local_insts = [], []
for l in lines[header_end + 1:cut]:
    m = re.match(r'^(section|namespace|noncomputable section)\b\s*(\S*)', l)
    if m:
        stack.append(m.group(2))
    elif re.match(r'^end\b', l) and stack:
        stack.pop()
    elif stack in ([], ['RiemannMasullo']):
        mi = re.match(r'^(?:@\[[^\]]*\]\s*)?local instance\s+([^\s:({\[]+)', l)
        if mi:
            local_insts.append(mi.group(1))
if local_insts:
    carried.append('attribute [local instance] ' + ' '.join(local_insts))

first_imports = [re.sub(r'^import all ', 'import ', l) for l in imports]
first_doc = [f'/-! # {title}', '', f'The first part of `{".".join(path.with_suffix("").parts)}`, split off so that modules',
             'that need only these declarations do not wait for the rest of that file.', '-/']
first = (['module'] + first_imports + first_doc + [''] + lines[header_end:cut] + ['', 'end RiemannMasullo', ''])
second = (['module', '', f'public import {first_mod}'] + imports + doc + [lines[header_end], ''] +
          ['namespace RiemannMasullo', ''] + carried + [''] + lines[cut:])
# the carried block already contains `namespace RiemannMasullo`? It cannot: that line is not depth 0.
first_path = path.with_name(first_mod.rsplit('.', 1)[1] + '.lean')
first_path.write_text('\n'.join(first), encoding='utf-8')
path.write_text('\n'.join(second), encoding='utf-8')
print(f'{first_path}: {len(first)} lines; {path}: {len(second)} lines; carried {len(carried)} directive lines')
