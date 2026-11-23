import re, sys
# Top-level [Elab.command] / [Elab.async] trace nodes with times, labelled by declaration name.
pat = re.compile(r'^(\s*)\[(Elab\.command|Elab\.async)\] \[([0-9.]+)\]')
decl = re.compile(r'\b(theorem|lemma|def|instance|abbrev|noncomputable def|structure)\s+([^\s:({\[]+)')
lines = open(sys.argv[1], encoding='utf-8', errors='replace').read().split('\n')
rows = []
for i, l in enumerate(lines):
    m = pat.match(l)
    if not m or len(m.group(1)) > 0:
        continue
    name = '?'
    for j in range(i, min(i + 40, len(lines))):
        d = decl.search(lines[j])
        if d:
            name = d.group(2); break
    rows.append((float(m.group(3)), m.group(2), name))
rows.sort(reverse=True)
tot = sum(r[0] for r in rows)
print(f'{len(rows)} nodes >= threshold, sum {tot:.1f}s')
for t, k, n in rows[:int(sys.argv[2]) if len(sys.argv) > 2 else 15]:
    print(f'{t:7.1f}s  {k:13s} {n}')
