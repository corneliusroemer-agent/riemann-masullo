import re, sys
# Self time (node minus children above threshold) of trace.profiler nodes within one top-level block.
path, start = sys.argv[1], int(sys.argv[2])
top = int(sys.argv[3]) if len(sys.argv) > 3 else 15
node = re.compile(r'^( *)\[([\w.]+)\] \[([0-9.]+)\] \S+ ?(.*)')
lines = open(path, encoding='utf-8', errors='replace').read().split('\n')
nodes = []
for i in range(start - 1, len(lines)):
    l = lines[i]
    if i > start - 1 and l.startswith('['):
        break
    m = node.match(l)
    if m:
        nodes.append([len(m.group(1)), m.group(2), float(m.group(3)), m.group(4)[:110], i + 1])
selfs = []
for k, (d, cls, t, txt, ln) in enumerate(nodes):
    child = 0.0
    for d2, _, t2, _, _ in nodes[k + 1:]:
        if d2 <= d:
            break
        if d2 == d + 2:
            child += t2
    selfs.append((t - child, t, cls, txt, ln))
selfs.sort(reverse=True)
for s, t, cls, txt, ln in selfs[:top]:
    print(f'self {s:6.2f}s  total {t:6.2f}s  [{cls}] {txt}  (log line {ln})')
