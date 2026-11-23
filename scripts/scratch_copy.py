"""Make a scratch copy of a module that stops after one declaration, with extra text appended.

    python3 scripts/scratch_copy.py MODULE.lean LAST_LINE TAIL.lean OUT.lean

Keeps lines 1..LAST_LINE of MODULE (end the cut after a complete declaration), then appends
TAIL, which must close the open sections and namespaces (`end Foo`). Use it to time variants of
one proof, or to run the probes in `lean/Probes.lean` inside the declaration's context, without
editing the module: `lake env lean` the copy with the options from `scripts/profile.sh`.
Every run re-elaborates the kept prefix, so cut as early as the target allows.
"""
import sys

src, last, tail, out = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4]
lines = open(src, encoding='utf-8').read().split('\n')[:last]
extra = open(tail, encoding='utf-8').read()
open(out, 'w', encoding='utf-8').write('\n'.join(lines) + '\n' + extra)
print(f'wrote {out}: {last} lines of {src} + {tail}')
