# Build-time profiling for riemann-masullo

Scripts and scratch-only Lean probes for finding out where the library's compile time goes. They were used for [mccorvie/riemann-masullo#6948](https://github.com/mccorvie/riemann-masullo/pull/6948), which names the subgroup behind `SIdeleQuotient` and cuts the compile time of the modules above `Ch03_IdelicZeta/Sec1` by 6.5%. Background: [#5398](https://github.com/mccorvie/riemann-masullo/issues/5398).

Copy `scripts/` and `lean/` into a checkout of the library (they are not part of it), and run everything from the repository root.

## Three traps

- **`lake env lean` ignores `[leanOptions]` from `lakefile.toml`.** Without `maxSynthPendingDepth = 3`, `Ch07_SchauderBasesZeta/Sec3b` does not even compile: 10 errors and 418 s, against 98 s with the options. `scripts/profile.sh` reads the options and passes them with `-D`.
- **Parallel elaboration misattributes time.** With `Elab.async` on (the default), a proof's time includes waiting for other proofs, and the profiler charges the wait to the next command. In Ch12 `Sec4` one `inferInstanceAs` term showed 20 s in one proof and 7 s in another, and under 0.3 s with `-DElab.async=false`. Profile with it off.
- **Tracing uses up heartbeats.** Heartbeats count allocations, and `trace.profiler` allocates, so an instance search close to its limit fails only under tracing (seen in Ch12 `Sec4`, a `BorelSpace` search at 20,000 heartbeats). An error that appears only when tracing is not a bug in the proof.

## Workflow

1. **Which declarations are slow:** `scripts/profile.sh <module.lean> out.log`, then `python3 scripts/top_declarations.py out.log 15`. The summary at the end of the log splits the time into elaboration, tactics, `simp`, type class inference and kernel checking.
2. **Which step inside a declaration:** `python3 scripts/self_time.py out.log <log line of the declaration's trace node> 10`. This lists the trace nodes with the most time of their own, not counting their children. A step with much self-time and no children did its work in code the tracer does not instrument (`kabstract` is one).
3. **Testing variants of one proof:** cut the module after the declaration and append variants, renamed (`scripts/scratch_copy.py`). Each run re-elaborates the kept prefix (for `Sec3b`, about 90 s), so test several variants per run.
4. **Goal size:** paste `lean/Probes.lean` into the scratch copy and call `probe_size`, `probe_gen` or `probe_blowup` inside the proof. A tree size far above the distinct-node count means `rw`, `obtain … := <term>`, `cases <term>` and `generalize` will be slow on that goal.
5. **Before/after over the library:** build `main` and the change from the same saved build, making both rebuild the same modules. The project uses the module system, so dependents rebuild only when a module's *public* interface changes: add the same public dummy `def` to the changed module on both sides. Build with `lake build -v`, then run `python3 scripts/compare_builds.py base.log change.log`.

## Finding: notation-inlined terms and `kabstract`

`kabstract` (Lean core, `Lean/Meta/KAbstract.lean`) walks a goal as a tree, without caching shared subterms. `rw`, `generalize`, and `obtain`/`rcases`/`cases` on a term that is not a local hypothesis all call it (the latter through `generalize`). In `sLocalGammaOrbitalQuotient_coeff_equiv` (Ch07 `Sec3b`) the goal has 1,362 distinct nodes but 388 million as a tree:

| on that goal | time |
|---|---|
| `kabstract` of any pattern, even one that never matches | 7.8 s (no candidate subterm at all) |
| `isTypeCorrect` of the same goal | 34–69 ms |
| `obtain ⟨x, hx⟩ := (⟨0, trivial⟩ : ∃ _ : ℕ, True)` | runs out of 600,000 heartbeats |
| `have h := …` then `obtain ⟨x, hx⟩ := h` | 0.055 s |

The cause was the local notation `projectedDiagonal` in `Ch03_IdelicZeta/Sec1`. The subgroup it stands for has about 190 distinct nodes. Spelled out in `SIdeleQuotient`, a copy sits in each instance argument (quotient group, topology, `SubgroupClass` and membership of `J₁(S)`), and these instances nest. `probe_blowup` shows the base terms (`Units.map`, `RingHom.comp`, `MonoidHom.range`, `Subgroup.map`, about 4,800 nodes as a tree) growing through `SubgroupClass.toSubmonoidClass` and `SetLike.instMembership` to 125,000 and then to the 388 million of the goal. With the subgroup named, as `abbrev sProjectedDiagonal`, these terms mention one constant.

An `abbrev`-size scan (`scripts/abbrev_sizes.sh` in the library) cannot see this, because `SIdeleQuotient`'s own body is small. The growth only appears in elaborated goals and instance terms.

Workarounds within a proof, when the definition cannot change: write `have h := term` and then `obtain … := h`, or use `.elim`/`.choose` instead of a case split. Both avoid `kabstract`.

## Files

- `scripts/profile.sh`: profile one module with the package options, parallel elaboration off.
- `scripts/top_declarations.py`: rank declarations in a profile log.
- `scripts/self_time.py`: self-time of the trace nodes under one declaration.
- `scripts/scratch_copy.py`: truncated copy of a module plus appended variants or probes.
- `scripts/compare_builds.py`: per-module comparison of two `lake build -v` logs.
- `lean/Probes.lean`: `probe_size`, `probe_gen`, `probe_blowup`. Scratch copies only: the library forbids new elaborators.
