# Build-time profiling for riemann-masullo

Scripts and scratch-only Lean probes for finding out where the library's compile time goes. They found the terms named in [mccorvie/riemann-masullo#6995](https://github.com/mccorvie/riemann-masullo/pull/6995), which cut the compile time of the 119 modules above `Ch03_IdelicZeta/Sec1` by 18% (wall clock 23%). The statement measurement went into the PR check as [#6996](https://github.com/mccorvie/riemann-masullo/pull/6996). Background: [#5398](https://github.com/mccorvie/riemann-masullo/issues/5398).

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

## Statement scan: finding the next family

`scripts/scan_statements.sh lean/StatementSizes.lean` measures every public statement of a built library (about 35 s). It prints the statements of 10⁶ tree nodes or more, and the subterm heads that recur most among them. Then:
- `lean/StatementBlowup.lean` lists, for chosen statements, the subterms with the largest multiplicity × tree size.
- `lean/ShowDominant.lean` pretty-prints the top one, whatever its head.

The largest hits on `main` at 2ffae66 fell into three families, all named in #6995:

| family | example statement | distinct | as a tree | named |
|---|---|---|---|---|
| the projected-diagonal subgroup of `SIdeleQuotient`, up to 2·10⁸ copies | `sLocalThetaSobolev_isotypeDecomposition` (Ch10 Sec1) | 20,263 | 3.2·10¹³ | `sProjectedDiagonal` |
| the weighted measure of `CompactIntervalSobolev` with the `logNorm` lambda, 4.2·10⁶ copies | `primeOrbitalSobolevConvolution_traceNorm_continuous` (Ch11 Sec2b) | 7,430 | 2·10¹¹ | `intervalSobolevMeasure`, `logIdeleClassNorm` |
| the diagonal embedding of the S-units, written out through `unitAtS`-style notations in Chapters 2, 3, 5, 7 and 12 | `sLocalGammaOrbitalQuotient_coeff_equiv` (Ch07 Sec3b) | | | `sUnitEmbedding` |

The fix is the same for all three: name the repeated term with an `abbrev`, and point the notations at the name. Instance arguments then mention one constant. Proofs that unfolded the term with `simp`, `dsimp` or `rw` need the name added to their simp set (21 proofs in #6995).

Naming pays when it removes copies of a large term from statements whose copies are counted in the millions. It pays little when the count stays and only each copy shrinks. Naming the continuous idele norm `⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩` (11 `m𝔽` notations, 69 spellings in 30 files) made the largest statements on top of #6995 three times smaller, but saved only 1.9% of build time, nearly all of it in `Ch11_ShellStructure/Sec2b`. Measure before opening such a change: the copy counts come from instances nested over `abbrev` quotient types, and only turning those into `def`s (#5398) reduces them.

## Files

- `scripts/profile.sh`: profile one module with the package options, parallel elaboration off.
- `scripts/top_declarations.py`: rank declarations in a profile log.
- `scripts/self_time.py`: self-time of the trace nodes under one declaration.
- `scripts/scratch_copy.py`: truncated copy of a module plus appended variants or probes.
- `scripts/compare_builds.py`: per-module comparison of two `lake build -v` logs.
- `lean/Probes.lean`: `probe_size`, `probe_gen`, `probe_blowup`. Scratch copies only: the library forbids new elaborators.
- `scripts/scan_statements.sh`: runs a statement scan over the whole built library, generating the imports.
- `lean/StatementSizes.lean`: every public statement's size, and the recurring subterm heads.
- `lean/StatementBlowup.lean`: for chosen statements, the subterms that account for their size.
- `lean/ShowSubterm.lean`: pretty-prints the dominant subterm with a given head.
