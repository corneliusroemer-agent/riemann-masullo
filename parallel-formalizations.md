# 05 — Parallel and neighbouring formalizations: what a prover can reuse now

Scope: outside Lean work bearing on the open, free proof issues of `mccorvie/riemann-masullo`
(`$R/.agent/proof-issues.jsonl`, 106 free issues at the time of the snapshot). Repository contents
were read as data; nothing was built or run.

## Findings that change what a prover does next

1. **The local checkout `$R` is behind `main` on exactly the point that most refutation issues need.**
   `main` (71236071, 2026-11-23T08:36Z) vendors `RiemannMasullo/External/ZetaLab/`: Thomas Lince's
   `teal-sea/zeta-lab` (MIT, `a401821`) with 24 modules of Anthropic's Zeta23 ported to Lean 4.36. It
   provides `HardyTenZeros.ten_zeros_on_line_below_fifty` (ten ordinates `0 < t₀ < … < t₉ < 50`, each in a
   certified two-decimal box, `ζ(1/2 + tₖ i) = 0`), `HardyFirstZero.first_zero_on_line` (14.13, 14.14),
   `HardyTenZeros.zero_in_2102`, `RHHeight.rh_up_to_height_fiftytwo` (every zero with `0 < Re < 1`,
   `0 < Im ≤ 52` has `Re = 1/2` and order exactly 1), `RHHeight.zero_count_fifty`. The local `$R` has no
   `ZetaLab` directory. Existence of a (critical-line, simple, explicitly located) zeta zero is therefore no
   longer a blocker for #6242, #5337, #5319, #5414, #5321, #6147, #5523, #5818. **#6242 is a five-line
   proof** whose text a contributor already posted in the issue (verified against main: the `sorry` is
   still there at line 47 of `Ch10_TraceSpectral/Sec3_SpectralProof_Printed.lean`). Rebase on `main` first.
2. **`thatnealpatel/grh` has grown by 366 sorry-free Lean files since the vendored pin `e55aab2`**
   (HEAD `406476f`, 2026-11-23T06:01Z; 279 → 645 files, ~80k lines in `Proofs/`; same Lean `v4.36.0` and the
   same Mathlib rev `fc4f59e` as this project, so vendoring is copy + namespace rename, no proof
   adaptation). The most valuable new item: for **every number field K and every unitary Mathlib
   `HeckeCharacter (𝓞 K) K`**, `exists_completedHeckeEulerProduct_gaussianContinuation_horizontal_logDeriv`
   gives a meromorphic continuation of the completed Euler product with heights `T n ∈ (n, …)` on which
   `L ≠ 0` and `‖logDeriv L‖ ≤ D (1+T n)²` for `-1 ≤ σ ≤ 2`; `completedHecke_rightLine_nonzero_logDeriv_bound`
   gives the linear bound on any line `Re s = a > 1`. Together with this project's
   `completedHeckeL_continuation_functionalEquation` and the already vendored
   `completed_logDeriv_reflection`, that is the whole analytic content of **#3880**
   (`hasSlowGrowthNearPoles_completedHeckeL_logDeriv`), whose last release note says exactly this estimate
   was missing. Remaining work is a bridge `completedHeckeL χ` ↔ `completedHeckeEulerProduct`
   (gamma-factor parameter choices, `ideleClassNormTwist χ 0` as a Mathlib Hecke character) and the
   identity theorem for the `MeromorphicNFOn` witness. Import closure to vendor: ~194 grh modules, ~22k lines.
3. **"The Anthropic proof" is two things, "the OpenAI proof" is one, and none supplies Masullo-shaped
   lemmas directly.** (a) Alpöge–Furman, *More than two thirds of the zeta zeros are simple and on the
   critical line* (arXiv:2608.13637, Aug 2026), Lean by Claude in `anthropics/formal-math/zeta23`
   (Apache-2.0); a slice is already in `main` via ZetaLab. (b) Levent Alpöge's 20 Nov 2026 announcement
   (`alpo.ge/remark.pdf`) of a proof of RH and of GRH for Dirichlet L-functions, found "working with
   Claude", published only as a Lean tarball, **without a licence**; mirrored at
   `Deicyde/riemann-hypothesis`, now `leanprover-community/riemann-hypothesis` (149k Lean files, ~20.8M
   lines, Lean v4.37.0-rc1). This project's Comparator setup copies it; the statements match this repo's RH
   and Dirichlet endpoints; nothing may be copied. (c) OpenAI's *Quasi-Riemann Hypothesis* (`openai/math`,
   family 003, Apache-2.0, Lean 4.34.1; `Re s > 7/8` zero-free for ζ and all Dirichlet L, and for
   finite-order Hecke characters over ℚ(√−3)); HEAD is still the commit the project's survey pins (`4eaee87`).
4. **What Zeta23 has that `main` has not yet taken**: Theorem B (`two_thirds_simple_on_critical_line`,
   positive proportion of simple critical-line zeros) plus the Riemann–von Mangoldt formula gives
   infinitely many simple critical-line zeros with gaps tending to zero by pigeonhole, which is the input
   of **#5231** (`Printed.spectralLineJet_uniformBiorthogonalBound_false`); ten certified zeros cannot
   give it. Cost: ~117 modules / ~40k lines from Lean 4.33.0-rc2; `main` already carries 24 of the needed modules (Stirling, GammaFacts, parts of RvM such as Backlund, CountByIntegral and MainTerm excerpts, WeilEF/XiLogDeriv), but not `RvM/Statement` or the Theorem A–B machinery.
   Zeta23 also proves Weil's explicit formula for ζ and for primitive Dirichlet L-functions, good heights,
   Stirling for Γ′/Γ on vertical lines and Landau's lemma, all sorry-free (README and file headers; the
   headline proofs were read only at the statement level).

## What each effort is

- **`thatnealpatel/grh`** — <https://github.com/thatnealpatel/grh>, MIT (© 2026 Neal Patel), Lean
  v4.36.0, Mathlib `fc4f59e` (identical to this project). HEAD `406476f` (2026-11-23T06:01Z); 587 commits
  since the vendored `e55aab2` (2026-11-22T06:11Z), i.e. in one day. `Proofs/{Lemmas,Props,Theorems}`:
  645 Lean files (366 new since the pin), ~80k lines, no `sorry`, no `axiom` (grep). Produced by an
  autonomous agent harness ("patel.codes/godel"); `Proofs/{Props,Theorems}` is meant as the human
  review surface; `.godel/` holds agent notes. Mostly over ℚ, with a growing all-field layer for unitary
  Mathlib `HeckeCharacter`s: completed Euler products, continuation via a Gaussian theta, good heights,
  log-derivative bounds, the trivial-character functional equation for every K, explicit formulas
  (ζ; trivial Hecke over K), idele-class Haar measure and fundamental domains, weighted radial Schwartz
  stages, entire jet interpolation, Hilbert-space trace lemmas. This project vendors 8 files of it at
  `e55aab2` (`External/Grh`, imported by nothing outside `External/` in the local checkout) and has
  adapted proofs from it (`ATTRIBUTION.md`).
- **ZetaLab (in this project's `main`)** — `teal-sea/zeta-lab` @ `a401821` (MIT; Thomas Lince;
  "makes no claim to have proved RH"), with Zeta23 modules @ `3635e74`. Certified low zeros of ζ
  (ten zeros below 50 in two-decimal boxes) and RH with simplicity to height 52. Brought in by #6225
  after the local checkout was taken.
- **Zeta23, Anthropic** — <https://github.com/anthropics/formal-math/tree/main/zeta23> (README also
  points to `anthropics/zeta-23-lean`), Apache-2.0, Lean v4.33.0-rc2, Mathlib `51e6992`; HEAD of
  `formal-math` `16a5ce4` (2026-10-26). 326 Lean files, ~102k lines in `Zeta23/`, sorry-free and
  Comparator-checked per README (not re-checked here). Formalizes Alpöge–Furman, *More than two thirds
  of the zeta zeros are simple and on the critical line* (arXiv:2608.13637; result announced by
  Anthropic in August 2026; "All Lean code was written by Claude"). Seventeen headline theorems
  (Theorems A–E, also for primitive Dirichlet L), plus Weil's explicit formula, Riemann–von Mangoldt,
  Stirling for Γ′/Γ, Chebyshev–Mertens, Montgomery–Vaughan, Hardy Z. This is the "Anthropic proof"
  in the sense of a peer-reviewable, licensed, Lean-checked result.
- **Alpöge's RH announcement / `Deicyde/riemann-hypothesis`** — the GitHub name now resolves to
  <https://github.com/leanprover-community/riemann-hypothesis> (HEAD `9c9f665`, 2026-11-23). It is a
  community-maintained mirror and clean-up of the Lean tarball that Levent Alpöge published with
  `alpo.ge/remark.pdf` (20 Nov 2026), in which he writes that he has, "working with Claude", found and
  formalized a proof of RH and of GRH for Dirichlet L-functions (Extended RH "with more time"); the
  method is described as Stepanov-type multiplicity via chains of theta lifts between unitary groups.
  Main theorems (`src/Main.lean`): `riemannHypothesis`, `riemannZeta_eq_zero_re`,
  `LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, `LFunction_eq_zero_re_of_isPrimitive`;
  a second Comparator setup against formal-conjectures' RH/GRH statements. Lean v4.37.0-rc1; 149,231
  Lean files, ~20.8M lines (`src/Development` alone 121k files: automorphic spectrum, étale cohomology,
  abelian varieties, resolution of singularities, Weil bound). **No licence** ("published without a
  license… mirrored here so that it can be checked"; the original is preserved on branch `original`,
  commit `40e56bab`). Andrew Sutherland reports a build, axiom audit and kernel replay (per this
  project's `survey/prior-formalizations.md`, not re-checked). Its supporting library is algebraic and
  automorphic (theta lifts, Galois cohomology, valuations, linear algebra in `Lemmata/`), not the
  distributional and functional analysis Masullo's chapters need, and it cannot be copied in any case.
- **OpenAI, *The Quasi-Riemann Hypothesis*** — <https://github.com/openai/math>, family 003, Apache-2.0,
  Lean 4.34.1. HEAD `4eaee87` (2026-10-29) is the commit this project's survey already pins, so there is
  nothing new. `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`,
  `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`, and the ℚ(√−3) Hecke family
  (statements per the survey; the folder `lean/OAI/NumberTheory/DirichletL/` with Continuation*,
  GaussianTheta, IdealLogDerivative, Reflection, Mellin, Poisson subfolders exists at HEAD). This is
  the "OpenAI proof about some Riemann thing".
- **Masullo audits** — `dvgyl/masullo-grh-proof-audit` (`6bef19b`, 2026-11-21), `enaslund/rh-verification`
  (`f7d53ba`, 2026-11-20), `ityonemo/music-of-primes` (`68da2f4`, 2026-11-22): prose, TeX, Python checks and
  `2b4m` (Zig) encodings; no Lean, no licence files.
- **Prove2Me** — four statements proved by dga471, already merged here (#3615).
- **SURVEY projects** — no new commits on the default branches of `hecke-seven-eighths`,
  `DedekindZetaZeroFree`, `AINTLIB`, `gaussian-field`, `ideles-journal` since their pins; the two
  `jonhanke` repositories were not reachable.

## Reusable declarations mapped to open issues

"V" = I opened the outside file and read the declaration; "S" = statement taken from a README or a
contributor's comment only. grh = `thatnealpatel/grh` @ `406476fb992c46186be177448fc3315eb2489236`
(MIT, Lean v4.36.0, Mathlib `fc4f59e`, identical to this project). ZetaLab = already in this project's
`main` under `RiemannMasullo/External/ZetaLab/` (MIT + Apache-2.0 notices). Zeta23 =
`anthropics/formal-math` @ `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`, `zeta23/` (Apache-2.0, Lean
v4.33.0-rc2, Mathlib `51e6992`; README links it as `anthropics/zeta-23-lean`, pinned by ZetaLab at `3635e74`).

| Issue | Declaration needed | Outside declaration | Src | What porting involves |
|---|---|---|---|---|
| #6242 `spectralLineSelection_three_zeta_zeros` (refutation helper) | three ordered critical-line zeros | ZetaLab `HardyTenZeros.ten_zeros_on_line_below_fifty : ∃ ts : Fin 10 → ℝ, StrictMono ts ∧ ∀ k, 0 < ts k ∧ ts k < 50 ∧ riemannZeta (1/2 + ts k * I) = 0` | V (main, file `ZetaLab/HardyTenZeros/TenZeros.lean`) | None: rebase on main, import `RiemannMasullo.External.ZetaLab.HardyTenZeros.TenZeros`; proof text is in the issue's second comment (obtain, `StrictMono` at `0<1`, `1<2`, `push_cast`). Grade A. |
| #5337 `Printed.spectralLineIsotype_bandAdjoint_contains_jets_false` | zeros at t = 14.1347…, u = 21.0220… | ZetaLab `HardyFirstZero.first_zero_on_line` (t ∈ (14.13, 14.14)), `HardyTenZeros.zero_in_2102` (u ∈ (21.02, 21.03)); `RHHeight.rh_up_to_height_fiftytwo` for simplicity | V (main) / S (box statements from the issue comment on #6242) | None for the zeros; the refutation's analytic part (dual inner product `Mπ exp(−|t−u|)`) is separate work. |
| #5319 `Printed.spectralLineKernel_extraWeight_false` | "abscissa of the first positive-ordinate zero" | ZetaLab `RHHeight.rh_up_to_height_fiftytwo : RHUpToHeight 52` + `first_zero_on_line` (so the abscissa is 1/2 and the first ordinate is in (14.13,14.14)); `RHHeight.zero_count_fifty` gives finiteness for "first" | V (main) | None for the zero; the minimum over a finite set via `zero_count_fifty`. |
| #5414, #5321, #6147, #5523, #5818 (refutations needing some zero `a + iγ`, `γ > 0`, mostly on the line) | existence of a nontrivial / critical-line zero | same ZetaLab theorems | V (main) | None for the zero. |
| #5231 `Printed.spectralLineJet_uniformBiorthogonalBound_false` | simple critical-line zeros with ordinate gaps → 0 | Zeta23 `two_thirds_simple_on_critical_line : ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (2/3 − ε) * Ncount T (2T) ≤ N0simple T (2T)` (`Challenge.lean`, proved in `Solution.lean` via `Zeta23.thmB₀_mult`) + `Zeta23.riemannVonMangoldt_zeta : RiemannVonMangoldt zetaZeroConfig` (`Zeta23/Final.lean:235`; `main`: `\|N(T,2T) − (T/2π)ℓ₁(T)\| ≤ C log T`) | V (statements, file locations) | Port ~117 modules (Lean 4.33-rc2 → 4.36), then pigeonhole: ≥ c·T log T simple on-line zeros in (T, 2T] force a gap ≤ T/(k−1) → 0. Large; only worth it if #5231 matters. |
| #3880 `hasSlowGrowthNearPoles_completedHeckeL_logDeriv` | heights with polynomial log-derivative bounds on horizontals, bounds on two interior vertical lines, for completed Hecke L of every unitary χ over every F | grh `Masullo.exists_completedHeckeEulerProduct_gaussianContinuation_horizontal_logDeriv (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ a : C, ‖χ a‖ = 1) (v) (r) (hr)` → ∃ λ L H, … `∀ s, 1 < s.re → L s = completedHeckeEulerProduct χ hχ s` … `∃ D > 0, ∃ T : ℕ → ℝ, (∀ n, n < T n ∧ \|λ\|+1 < T n) ∧ ∀ n σ, -1 ≤ σ → σ ≤ 2 → L(σ ± i T n) ≠ 0 ∧ ‖logDeriv L (σ ± i T n)‖ ≤ D (1 + T n)^2` (`Proofs/Theorems/IdeleClassGaussianHorizontalLogDeriv.lean:90`); grh `completedHecke_rightLine_nonzero_logDeriv_bound` (`Proofs/Theorems/CompletedHeckeRightLineGrowth.lean:30`): for `1 < a`, `∃ C > 0, ∀ t, L(a+it) ≠ 0 ∧ ‖logDeriv L (a+it)‖ ≤ C (1+\|t\|)`; the section `r` is discharged in grh by `ideleIdealClass_normOne_surjective` | V | Vendor the closure (194 modules, ~22k lines; mechanical, same pin). Write the bridge `completedHeckeL χ s = completedHeckeEulerProduct χ' hχ' s` on `Re s > 1` (compare `heckeGammaFactor`'s chosen parameters with grh's `localHeckeGammaFactor`). Left vertical line from `completedHeckeL_continuation_functionalEquation` + vendored `completed_logDeriv_reflection`; trivial-χ model of that step: grh `completedHecke_one_leftLine_nonzero_logDeriv_bound` (`Theorems/CompletedHeckeOneReflection.lean:211`). Transfer to the issue's `L` by the identity theorem. Grade B (a day, not hours). A `Claiming` comment by another contributor was the last activity, without the label. |
| #6235 `archimedeanWeightedSchwartz_metrizable`, #6236 `…_complete` | metrizability and completeness of the weighted space `𝓦(I)` | grh `logWeightedStage_seminorm_le_endpoints` (interpolation of an intermediate weight by the two endpoint weights, with binomial derivative terms), `exists_countable_logWeightedStage_closedEmbedding`, `metrizableSpace_logWeightedStage`, `completeSpace_logWeightedStage` (`Proofs/Theorems/RadialWeightedSchwartzFrechet.lean:83,181,199`, `RadialWeightedSchwartzStage.lean:148`) | V | Template, not a drop-in: grh's stage is one real variable in log coordinates; `𝓦(I)` is a product of real and complex places with per-coordinate exponents. The countable-bracketing + closed-embedding-into-a-countable-product proof pattern transfers. 3 modules, 478 lines. Grade B. |
| #4771 `sLocalGamma_all_coeff_surjective`, #4768 `sLocalGammaFiltration_coeff_independent`, #5149 `strongCoprimality_bezout` | prescribed Laurent/Taylor jets at a discrete set; divisibility by an entire function via jets | grh `entireDivisorJet_surjective (hg : AnalyticOnNhd ℂ g univ) (hg₀ : g ≠ 0) : Surjective (f ↦ entireDivisorJet (g := g) f.val)` (`Proofs/Lemmas/EntireDivisorInterpolation.lean:235`); `entire_mul_iff_vanishing_jets : (∃ q entire, f = g * q) ↔ ∀ z, g z = 0 → ∀ k < ord_z g, iteratedDeriv k f z = 0` (`Proofs/Lemmas/EntireDivisorDivision.lean:22`); `entireDivisorJet_eq_zero_iff` | V | Ingredient only: no growth control on the interpolant, while the issue spaces are Schwartz–Bergman. 3 modules, 455 lines, standalone. |
| #5523 `Printed.absolutePWCondensation_trace_tendsto_false` (rank-one idempotent with trace near one), Ch07 §4 nuclearity traces (#5083, #5089, #5107) | trace of a sum of rank-one operators; quotient by closed range in a Hilbert space | grh `OperatorTrace.hasSum_diagonal` (`Proofs/Props/HilbertRankOneTrace.lean:19`: for `T x = ∑ rankOne (u n) (v n) x` with `∑ ‖u n‖‖v n‖ < ∞`, the diagonal sum over any Hilbert basis is `∑ ⟪v n, u n⟫`); `ker_hilbertQuotientProjection`, `norm_hilbertQuotientProjection`, `exists_denseEmbedding_quotient_rangeClosure` (`Proofs/Lemmas/HilbertDenseQuotient.lean`) | V | Small, standalone; copy with namespace change. |
| #5679 `Printed.introTraceApprox_spectral_limit_false`, #5680 `…_primeSum_tendsto_false` (explicit formula at 2 for the trivial rational character) | Weil explicit formula for ζ with compactly supported tests | grh `completedZeta_explicit_formula (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)` (`Proofs/Theorems/RationalExplicitFormula.lean:23`, present since `e55aab2`); Zeta23 `WeilEF/*` (ζ and primitive Dirichlet) | V (grh statement head) / S (Zeta23) | grh version: same pin, vendor. The tests in the issues are not compactly supported in all variables; check fit before porting. |
| #4871 `globalPolarFreeTheta_directionallySmooth` ((10.1.1.1)) | weighted polar-free theta functions | grh `Theorems/RationalThetaRadialCore.lean` (ℚ, trivial isotype only) | V | ℚ-only model; useful as a sanity check, not as a proof over general F. |
| #6239 `globalThetaSobolev_isotype_le_closure_absLevel` (11.2.1.2(1), 7.3.2.2(1)) | band density in weighted theta closures | grh `rationalThetaWeightedLog_band_closure`, `tendsto_rationalThetaWeightedEvenBand_projection` (`Proofs/Theorems/RationalThetaBandClosure.lean:31,51`, ℚ, even model) | V | ℚ-only; check whether the issue's F can be specialised; otherwise a model. |

For the even quadratic character mod 5 of #5199 (`Printed.sLocalCarvingLimit_eq_rawClosedSpan_false`)
and #5150 (`Printed.strongCoprimality_false`), grh has the Dirichlet side only: `dirichletFive :
DirichletCharacter ℂ 5 := (quadraticChar (ZMod 5)).ringHomComp (Int.castRingHom ℂ)`
(`Proofs/Theorems/HeckeDirichletFactorization.lean:126`) with `dirichletFive_even`,
`dirichletFive_primitive`, `dirichletFive_ne_one` (`Proofs/Lemmas/NegFiveDirichletCharacters.lean:18,42`,
`HeckeDirichletFactorization.lean:139`) (V). These are short `decide` proofs; the issues need the
corresponding idele class character, which grh does not construct. No outside source was found for the
ℚ(√−7) witness of #5516, the splitting field of X³−2 of #4990, or a prime ideal theorem over a number
field as used by #5615. grh's other explicit fields are ℚ(√−5) (`NegFive*`, `QSqrtNegFive*`,
`IdealClassPrime{Two,Five}Factor`) and characters mod 3 and 4 (`DirichletThree*`, `dirichletNegFour`).

## Standalone statements worth borrowing as targets or sanity checks

- `RHHeight.RHUpToHeight 52` (on main): any refutation that picks "the first zero" or "a zero with
  ordinate below 50" can fix it as `1/2 + i t` with `t` in a certified box and simple; use it to check that
  a counterexample's numerics (e.g. #5337's `Mπ exp(−|t − u|) ≠ 0`) are consistent before writing them.
- Zeta23's counting definitions (`Ncount`, `N0star`, `N0simple`, `zerosIn` in `ChallengeDeps.lean`) are
  Mathlib-only and audited by a paper author; reuse them verbatim when a Masullo statement needs "the
  zeros up to height T" so that a later port of Zeta23 lemmas lines up by name.
- grh `Props/ZetaTestSumComparison.lean` (present since `e55aab2`): `zetaZero_in_closedStrip_of_test_agreement`,
  `riemannHypothesis_of_strip_test_agreement`, `zetaZero_on_criticalLine_and_simple_of_test_sum_eq`. These
  show in Lean that agreement of the spectral sums of (10.3.2.3–4) or (13.3.1.1–3) with the full zero sum
  would imply RH (and simplicity). They are a ready-made check on any repaired Chapter 10/13 statement:
  if a repaired statement plus a proved lemma yields the hypothesis of one of these, it is too strong.
- grh `completedHecke_one_reflection` (every number field, trivial character): the functional equation in
  germ form `L(1−s) = exp(δ(s − 1/2)) L(s)` with `δ = log |disc K|`. A cross-check on this project's
  `completedHeckeL_continuation_functionalEquation` normalisations at χ = 1.
- Deicyde / leanprover-community `src/Challenge.lean` (statements only, unlicensed): the five RH and
  Dirichlet-GRH statements that this project's `Statements.lean` already matches; Comparator target names.
- OpenAI 7/8 and Hu 7/8 (unchanged since the survey): zero-free half-planes are sanity bounds for any
  printed zero-location step in Appendix B.6 or Chapter 13.

## Dead ends

- `dvgyl/masullo-grh-proof-audit` (HEAD `6bef19b`, 2026-11-21), `enaslund/rh-verification` (`f7d53ba`,
  2026-11-20), `ityonemo/music-of-primes` (`68da2f4`, 2026-11-22): no Lean at all, and no licence file
  in any of them. The `.b4m` files are for Yonemoto's own Zig checker `2b4m`, not Lean. They contain
  prose witnesses that agree with this project's refutation docstrings (e.g. ℚ(√5) volume
  `2 log φ/√5` for Thm 12.5.1.1, the Q₈ field of Martinet for Thm 10.3.1.1(2), the S₃ splitting field of
  X³−2 for Thm 10.2.1.1, the CM curve `y² = x³ − 1254² x` over ℚ(i) for Ch. 13, prime-2 shells for
  Thm 11.3.2.1, ℚ(i) with the split prime 5 for §11.3.1.1) and a few Python exact-arithmetic checks
  (`dvgyl/checks/*.py`, not run). Useful as cross-checks of witnesses, not as code. None of them has a
  three-zero spectral-line selection or explicit zero ordinates.
- Prove2Me: the four dga471 proofs (`elementarySchwartz_withSeminorms_P2/P3/_sum`,
  `rapidDecaySequence_isFrechet`) are already merged (#3615, recorded in `ATTRIBUTION.md`); nothing further
  was found.
- SURVEY projects since their pins: `hecke-seven-eighths` (`c77efa9`), `DedekindZetaZeroFree`
  (`09afbb4`), `AINTLIB` (`c3bc9bf`), `gaussian-field` (`1283a27`), `ideles-journal` (`fe49f52`) have no
  new commits on their default branches. `jonhanke/algebraic-number-theory-lean` and
  `jonhanke/quadratic-forms-lean` return 404 to this session's GitHub credential and were not checked
  (an account-visible `jonhanke/quadratic_forms_in_lean` exists under a different name).
- Hardy's theorem as such (infinitely many critical-line zeros by the Hardy Z sign argument) is not
  formalized anywhere I found apart from Zeta23's much stronger proportion theorem; grh takes
  `Infinite criticalStripZetaZeros` as a hypothesis (`rationalMellinDivisorJet_ne_one`).
- Alpöge's RH development: unlicensed and enormous (~20.8M lines, Lean v4.37.0-rc1); nothing can be copied
  and nothing is small enough to be worth reading for a single proof issue here.

## Verified vs search-result claims

Verified by opening the source: every grh declaration in the table (statements read at `406476f`), the
ZetaLab declarations on `main` (files fetched through the GitHub API), the Zeta23 Challenge statements,
`Solution.lean` delegation names and `riemannVonMangoldt_zeta` location, the Deicyde README, licence text
and `Main.lean` theorem list, `alpo.ge/remark.pdf` (text extracted), the OpenAI HEAD commit and folder
listing, and the absence of Lean/licences in the three audits (by a helper; spot-checked by file count).
Taken from READMEs or search results only: that Zeta23 and the Deicyde mirror pass Comparator and are
axiom-clean; Sutherland's audit; the August 2026 Anthropic announcement and the 41.6% → 67.2% framing;
the OpenAI statements' exact forms (from the project's own survey); Lince's 67.28% update.

## Reusable

- `notes/free_stmts.md`: statement + docstring of every free proof issue (generated by
  `scripts/stmts.py` from `$R/.agent/proof-issues.jsonl`; 8 newest issues are not in the stale checkout).
- `scripts/closure.py <root> <Module>...`: import-closure size of a Lean module inside a cloned
  project (module and line counts), used for porting estimates.
- `notes/grh_lean_added.txt`: the 366 grh Lean files added since `e55aab2`; `notes/grh_old_lean.txt`
  the 279 at the pin. Recompute with `gh api repos/thatnealpatel/grh/git/trees/<sha>?recursive=1`
  (the compare API truncates at 300 files, all of them `.godel/` notes here).
- grh docstrings cite Masullo item numbers; `grep -rnoE "\b(B\.4\.2|10\.3\.1|…)" Proofs` maps
  files to paper items quickly (done once above; B.4.2.x and 11.x/12.x dominate).
- `notes/main_external_tree.txt`: the `External/` tree on `main` at `7123607`.
- Clones (shallow, untrusted, never built): `clones/{grh,zeta23,deicyde-rh,openai-math,dvgyl,enaslund,ityonemo}`
  and `clones/alpoge-remark/remark.txt`.
- Rule of thumb for this project: check `main` (not the local checkout) and the latest comments of an
  issue before treating an ingredient as missing; contributors post ports and proof text in comments.
