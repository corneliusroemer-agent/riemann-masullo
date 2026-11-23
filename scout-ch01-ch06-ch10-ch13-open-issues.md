# Scout 03: misc files (Ch01 Sec4, Ch06 Sec2/Sec3, Ch10 Sec1/Sec3, Ch11 Sec1b/Sec2b/Sec3/Sec3_Printed, Ch12 Sec4, Ch13 Sec3, AppB Sec4b)

Repo: mccorvie/riemann-masullo. All 37 assigned issues were open with no `claimed`/`stuck`/`gap`/`blocked`
label at 07:02 UTC on 2026-11-23 (live `gh`); the four top candidates were rechecked at 07:15 UTC.
Nothing was compiled; grades come from reading the files, the issue threads and closed PRs.

## Top picks

### 1. #4297 `sLocalThetaIsotypeSum_complete` (Ch06_LocalGlobal/Sec2.lean:353) — grade A

Statement: the locally convex direct sum of the S-local isotypes `Eₛ(χ)` is Hausdorff, polynormable and
complete for every compatible uniform structure.

Why it is easy now:
- The global twin `globalThetaIsotypeSum_complete` (Sec2.lean:506-543) is proved on `main` (PR #5920, merged
  02:43 UTC). Its four abstract private helpers sit in the same file:
  `globalThetaIsotypeSum_finalTopology_withSeminorms` (:363), `globalThetaIsotypeSum_continuous_lcDirectSum_component`
  (:397), `globalThetaIsotypeSum_completeSpace_lcDirectSum` (:416), `globalThetaIsotypeSum_uniform_eq` (:498).
- A complete proof of the local statement exists in closed PR #5915 (built, lint and signature check passed
  per its description). It was closed at 05:56 UTC only because of a merge conflict (imports plus content) left
  unresolved for four hours; the merger released the issue and wrote "a revised PR against current main would
  be welcome". That proof used `import all AppC_LCTVS.Sec2a_part2`, which is now forbidden and no longer needed.
  Diff saved at `03-scout-misc/pr5915.diff`.
- The earlier `Releasing` note says the attempt failed only its own "no sorryAx" check; `prompts/prover.md`
  accepts inherited `sorryAx` (here from `sLocalAdelicThetaSpace_strictLF` and `existsUnique_sLocalThetaAction`).

Proof (mirror of lines 514-543, not compiled):
```lean
  classical
  let : T2Space (Θₛ(S)) := sLocalAdelicThetaSpace_t2_of_isClosed
    (sLocalAdelicTheta_ker_isClosed (F := F) (S := S))
  let : PolynormableSpace ℂ (Θₛ(S)) := sLocalAdelicThetaSpace_polynormable
  let : IsTopologicalAddGroup (Θₛ(S)) := PolynormableSpace.isTopologicalAddGroup ℂ _
  let : ContinuousSMul ℂ (Θₛ(S)) := PolynormableSpace.continuousSMul ℂ _
  let : UniformSpace (Θₛ(S)) := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup (Θₛ(S)) := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace (Θₛ(S)) := sLocalAdelicThetaSpace_complete
  let X := fun χ : PontryaginDual J₁(S) ↦ ↥(Eₛ(χ))
  let D := ⨁ χ, X χ
  let lof := DirectSum.lof ℂ (PontryaginDual J₁(S)) X
  let : ∀ χ, UniformSpace (X χ) := fun χ ↦ UniformSpace.comap Subtype.val inferInstance
  let : ∀ χ, IsUniformAddGroup (X χ) := fun χ ↦
    IsUniformAddGroup.comap (f := (Eₛ(χ)).subtype.toAddMonoidHom)
  let : ∀ χ, CompleteSpace (X χ) := fun χ ↦
    (isClosed_actionIsotype (ρₛ₁(S)) χ).completeSpace_coe
  -- from here verbatim as lines 528-543 of the global proof
```
Lemmas (all verified by grep): `sLocalAdelicThetaSpace_t2_of_isClosed` (Ch05/Sec1.lean:904),
`sLocalAdelicTheta_ker_isClosed` (Ch05/Sec1.lean:1108), `sLocalAdelicThetaSpace_polynormable` (Ch05/Sec1.lean:890),
`sLocalAdelicThetaSpace_complete` (Ch05/Sec2.lean:110), `isClosed_actionIsotype` (Ch04/Sec3b.lean:40, public,
needs `T2Space` and `ContinuousSMul`). The global proof takes closedness from `globalThetaIsotypicAverage_equiv`;
its local analogue `sLocalThetaIsotypicAverage_equiv` is still `sorry`, so use `isClosed_actionIsotype` directly.

The one structural point: the helpers are declared after the theorem (lines 363-502 vs 353). The theorem block
(lines 351-360) has to move below line 502, e.g. next to `globalThetaIsotypeSum_complete`. Nothing in between
uses it, both places are inside `section IsotypicSums`, no import changes, and `scripts/signatures.sh --compare`
is keyed by name, so the move is invisible to the statement check. Say so in the PR.

Expected hard step: none mathematically; possible elaboration slowness (the neighbouring
`sLocalThetaIsotypeSum_dense` needed `with_reducible_and_instances`).

Risks: 4 other claims in this file (#4290 #4292 #4296 #4316), no open PR touches Sec2.lean at 07:05 UTC.
The earlier submitter (elmismisimoxhunca's automation) reclaimed once before and may resubmit.

### 2. #5609 `mem_criticalTraceTestSubmodule_iff` (Ch13_ZerosHecke/Sec3.lean:111) — grade B

Statement: φ lies in the common kernel of the log-norm moments `∫ φ·χ₀·(log|g|)^k dμ` (χ₀ trivial on the section
τ, k < [F:ℚ]) iff for every unitary χ and real x with `χ(τ t) = t^{ix}`, the first [F:ℚ] derivatives at
`s = -ix` of `s ↦ ∫_t χ(τ t) t^s ∫_{C₁} φ(τ t·g) χ(g)` vanish.

The statement is true and non-vacuous: with `f_s(h) = φ(h)·χ(h)·|h|^s` the right-hand function is
`∫_{C𝔽} f_s dμ` (norm-fibre disintegration, using `χ(τt·g) = χ(τt)χ(g)` and `|τt·g| = t`), its k-th derivative
at `-ix` is `∫ φ·χ·|·|^{-ix}·(log|·|)^k`, and `χ₀ := χ∘(h ↦ h/τ|h|)` equals `χ·|·|^{-ix}` pointwise and is
trivial on the section. Conversely a section-trivial χ₀ is the case `x = 0`.

History: two closed PRs (#5895, #5940, identical diff, saved as `pr5895.diff`) from corneliusroemer-agent
contained only the skeleton with every analytic step `sorry`; rejected for inline `sorry`s, issue released 06:37 UTC.

Steps:
1. Lemma A (disintegration): for continuous compactly supported `f : C𝔽 → ℂ`,
   `∫ f ∂μ𝔽 = ∫ t, ∫ g : C₁, f (τ t * g.val) ∂normOneIdeleClassTamagawaMeasure F ∂positiveRealHaar`.
   The ready-made formula `classTamagawa_normProduct` (Ch03_IdelicZeta/Sec2.lean:3612) is private; Ch12 Sec5
   `normTest_mellin` (:785-830) shows its use (`integral_map`, then a product integral) and is the template.
   Public routes that stay inside Sec3.lean:
   (a) `ideleClassTamagawaMeasure_eq_smul_canonical` (Ch09/Sec2.lean:630) with
       `canonicalModulatedHaar_eq_map_prod` (AppD/Sec2a.lean:815), taking `μ₁ := (V)⁻¹ • normOne measure`;
   (b) Weil's formula from `(multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.2.2.2`
       (`IsWeilQuotientMeasure`, AppD/Sec1a.lean:2135) with `lcaCosetIntegral_mk` (AppD/Sec1a.lean:2115) and the
       equivalence `C𝔽 ⧸ C₁ ≃ ℝ≥0ˣ` (`QuotientGroup.quotientKerEquivOfRightInverse`, `MeasurableEquiv.map_symm`).
   Get integrability on the product by transporting `Integrable f μ𝔽` through `integrable_map_measure`;
   `positiveRealHaar_isHaarMeasure` is private, `SFinite positiveRealHaar` is `by unfold positiveRealHaar; infer_instance`.
2. Lemma B: for all χ, s the statement's iterated integral equals `∫ h, φ.val h * ideleClassNormTwist χ s h ∂μ𝔽`
   (Lemma A plus `integral_const_mul`; integrability from `spectralConvolution_mellin_integrable`, Ch10/Sec3.lean:830).
3. Lemma C: `iteratedDeriv k (fun s ↦ ∫ h, φ h * twist χ s h) s₀ = ∫ h, φ h * twist χ s₀ h * (log|h|)^k`.
   Exactly `iteratedDeriv_exp_moment_of_measurable` / `iteratedDeriv_normTwist_moment`
   (Ch09_HardySobolev/Sec2.lean:1456 and :1989), both private and fully abstract; port the ~110 lines as a
   private helper (precedent: "ported from the private ..." in Ch12/Sec4.lean:82). Moment integrability:
   continuous with compact support.
4. Assembly: build χ₀ as in `criticalTraceSpectral_converges` (same file, lines 150-168: `p`, `r`, `χ ω := ω.comp r`);
   unfold membership with `Submodule.mem_iInf`, `LinearMap.mem_ker`, `IsLinearMap.mk'_apply`;
   `spectralZeroJet χ 0 0 k g = twist χ 0 g * (log|g|)^k` (Ch10/Sec2.lean:421).

Expected hard steps: Lemma A (instance alignment of the Borel/Haar local instances, Fubini) and the port in
Lemma C. Estimated 250-350 lines.

Risks: 2 other claims in the file (#5610, #5613). Open PR #6092 (for #5610) inserts helpers directly after this
theorem's `sorry` line, so whichever merges second must rebase. Keep imports untouched (the file's
`import all` lines are being removed project-wide under #5966).

### 3. #5516 `Printed.primaryDivisorialStratum_eq_norm_preimage_false` (Ch11_ShellStructure/Sec3_Printed.lean:48) — grade B-/C, stretch

Statement: refute "unit at every place above the first k primes ⇔ norm is a unit at those primes".
The proposition does not require T to avoid S, so any F ≠ ℚ works: no need for ℚ(√−7) or its class number.

Route: F := `CyclotomicField 4 ℚ` (used in five other `_Printed` files); S := a saturated finite set containing
the ramified places and the T of `eventually_trivial_sIdealClassGroup` (AppA/Sec2b.lean:3542); a completely split
prime p from `infinite_split_primes_unramified` (Ch07/Sec1b.lean:315, itself `sorry`, allowed as a dependency);
k with p among the first k primes; two places v ≠ w over p; idele with a uniformizer at v, its inverse at w,
1 elsewhere. Its norm is a unit at p by the pointwise formula `rationalAdeleNorm_finitePlace`, as in
`relativeIdeleNormRat_mem_divisorialStratum` (Ch11/Sec3.lean:242).

Sibling merged-or-pending since the note: the release note's blocker was that `rationalAdeleNorm_finitePlace`
is private. Open PR #6174 (koffie, 06:45 UTC) makes it public. Until that merges the issue is blocked on it.

Hard steps: finite set of ramified places as a Finset, exactly-two-places from complete splitting
(`Ideal.sum_ramification_inertia_eq_finrank`), constructing the two-component idele (the earlier agent's
conditional scratch proof of the back half is not in the repo). Realistically more than a few hours.
0 other claims in this file.

After picks 1 and 2 the quality drops sharply; #6161 is the alternative stretch (see table).

## All issues

| # | Declaration | To prove | Grade | Reason |
|---|---|---|---|---|
| 5641 | `introTrace_characterTrace` (Ch01 Sec4) | single-isotype trace identity | C | specialization of `traceFormula` / `traceFormula_exteriorZeros` (Ch12 Sec5, `sorry`), needs the full specialization argument |
| 5657 | `introTraceApprox_spectral_differentiable` | zero sum over an infinite vertical window is entire in z | C | needs locally uniform summability; pointwise sibling #5656 still open |
| 4289 | `existsUnique_sLocalNormOneQuotientTransition` (Ch06 Sec2) | norm-one quotient transition S⊂T | C | norm-compatible idele decomposition missing |
| 4297 | `sLocalThetaIsotypeSum_complete` | see pick 1 | A | twin proved, closed PR has the proof |
| 4299 | `sLocalThetaIsotypeSum_inherited_properties` | LF, nuclear, barrelled, Montel and four strong-dual properties of the isotype sum | C | eight properties, none available for these direct sums; note-less auto-release |
| 4300 | `globalThetaIsotypeSum_inherited_properties` | same, global | C | same |
| 4301 | `globalThetaToHomogeneousProduct_not_isClosed_range` | image in ∏ Θω not closed | C | needs nonvanishing of infinitely many homogeneous quotients of unbounded conductor |
| 4305 | `sLocalStandardThetaTensor_toGlobal_openQuotient` | open quotient map | C | surjectivity is the cyclic-vector claim of p. 301; continuity of `sLocalStandardThetaTensor` not in library |
| 4306 | `infiniteStandardThetaAverage_integrable` | integrability over norm-one archimedean ideles | C | no concrete description of `sNormOneIdeleTamagawaMeasure F ∅`; decay lemmas private |
| 4308 | `exists_infiniteStandardThetaAverage` | continuous map into C(I∞) | C | downstream of #4306 |
| 4317 | `sLocalStandardThetaTensor_quotient_equiv` | quotient iso | C | same cyclic-vector content as #4305 |
| 4318 | `infiniteStandardThetaAverage_forwardDecay` | Schwartz-type decay of the average | C | downstream of #4306 |
| 4319 | `infiniteStandardThetaAverage_logBound` | log^{r1+r2-1} bound | C | needs S-unit lattice point count (Thm A.4.1.1, not formalized) |
| 4457 | `globalPrincipalValueConverse_nontrivial` (Ch06 Sec3) | PV image = Bergman ideal | C | division by Euler factors in Schwartz-Bergman space (ERRATA I200) |
| 4458 | `globalPrincipalValueConverse_normTwist` | same, norm-twist component | C | same |
| 4462 | `globalPrincipalValueConverse_normTwist_divided_exact` | divided residue map exact and open | C | non-PV sibling `globalConverse_normTwist_exact` still `sorry`; needs continuity of residues on the PV image |
| 4871 | `globalPolarFreeTheta_directionallySmooth` (Ch10 Sec1) | theta smooth along every one-parameter subgroup | C | differentiation under the lattice sum in archimedean directions |
| 4903 | `globalThetaSobolev_fourier_extension_iff` | Fourier extends iff a = 1/2 | C | necessity is a recorded paper gap (p. 438) |
| 5221 | `spectralLineConvolution_trace` (Ch10 Sec3) | trace = absolutely convergent zero sum | C | needs diagonal coefficients of convolution in the jet basis; sibling #5223 open |
| 5222 | `spectralLineIsotypeConvolution_rapid_approximationNumbers` | rapid decay of singular values | C | convolution factorization machinery absent |
| 5226 | `spectralStripConvolution_traceNorm_continuous` | linear lift, continuous in trace norm | C | closed-graph argument on an LF space; line twin #5219 claimed |
| 5228 | `spectralStripConvolution_trace` | strip version of #5221 | C | same |
| 5229 | `spectralStripIsotypeConvolution_rapid_approximationNumbers` | strip version of #5222 | C | same |
| 5186 | `sLocalUncutCarving_lt` (Ch11 Sec1b) | strict inclusion of carving stages | C | needs a test with nonzero Mellin value at a new Euler zero |
| 5194 | `sLocalCarvingLimit_eq_closedSpan` | limit = closed span | C | uses open #5193 and an undefined object (p. 483 gap) |
| 5463 | `absolutePWProjection_tendsto` (Ch11 Sec2b) | PW projections converge | C | reduced to a density lemma that stays open |
| 5477 | `primeOrbitalSobolevQuotient_completion` | quotient norm formula, dense range | C | density of test denominator in the pulled-back closure not established |
| 5481 | `primeOrbitalSobolevConvolution_nuclear` | trace class | C | no bound on biorthogonals (file TODO) |
| 5482 | `primeOrbitalSobolevConvolution_traceNorm_continuous` | trace-norm continuity | C | same |
| 5484 | `primeOrbitalSobolevConvolution_trace` | trace formula | C | same |
| 6161 | `orbitalEulerSum_eq_poisson_local` (Ch11 Sec3) | Poisson summation for one unramified place | B-/C | true; needs a real Schwartz profile from a Bruhat test (smoothness of the C₁-average in log-norm), private `classTamagawa_normProduct`, and a new import of `Mathlib.Analysis.Fourier.PoissonSummation` |
| 5516 | `Printed.primaryDivisorialStratum_eq_norm_preimage_false` | see pick 3 | B-/C | long algebraic chain, waits on PR #6174 |
| 5556 | `exists_sLocalTraceLift` (Ch12 Sec4) | compactly supported lift with given S-unit periodization | C | periodization surjectivity for compact support over the S-units not available (only `schwartzBruhatCosetIntegral_surjective`) |
| 5609 | `mem_criticalTraceTestSubmodule_iff` (Ch13 Sec3) | see pick 2 | B | true, both analytic steps have templates |
| 5612 | `criticalTraceGeometric_converges` | finite-place series converges to a continuous functional | C | needs summability of local principal values and continuity; explicit formula sibling open with different normalization |
| 3880 | `hasSlowGrowthNearPoles_completedHeckeL_logDeriv` (AppB Sec4b) | log-derivative bounds avoiding zeros | C | classical zero-density style estimates absent |
| 3894 | `complexLogFourier_finitePart` | planar Fourier transform of log‖z‖² | C | the real case took the 751-line `ForMathlib/Analysis/Fourier/Log.lean`; no planar analogue |

No statement in this set looks false or vacuous (no F).

## Claims by others per file (label `claimed`, from `.agent/proof-issues.jsonl`)

Ch01 Sec4: 10. Ch06 Sec2: 4. Ch06 Sec3: 5. Ch10 Sec1: 8. Ch10 Sec3: 3. Ch11 Sec1b: 1. Ch11 Sec2b: 1.
Ch11 Sec3: 2. Ch11 Sec3_Printed: 0. Ch12 Sec4: 4. Ch13 Sec3: 2. AppB Sec4b: 7.

## Reusable

- `gh pr list -R mccorvie/riemann-masullo --state all --search "<declaration name>"` finds closed PRs for an
  issue. A PR closed by the merger for a stale conflict can hold a finished proof (#5915 for #4297).
- `gh api repos/mccorvie/riemann-masullo/issues/<n>/timeline` shows label and cross-reference events that
  `gh issue view --comments` omits (how #5895/#5940 were found).
- Private abstract lemmas worth porting: `iteratedDeriv_exp_moment_of_measurable` (Ch09/Sec2.lean:1456),
  `classTamagawa_normProduct` (Ch03/Sec2.lean:3612), locally convex direct-sum completeness
  (Ch06/Sec2.lean:363-502).
- Open "make helpers public" PRs (#6173, #6174, #6179, #6188, part of #5966) change which private lemmas are
  reachable; check them before porting.
- Saved material: `03-scout-misc/issues/` (issue bodies and comments), `pr5915.diff`, `pr5895.diff`,
  `pr6092.diff`, `open_prs.txt` (open PRs with files, 07:05 UTC).
