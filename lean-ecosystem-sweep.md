# 04: Lean ecosystem sweep (2026-11-23)

Scope: outside Lean developments and tools that a prover on riemann-masullo (Lean v4.36.0, Mathlib v4.36.0 = `fc4f59e5`) could reuse. Only things missing from, or newer than, `RiemannMasullo/External/SURVEY.md`, `survey/*.md` and `ATTRIBUTION.md` are listed. **[V]** = I opened the source file and read the statement. **[H]** = a helper read it and I spot-checked it (file exists, name and statement match, sorry count). **[S]** = search result or README claim only.

## What changes what a prover does tomorrow

1. **Exponential-polynomial independence has a drop-in proof on the same pin.** `LeanPool.StrongSix.M2.expPoly_indep` (LeanPool/lean-pool, Apache-2.0, Lean v4.36.0, Mathlib `v4.36.0`, 0 sorry) [V] proves the discrete form Σ_ρ Q_ρ(n) ρⁿ = 0 ∀n ∈ ℕ ⇒ Q_ρ = 0. The continuous statement follows in about 40 lines by sampling at t = n·h. Recipe in `priority-1.md`. It is in neither Mathlib (tag or master) nor any open PR.
2. **Tau Ceti already has much of what open issues ask for, and the survey misses it.** All at TauCeti HEAD `c638212b`, Apache-2.0, Lean v4.37.0-rc1, Mathlib master; port, don't import:
   - Mittag-Leffler with prescribed principal parts: `exists_meromorphic_prescribed_principal_parts` [V].
   - Residues tied to `meromorphicOrderAt` and to `meromorphicTrailingCoeffAt` [V].
   - `circleLaurentCoeff_neg_one_eq_residue` [V].
   - Mellin line-shift with residues: `mellinInv_eq_sum_residue_add`, `mellinInv_sub_mellinInv_eq_sum_residue` [V].
   - Dual of a quotient ≅ annihilator, as an isometric equivalence: `quotientDualEquivAnnihilator`, **normed spaces only** [V].
   - Topological bipolar theorem [H].
   - Non-archimedean locally convex Hahn–Banach [H].
   - Nuclear-operator trace [H].
   - Dual projective limits that are Montel: `DualProjectiveLimit.montelSpace` [V].
3. **A cold clone does not need a 45-minute build.** The project's own `Main state` workflow uploads `.lake/build` of every main push as artifact `main-state`. It is about 370 MB, kept for 1 day, and there were 115 of them on 2026-11-23. `scripts/ci/base_state.py` restores it:
   ```
   lake exe cache get
   GH_TOKEN=$(gh auth token) GH_REPO=mccorvie/riemann-masullo REPO_ID=1465783492 \
     python3 scripts/ci/base_state.py --work . --base $(git rev-parse HEAD) --out ./tmp/base-state
   ```
   This needs only read access. Verified by reading the workflow and the script and listing the artifacts; I did not run the restore.
4. **Several of the analytic gaps are filled outside Tau Ceti, most on the same or an adjacent pin.** All [H], spot-checked by me, 0 sorry:
   - `mellin_mellinInv_eq`, Mellin round trip (bjbraams/lean-codes).
   - `MeromorphicAt.exists_principalPart_add_analyticAt` and `laurentCoeffAt_order` (LeanPool, same pin).
   - The easy Paley–Wiener direction, entire of exponential type (bjbraams/lean-CA).
   - Mittag-Leffler expansions (bjbraams/lean-DLMF, same pin).
   - Adelic and idelic Haar statements, in about 29k standalone theorem files (anthropics/fermats-last-theorem).

## Priority 1: independence of t^j e^{zt}

Full write-up: `priority-1.md`.

- **Mathlib v4.36.0:** absent. I grepped the local source. There is no `LinearIndependent` statement about `cexp`/`Complex.exp` and no exponential-polynomial file.
- **Mathlib master (`90e6eec9`, 186 commits past the tag) and open PRs:** absent [H].
- **Zulip:** the only discussion is a 2022 Lean 3 thread ("Linear combinations of t^k e^{λt}"). Its PR number does not resolve to a relevant mathlib4 PR.
- **Existing proof:** `LeanPool.StrongSix.M2.expPoly_indep` in https://github.com/LeanPool/lean-pool, file `LeanPool/RoyStrongSix/M2/ExpPoly.lean`. Last changed in `5dd712603d49049c7a5198e5dd725f768c5a510b`; repo HEAD is `de53f087`. Apache-2.0, © 2026 Shawn Krisman. It is a `module` file with only Mathlib imports, about 110 lines with its helpers. [V]
  ```lean
  variable {K : Type*} [Field K] [CharZero K]
  theorem expPoly_indep (R : Finset K) (h0 : ∀ ρ ∈ R, ρ ≠ 0) :
      ∀ Q : K → K[X], (∀ n : ℕ, ∑ ρ ∈ R, (Q ρ).eval (n : K) * ρ ^ n = 0) → ∀ ρ ∈ R, Q ρ = 0
  ```
- **Reduction to the continuous statement:**
  1. Choose h > 0 so that exp(h·z) is injective on the finite set of exponents, e.g. h = 1/(1+Σ‖z−z'‖). Use `Complex.exp_eq_exp_iff_exists_int`.
  2. Apply the theorem to ρ_z = exp(hz) and Q_z = P_z.comp (C h * X).
  3. Recover P_z = 0 with `Polynomial.comp_C_mul_X_eq_zero_iff`.

  Every Mathlib name in this route was checked to exist at the pin.
- **Mathlib-only alternative:**
  - Take generalized eigenvectors of the shift `f ↦ f(·+h)` on `ℝ → ℂ`.
  - Independence comes from `Module.End.independent_genEigenspace` (LinearAlgebra/Eigenspace/Basic.lean:692) together with `iSupIndep.dfinsupp_lsum_injective` or `iSupIndep.linearIndependent` (LinearAlgebra/DFinsupp.lean:546,640).
  - The degree drop comes from `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt` (Algebra/Group/ForwardDiff.lean:268).

  This needs more glue than the port.
- **Building blocks that do not reach the goal:**
  - `linearIndependent_monoidHom`: Dedekind independence, covers only j = 0.
  - `AddChar.linearIndependent`: finite groups only.
  - `Polynomial.eq_zero_of_infinite_isRoot`, `Polynomial.funext`.
  - PrimeNumberTheoremAnd `Mathlib/Analysis/Complex/ExpPoly/Growth.lean` has only a degree bound, `natDegree_le_floor_of_exp_eval_norm_bound` [H].

## Outside libraries

Portability:
- **paste** = same pin (v4.36.0 / `fc4f59e5`); expect it to compile with few changes.
- **port** = other pin; re-prove with the source open.

All rows are 0 sorry in the cited file unless noted.

| Project | URL | Licence | Lean / Mathlib | Relevant declarations (path) | Portability |
|---|---|---|---|---|---|
| LeanPool | https://github.com/LeanPool/lean-pool @ `de53f087` | Apache-2.0 | v4.36.0 / `v4.36.0` | `expPoly_indep` (`LeanPool/RoyStrongSix/M2/ExpPoly.lean`) [V]; `MeromorphicAt.exists_principalPart_add_analyticAt`: f =ᶠ principalPartAt + analytic h, with Taylor coeffs of h = nonnegative Laurent coeffs (`LeanPool/JacobianDiffgeo/ResidueCalculus/PrincipalPart.lean`) [H]; `laurentCoeffAt_order` = `meromorphicTrailingCoeffAt` (`…/ResidueCalculus/LaurentCoeff.lean`) [H]; `mlCoeff` Mittag-Leffler coefficient data (`…/MittagLeffler.lean`) [H]; `NuclearSpace`, `IsHilbertNuclear` classes over ℝ (`LeanPool/OSforGFF/…`) [H] | paste |
| Tau Ceti | https://github.com/TauCetiProject/TauCeti @ `c638212be3d6c8cc7d3ee1a4c57716357dbe3434` | Apache-2.0 | v4.37.0-rc1 / master `31ce06ea` | see the list below | port (the project already vendors from 8794ab3) |
| bjbraams/lean-codes | https://github.com/bjbraams/lean-codes @ `39ce9533` | Apache-2.0 | v4.36.0-rc2 | `mellin_mellinInv_eq`: Ψ continuous and integrable on Re = σ and `MellinConvergent (mellinInv σ Ψ) σ` ⇒ `mellin (mellinInv σ Ψ) s = Ψ s` on Re s = σ (`ToMathlib/Analysis/MellinBarnes.lean:543`) [H] | near-paste |
| bjbraams/lean-DLMF | https://github.com/bjbraams/lean-DLMF @ `1585f72e` | Apache-2.0 | v4.36.0 / `fc4f59e5` | `exists_analyticAt_tsum_mittagLeffler_eq`: Σ a_k(1/(z−z_k)+1/z_k) has principal part a_n/(z−z_n) at z_n (`DLMFMathlib/Analysis/Complex/MittagLeffler.lean:136`) [H] | paste |
| bjbraams/lean-CA | https://github.com/bjbraams/lean-CA @ `bf70bd0a` | Apache-2.0 | v4.36.0-rc1 | `paleyWienerTransform`, `hasExponentialTypeLE_paleyWienerTransform`: the Fourier–Laplace transform of an L¹ function on [−τ,τ] is entire of exponential type ≤ τ; easy direction only (`ComplexAnalysis/PaleyWiener.lean`) [H]; `MeromorphicAt.exists_principalPart` (`ComplexAnalysis/Residue/PrincipalPart.lean`) [H]; `residue_eq_contour_residue`, which depends on Tau Ceti [H] | near-paste |
| anthropics/fermats-last-theorem | https://github.com/anthropics/fermats-last-theorem @ `6e837e75` | Apache-2.0 | v4.33.1 / `db584cd6` | Beyond what the survey cites: `MellinParseval.setIntegral_Ioi_inv_mul_cpow_neg_mul_lineIntegral_eq_two_pi_mul`; `NumberField.AdeleRing.compactSpace_quotient_principalSubgroup` (𝔸_F/F compact); `NumberField.Idele.lintegral_comp_mul_norm_one_mul_maximalCompact_eq_of_isFundamentalDomain_of_periodic` (unfolding over a norm-one-invariant fundamental domain of F^×\𝕀_F); `NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm` (Haar character on adele units = product of local norms). All in `Theorems/Thm_<name>.lean` [S/H, statements copied by a helper, not opened by me] | port |
| AxiomMath/DedekindZetaZeroFree | https://github.com/AxiomMath/DedekindZetaZeroFree @ `09afbb4c` | Apache-2.0 | v4.35.0-rc3 | `mellin_inversion_positive_line`: smooth and compactly supported h ⇒ `mellinInv σ (mellin h) x = h x` for σ > 0 (`HarmonicAnalysis/Mellin/PositiveLineInversion.lean`) [H] | port |
| FLT (Imperial) | https://github.com/ImperialCollegeLondon/FLT @ `01980581` | Apache-2.0 | v4.35.0 / `56a00585` | `MeasureTheory.ringHaarChar_adeles_rat` (`FLT/HaarMeasure/HaarChar/AdeleRing.lean`) [H]; nothing on Tate's thesis | port |
| PrimeNumberTheoremAnd | https://github.com/AlexKontorovich/PrimeNumberTheoremAnd @ `a4fb6989` | Apache-2.0 | v4.35.0 | `rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt` (argument principle on rectangles) [H]; `MellinConvolutionTransform` [H]; `natDegree_le_floor_of_exp_eval_norm_bound` [H] | port |
| mrdouglasny/os-reconstruction (also xiyin137/OSreconstruction) | https://github.com/mrdouglasny/os-reconstruction @ `a63f1432` | Apache-2.0 | v4.35.0-rc4 | `OSReconstruction/SCV/PaleyWiener.lean`: `HasOneSidedFourierSupport`, `fourier_pairing_eq_of_eqOn_nonneg` [H]; the survey cites OSReconstruction already | port |
| facebookresearch/atlas-lean | https://github.com/facebookresearch/atlas-lean @ `b35e9fd0` | **custom, not SPDX (check before porting)** | v4.35.0 | `fujisaki_compact_fundamental_region` (`v1/Atlas/NumberTheoryI/code/Ideles.lean`, **4 sorry in the file**); `poisson_summation`; `montel_normal_families` [H] | read only until the licence is checked |
| physlib | https://github.com/leanprover-community/physlib @ `db96e885` | Apache-2.0 | v4.36.0 / `fc4f59e5` | `toTemperedDistribution_fourierTransform` (`Physlib/Mathematics/Distribution/TemperedDistribution.lean`) [H] | paste |
| Mathlib open PRs | leanprover-community/mathlib4 | Apache-2.0 | master | #26345 topological bipolar theorem (open); #44899 reflexive TVS class (open); #42278 nuclear space (draft); #42127 projective LC tensor topology (draft); #45403 algebraic properties of distribution support (draft); #29588 residue theory (open, stale 2025-09); #39232 rectangle residue theorem (draft); #40791 Dirichlet S-unit theorem (open); #45841 𝔸_ℚ = ℝ × 𝔸_f (open); #36404 adeles of a number field locally compact (open); #40582 one-sided Laplace transform (open). Open/draft state verified with `gh pr view` | port from the PR diff |

**Tau Ceti, by topic.** Repo described as "An AIs-welcome Lean library downstream of Mathlib": AIs implement and review, humans write roadmaps and rubrics, bors merges after a human r+, the Mathlib pin is bumped hourly, and the org has 24 repos (Roadmap, Review, Worker, Tools, …). Paths are under `TauCeti/`. "new" = absent at the vendored commit 8794ab3; everything else already existed there but is not cited in the survey.

- **Dual of a quotient and annihilators:**
  - `quotientDualEquivAnnihilator (S) : StrongDual 𝕜 (E ⧸ S) ≃ₗᵢ[𝕜] S.orthogonalBilin (topDualPairing 𝕜 E).flip` (`Analysis/Normed/Module/Dual/Quotient.lean`, normed) [V].
  - `exists_dual_eq_infDist`, `mem_topologicalClosure_iff_forall_dual_eq_zero` (`Analysis/Normed/Module/Annihilator.lean`) [H].
  - `map_orthogonalBilin_flip_orthogonalBilin_eq_topologicalClosure` (`Analysis/LocallyConvex/WeakDual/Annihilator.lean`) [H].
  - `kerDualMapEquiv`, `cokerDualMapEquiv` (algebraic, `LinearAlgebra/Dual/Annihilator.lean`) [H].
  - The locally convex / Fréchet strong-topology versions the project needs are **not** there.
- **Bipolar:** `bipolar_eq_closedAbsConvexHull`, `bipolar_eq_closure` (`Analysis/LocallyConvex/Bipolar.lean`) [H]; `isVonNBounded_polar` [H].
- **Hahn–Banach:** non-archimedean `exists_extension_of_isNonarchimedean` (`Analysis/LocallyConvex/HahnBanach/Nonarchimedean.lean`) [H]. No new archimedean LC version; Mathlib's `geometric_hahn_banach_*` and the project's own `exists_dual_norm_eq_seminorm` already cover that.
- **Montel:**
  - new `MontelSpace.of_isClosedEmbedding`, `MontelSpace.pi`, `MontelSpace.of_isScalarTower` (`Analysis/LocallyConvex/Montel.lean`) [H].
  - `DualProjectiveLimit.montelSpace (hT : ∀ n, IsCompactOperator (T n)) : MontelSpace 𝕜 (dualProjectiveLimit T)` and `bidualEquiv` (`Analysis/LocallyConvex/DualProjectiveLimit.lean`) [V]. This file and `LocallyConvex/CompactInductiveLimit.lean` (not read) look like the closest match to the paper's LF/Fréchet–Schwartz duality.
  - Banach reflexivity through bases: `surjective_inclusionInDoubleDual_iff` (`Analysis/Normed/Module/Bases/Reflexive.lean`) [H].
- **Mittag-Leffler:**
  - `exists_meromorphic_prescribed_principal_parts {Ω E : Set ℂ} (hEΩ : E ⊆ Ω) (hE : Eᶜ ∈ codiscreteWithin Ω) (P : E → ℂ → F) (hP : ∀ a, MeromorphicAt (P a) a) : ∃ f, MeromorphicOn f Ω ∧ (∀ a, ∃ g, AnalyticAt ℂ g a ∧ ∀ᶠ z in 𝓝[≠] a, f z - P a z = g z) ∧ DifferentiableOn ℂ f (Ω \ E)` (`Analysis/Complex/MittagLeffler.lean:562`) [V].
  - Sheaf-cohomology version for Riemann surfaces (new) [H].
- **Borel-type asymptotic sums:** `exists_asymptoticSum` for symbol classes and `borelSum` (`Analysis/Pseudodifferential/AsymptoticSum.lean:780`) [V]. This is Borel's construction for symbols, not Borel's lemma for Taylor coefficients, but the summation scheme is reusable.
- **Residues and Laurent:**
  - `Contour.residue`, `residue_eq_zero_of_meromorphicOrderAt_nonneg`, `residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one` (`Analysis/Contour/Residue/Basic.lean:188`) [V].
  - `residue_eq_of_order_lt_zero`, an iteratedDeriv formula [H].
  - `circleLaurentCoeff_neg_one_eq_residue` (`Analysis/Complex/Laurent/PrincipalPart.lean:272`) [V].
  - `PolarPartDecomposition` (`Analysis/Contour/PolarPart/Decomposition.lean`, not read).
- **Mellin:**
  - `mellinInv_sub_mellinInv_eq_sum_residue` (`Analysis/MellinInversion.lean:154`) [V].
  - new `mellinInv_eq_sum_residue_add` (`Analysis/MellinTransform/LineShift.lean:48`) [V].
  - `integral_mul_comp_mul_eq_mellinInv` (Mellin convolution, `Analysis/MellinTransform/Convolution.lean`) [H].
- **Nuclear and trace:**
  - `nuclearOperators`, `mem_nuclearOperators_iff_exists_hasSum`, nuclear `trace` and `hasSum_trace` on Banach spaces (`Analysis/Normed/Operator/Nuclear.lean`) [H].
  - new Hilbert trace-class `trace_eq_tsum_inner_apply` (`Analysis/OperatorIdeal/Family/TraceClass/Trace.lean`) [H].
- **Distributions:**
  - `dsupport_apply_apply_subset`: δ-type functionals are supported in {x} (`Analysis/Distribution/Support.lean`) [H].
  - `mass_sum_smul_delta` [H].
  - Not the converse (point support ⇒ finite sum of δ derivatives).
- **Number theory:**
  - S-unit theorem `finrank_sUnits_numberField` with fundamental system `exist_unique_eq_mul_prod` (`NumberTheory/NumberField/Units/SUnit/`) [H].
  - adele and idele basics (`NumberTheory/NumberField/Global/Adeles/`, `Ideles/Basic.lean`).
  - S-ideles and idele class finiteness under `ClassFieldTheory/Global/` [S].
  - No Tate zeta integral and no Haar measure on ideles.

**Out of date in the project's survey.**
- `jonhanke/algebraic-number-theory-lean` now returns 404 on GitHub (`gh api repos/jonhanke/algebraic-number-theory-lean`). The vendored copy at `5ea368e` and the survey's links are now the only access; links to it in `SURVEY.md`/`README.md` are dead.
- Tau Ceti moved from `8794ab3` to `c638212b`. Its Lean is still v4.37.0-rc1.

## Tooling

[V] = README or source opened by a helper. Unmarked = from search snippets [S].

| Tool | URL | Offline? | 4.36? | Use here |
|---|---|---|---|---|
| Project build artifact `main-state` | `.github/workflows/main_state.yml`, `scripts/ci/base_state.py` | needs GitHub read | yes | Restore main's `.lake/build` instead of building cold (command above) [V, me] |
| Loogle | https://github.com/nomeata/loogle (Apache-2.0) | yes, local build plus index | yes, with a matching toolchain | Type-shape search, e.g. `Polynomial.comp, Polynomial.eval`; the hosted version lags behind the pin [V] |
| LeanSearchClient (`#leansearch`, `#loogle`, state search) | already in `.lake/packages/LeanSearchClient` | no, hosted APIs | in the manifest | Natural-language lookup from inside a file [V] |
| LeanSearch | https://leansearch.net | no | unknown | Natural-language Mathlib search [V page] |
| LeanExplore | https://github.com/lean-explore/lean-explore (Apache-2.0) | local mode: `pip install lean-explore[local]`, `lean-explore data fetch`, `lean-explore mcp serve --backend local` | data version unverified | Semantic search over Mathlib (+ PhysLean/FLT) as an MCP server [V] |
| Lean Finder | https://github.com/delta-lab-ai/lean-finder | self-host | indexes only Mathlib 4.19/4.24/4.28 | Not useful at this pin [V] |
| Moogle | moogle.ai | – | – | Dead (TLS expired, repo 404) [X] |
| lean-lsp-mcp | https://github.com/oOo0oOo/lean-lsp-mcp (MIT) | LSP and `lean_local_search` offline; search tools online | yes; use repl tag v4.36.0, not the README's v4.35.0 | Goals, diagnostics, hover, multi-attempt for an agent without a running editor. Local Loogle needs ~13 GiB to index, so mind RAM next to a full build [V] |
| leanprover-community/repl | https://github.com/leanprover-community/repl (Apache-2.0), tag v4.36.0 | yes | yes | JSON command/tactic REPL; base for LeanInteract and Kimina [V] |
| LeanInteract / LeanProbe | https://github.com/augustepoiroux/LeanInteract (MIT), https://github.com/epfl-lara/LeanProbe (MIT) | yes | LeanInteract documented up to v4.36.0-rc1 | Python-driven proof checking with a warm REPL [V] |
| Pantograph | https://github.com/lenianiva/Pantograph (Apache-2.0) | yes | pin the toolchain | Machine REPL [V] |
| LeanHammer / duper | https://github.com/JOSHCLUNE/LeanHammer (Apache-2.0) | yes | **README stops at v4.35.0** | Not usable at 4.36 until a release appears [V] |
| LeanCopilot | https://github.com/lean-dojo/LeanCopilot (MIT), tag v4.36.0 | yes, after the model download | yes | Local tactic suggestions and premise selection; needs a lakefile change, so not for this repo's PRs [V] |
| Core tactics | Lean core / Mathlib | yes | yes | `exact?`, `apply?`, `rw?`, `simp?`, `hint`, `grind`/`grind?`, `fun_prop`, `bound`, `positivity` all exist at 4.36 [V]. 4.36 release notes: `grind?`/`finish?` fixes, `[grind hom] fallback`, `backward.grind.normalizer` [V]. `canonical` not found [X] |
| Module system | https://lean-lang.org/doc/reference/latest/The-Module-System/Visibility | – | yes | `module` + `public import` + `@[expose] public section`: theorem bodies are not exported, so editing a proof does not force downstream rebuilds. 4.36 adds faster imports and drops exported equation lemmas and private data (release notes [V]). This repo has 448 `module` files already |
| Lake artifact cache | Lake reference manual (`lake cache get/put`, `LAKE_ARTIFACT_CACHE`, `enableArtifactCache`, `[[cache_service]]`) | needs an S3-style service | experimental | Alternative to the artifact trick: `lake cache put` to an S3/R2 bucket from CI, `lake cache get` on clone. Example setup: apnelson1/Matroid `CACHE.md`. Tau Ceti uses its own S3 script `scripts/lake-cache-get.sh` [V] |
| Proof models | DeepSeek-Prover-V2, Goedel-Prover-V2, Kimina-Prover (open weights); Seed-Prover 1.5; Aristotle (Harmonic, hosted API, accepts Lean files with sorry) [S]; Gauss (Math Inc, early access) [S] | weights local / API | n/a | Aristotle is the only one aimed at filling `sorry`s in a whole project; licence and terms unverified |
| Prove2Me / Formalpedia | https://prove2.me, https://github.com/prove2me/formalpedia (Apache-2.0, daily snapshot) | – | – | Already a source in ATTRIBUTION.md; the Formalpedia snapshot is greppable |

Organisation patterns elsewhere:
- **Tau Ceti:** human roadmaps; adversarial AI review against a written rubric (scope, correctness, reuse, attribution, API, generality, placement, naming, docs, proof quality, deprecation); no stacked PRs; an intentions registry for claims; bors merge after a human r+ [V].
- **Equational Theories, FLT, PNT+:** blueprints (leanblueprint).
- **Formal Conjectures:** one GitHub milestone per problem [V].

## Dead ends (searched, nothing found)

- **Borel's lemma (smooth function with prescribed Taylor coefficients):**
  - not in Mathlib tag, master or open PRs, and not in Tau Ceti (only the symbol analogue).
  - `gh search code` for `borel_lemma`, `exists_contDiff_taylor` and "Borel lemma": 0 hits.
  - The project's own `ForMathlib/Analysis/LocallyConvex/MittagLefflerLift.lean` (`surjective_coeff_of_withSeminorms`) is the abstract tool.
- **Distributions supported at a point = finite sums of δ derivatives:** none anywhere (Mathlib tag, master or PRs; Tau Ceti; physlib; gaussian-field; code search for dirac+support).
- **Köthe sequence spaces:** none (`KotheSpace` 0 hits; Tau Ceti only cites Köthe 1953). Nearest: gaussian-field `RapidDecaySeq` and `DyninMityaginSpace` (the survey cites them already).
- **Schauder bases in Fréchet spaces:** none. Everything found is Banach (Mathlib `Bases.lean`, Tau Ceti `Bases/*`, atlas-lean `lpSchauderBasis`).
- **Paley–Wiener converse (exponential type ⇒ compact support), and the Fourier transform of compactly supported distributions:** none. Only the easy direction exists (lean-CA, fermats-last-theorem `MellinPaleyWiener`).
- **Tate's thesis zeta integrals, functional equation, idelic Haar/Tamagawa measure:**
  - nothing new beyond what the survey lists (Hanke, Anthropic FLT).
  - No Mathlib PR.
  - Tau Ceti has adeles, ideles and S-units but no zeta integral.
- **Strong dual of a closed subspace ≅ quotient of the strong dual, as a topological isomorphism (Fréchet/Montel/nuclear):** none outside the project. The project's own `ForMathlib/Topology/Algebra/Module/StrongDualQuotient.lean` (`range_transpose_mkQL`, `completeSpace_strongDual_quotient`) and `StrongBidual.lean` are further along than anything public.
- **No hits in:** Carleson, brownian-motion, sphere-eversion and teorth/analysis.
- **Mathlib master since v4.36.0** (186 commits): nothing topical. Notable renames: `Analysis/Fourier/AddCircle` moved into the `AddCircle` namespace (#45629); `IsConcreteLE.le_iff` → `le_iff_mem_imp_mem`.

## Reusable

- `priority-1.md`: a self-contained port recipe for exponential-polynomial independence.
- `ExpPoly.lean.txt`: the raw upstream file at HEAD `de53f087`.
- `scratch-tauceti/src/`: 71 Tau Ceti files at `c638212b`, for offline reading. Also `tree.txt` (full path list) and `fetch-report.txt` (sorry count, and whether each file existed at 8794ab3).
- `scratch-mathlib/`:
  - `repo/`: a blobless mathlib4 clone.
  - `master_vs_tag.diff`: added lines from v4.36.0 to master.
  - `prs/*-open.json`: open-PR searches by topic.
- `scratch-projects/`:
  - `raw/`, `extract*.txt`: fetched files and extracted statements.
  - `code_search*.tsv`: `gh search code` results.
- `scratch-tooling/readme-*.md`: tool READMEs.
- `verify/`: the four outside files I opened (MellinBarnes, PaleyWiener, PrincipalPart, MittagLeffler).
- Pattern: `gh api 'repos/O/R/contents/<path>?ref=<sha>' -H 'Accept: application/vnd.github.raw'` reads a single file without cloning. The `?ref=8794ab3…` form tells whether a file is new since the vendored commit.
