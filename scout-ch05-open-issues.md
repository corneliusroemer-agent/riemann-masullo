# Scout 01: Ch05 Sec3a / Sec3b / Sec4 / Sec5 (state at 2026-11-23 07:20 UTC, main at 4da8d06)

`$R` = `<repo>`,
files under `$R/RiemannMasullo/Ch05_ThetaZSpaces/`. Nothing was built; every grade is from reading.

## Recommendation

1. **#4159 `sLocalThetaPrincipalValue_toGlobal` (Sec3a.lean:1120)** — grade A. About 80 lines, all from
   public lemmas, in a file with no active competing work.
2. **#4394 + #4403 `sLocalThetaEigendistribution_holomorphic` / `globalThetaEigendistribution_holomorphic`
   (Sec5.lean:579, 712)** — grade A, about 40 lines for the pair, but the file belongs to one very
   active contributor who has already proved both once.
3. **#4230 `complexArchimedeanMellin_existsUnique` (Sec3b.lean:1891)** — grade B, 250–350 lines, in the
   most crowded of the four files.

Both A picks have an existence proof of feasibility: a pull request that built and passed the
project check, and was closed for a reason that has nothing to do with the mathematics.

## Label and crowding state

All 27 assigned issues are open and carry no `claimed`/`stuck`/`gap`/`blocked` label. Three of
them are not untouched, and three more are covered by open pull requests:

| Issue | State behind the label |
|---|---|
| #4159 | PR #5855 (elmismisimoxhunca, +138 −1) proved it; closed 04:54 UTC for a merge conflict in the import block. The merger released the issue "for someone to claim". |
| #4394, #4403 | PR #5954 (Filimoa, +45 −2) proved both; refused because it added `import all …Sec2` (rule enforced since #6103), closed 06:48 UTC, issues released "for others to pick up". |
| #4216, #4226 | Open PR #6167 (cobalt8814) proves both as splits (`Closes #4216`, `Closes #4226`). |
| #4340 | Open PR #6190 (cobalt8814) proves it as a split (`Closes #4340`); the surjectivity half stays `sorry`. |

Claims by other people per file (label `claimed`), and open pull requests touching the file:

| File | Claimed issues | Claimants | Open PRs on the file |
|---|---|---|---|
| Sec3a.lean | 18 | elmismisimoxhunca 17 (an automated runner; claims made 22:04–01:16 UTC, six to nine hours old and still labelled at 07:06 UTC; its last PR was opened at 02:04 UTC), troyjlee 1 | #6160 (troyjlee, lines ≈2414–2460) |
| Sec3b.lean | 12 | elmismisimoxhunca 5, troyjlee 2, mojtaba-amiri 2, alipatti 1, k-ieren 1, cobalt8814 1 | #6167, #6184, #6076, #6042, #6188 (import clean-up) |
| Sec4.lean | 8 | CalebAlbers 3, una-dinosauria 2, iyerkri 2, Filimoa 1 | #6190, #6094, #6059 |
| Sec5.lean | 13 | Filimoa 13 | eight by Filimoa (#6020, #6024, #6033, #6051, #6056, #6073, #6078, #6084); the integrator told him those opened before 05:00 UTC conflict pairwise on their `import all` lines and asked for one combined PR |

Sec3a is the quietest file in practice. Sec5 has a single owner who may resubmit #4394/#4403 inside
a combined pull request. Sec3b and Sec4 exceed the project's own "do not crowd a file" threshold
(two or three other people).

## Grades

### Sec3a.lean

| Issue | Declaration (line) | What must be proved | Grade |
|---|---|---|---|
| #4159 | `sLocalThetaPrincipalValue_toGlobal` (1120) | The S-local principal value on theta classes commutes with insertion into the global theta quotient. | **A** — see pick 1. |
| #4167 | `realTemperedDistribution_eq_sum_diracDerivative` (1666) | A tempered distribution on ℝ supported at 0 is a finite combination of derivatives of δ. | **B−** — needs "T has finite order N" plus the shrinking-cutoff estimate (`χ(x/ε)·f → 0` in the order-≤N Schwartz seminorms when `f` vanishes to order N). The quotient-dual theorems that would shortcut it (`realSchwartzFlatQuotient_strongDual` l.1977, `realDiracDerivatives_polynomialEquiv` l.2022) are declared after it, so they cannot be used without reordering the file. Two automated attempts stopped at exactly this estimate. |
| #4188 | `complexTemperedDistribution_eq_sum_diracDerivative` (2980) | Same on ℂ with mixed Wirtinger derivatives. | **C** — two-variable version of #4167 with no sibling above it. |
| #4192 | `complexDiracDerivatives_polynomialEquiv` (3027) | `FinestLocallyConvex (MvPolynomial (Fin 2) ℂ) ≃L StrongDual (𝓢(ℂ)/flat)` by normalized Dirac derivatives, and order ≤ N ⇔ total degree ≤ N. | **C** — a two-variable port of the 220-line real proof (l.2022–2246); the complex Borel theorem `complexSchwartzTaylor_equiv` (l.3431) is declared after it. |

### Sec3b.lean

| Issue | Declaration (line) | What must be proved | Grade |
|---|---|---|---|
| #4204 | `iteratedDeriv_puncturedTest_closedRange` (486) | `d^m/dx^m` is a continuous operator on `𝓓(ℝ∖{0})` with closed range. | **B** — range = common kernel of the 2m functionals `g ↦ ∫_{±x>0} x^j g`, `j<m`. Mathlib has `TestFunction.lineDerivCLM` and `TestFunction.integralAgainstBilinCLM`; the work is the m-fold primitive (smooth, compact support off 0) and the moment identity by parts. 250–400 lines. |
| #4210 | `iteratedWirtinger_allExponentialDecay` (1030) | m-fold Wirtinger derivatives act continuously on the all-exponent decay space on ℂˣ. | **B−** — assembly from the half-line operator `iteratedWirtinger_exponentialDecay` (#4207, still `sorry`, claimed) by choosing a half-line per target weight; two earlier attempts did not finish this assembly. |
| #4216 | `archimedeanWeightedSchwartz_frechet` (1356) | 𝓦(I) is Fréchet for an open interval I. | Covered by open PR #6167 (split). The remaining halves (countable weight family, completeness) are **C+**. |
| #4220 | `archimedeanWeightedSchwartz_tensor` (1481) | The completed projective tensor of one-variable decay spaces is 𝓦(I). | **C** — kernel theorem for a multi-weight space. |
| #4226 | `archimedeanFlatSchwartz_restrict_equiv` (1624) | Flat Schwartz functions ≃ 𝓦(univ) by restriction. | Covered by open PR #6167 (split); the halves are **C**. |
| #4227 | `archimedeanFlatSchwartz_quasiCharacter_mul` (1632) | A quasi-character of the punctured product acts by a unique linear homeomorphism on flat Schwartz functions. | **C+** — conjugate through #4226; multiplication by a quasi-character on the multi-weight space 𝓦(univ) does not exist yet (`modulatedExponentialDecay_mul_quasiCharacter` is for one modulation). |
| #4230 | `complexArchimedeanMellin_existsUnique` (1891) | The angular-radial Mellin integral of a Schwartz function on ℂ has a unique meromorphic normal-form continuation. | **B** — see pick 3. |
| #4246 | `sLocalIdelicZFunction_entire_of_polarFree` (3031) | Zeta transform of a polar-free test is entire on every chart. | **C** — missing fact: absolute convergence of the zeta integral of a polar-free test at every twist (the Releasing note has the holomorphy half in a scratch file). |
| #4247 | `sAdelePolarFree_quasiCharacter_mul` (3039) | Quasi-characters act on polar-free tests by a linear homeomorphism. | **C**. |
| #4249 | `sLocalHomogeneousTheta_trivial_exists_polarFree` (3050) | Every all-exponent log-Schwartz profile is the trivial homogeneous theta of a polar-free test. | **C** — a construction; the paper's own (5.3.4.9) is recorded as broken. |
| #4251 | `sLocalIdelicZFunction_entire_iff_eq_polarFree` (3058) | Entire ⇔ equal on the chart to the transform of a polar-free test. | **C** — (⇐) is #4246 plus a congruence; (⇒) needs #4249, #4247, #4252 and Mellin glue, none proved. |
| #4252 | `sLocalIdelicZFunction_entire_iff_theta_exponentialDecay` (3068) | Entire ⇔ homogeneous theta lies in the all-exponent decay space of `Jₛ`. | **C** — Paley–Wiener in both directions; no lemma yet puts any theta function in a `ModulatedExponentialDecay` space. |
| #4263 | `sLocalPrincipalValue_homogeneousTheta_range_unramified` (4115) | The range of the homogeneous principal value is already the image of tests vanishing at zero at the unramified places. | **C+** — "⊆ image of Z_T" follows from the proved sibling `sLocalPrincipalValue_homogeneousTheta_range` (l.4052) and `Z_S ≤ Z_T`; the converse needs a unit-average operator at each ramified place and its compatibility with the homogeneous theta map. |

### Sec4.lean

| Issue | Declaration (line) | What must be proved | Grade |
|---|---|---|---|
| #4339 | `sLocalZetaPair_isClosedEmbedding` (379) | The zeta pair is a closed embedding `Θω → B⁺×B⁻`. | **C** — the Second Structure Theorem. |
| #4340 | `sLocalZetaPair_range` (384) | Range = matching pairs. | Covered by open PR #6190 (split); the surjectivity half is **C**. |
| #4349 | `sLocalPolarFreeZetaPair_isClosedEmbedding` (986) | Same for the polar-free quotient. | **C** — needs #4339 and a comparison of quotient topologies the paper does not supply (file TODO, p. 273). |
| #4351 | `existsUnique_sLocalThetaWeightedL2` (1043) | A unique continuous injection `Θₛ → L²(|g| dμ)` by a.e. class of the theta function. | **C** — uniqueness is immediate; existence needs a growth bound for the S-unit theta sum (log-power at 0, rapid decay at ∞) and continuity. The theta sum runs over S-units only, so the function is in L²; the statement is not false. |
| #4357 | `existsUnique_sLocalDecayFourier` (1194) | Fourier extends uniquely between weighted isotypes. | **C** — needs homogeneous theta functions to lie, densely, in the decay isotype. |
| #4358 | `existsUnique_sLocalDecayToThetaL2` (1208) | The decay space injects continuously into the theta L² completion. | **C** — needs the range to lie in the closure of theta classes. |
| #4359 | `sLocalDecayFourier_eq_weightedFourier` (1216) | The two Fourier extensions agree. | **C** — rests on #4354, #4357, #4358 and a density fact. |
| #4361 | `existsUnique_sLocalCechThetaPair` (1247) | A unique continuous map sending a class to the pair of homogeneous thetas of `f` and its Fourier transform. | **C** — uniqueness is immediate; existence needs `φω f ∈ Ẽ(Ioi 0)` continuously in `f`, which no lemma gives. |

No statement in the four files looks false or vacuous as stated.

### Sec5.lean

| Issue | Declaration (line) | What must be proved | Grade |
|---|---|---|---|
| #4394 | `sLocalThetaEigendistribution_holomorphic` (579) | The descended S-local eigendistribution family is holomorphic into the strong dual of the theta quotient. | **A** — see pick 2. |
| #4403 | `globalThetaEigendistribution_holomorphic` (712) | Same for the global family. | **A** — see pick 2. |

## Pick 1: #4159 `sLocalThetaPrincipalValue_toGlobal` (Sec3a.lean:1120)

Statement: `(sLocalThetaToGlobal F S).comp (sLocalThetaPrincipalValue F h₀) =
(globalThetaPrincipalValue F S₀).comp (sLocalThetaToGlobal F S)` for `h₀ : S₀ ⊆ S`. Used downstream
at `Ch06_LocalGlobal/Sec3.lean:1070`.

All three maps are `Submodule.mapQ`s (`sLocalThetaToGlobal`, `Sec2.lean:891`; the two principal
values, `Sec3a.lean:937, 944`), so the statement reduces to an identity of maps on test functions,
and that identity is already proved, privately, further up the import chain:
`adelePrincipalValue_mem_polarSubspace_toGlobal_comm` in
`$R/RiemannMasullo/Ch11_ShellStructure/Sec1b.lean:475–542`. Ch11 imports Ch05, so it has to be
ported, not imported. It uses only public declarations.

Steps (two private helpers directly above the theorem, inside `section AdelicPrincipalValue`, under
`open Classical in`):

1. `private theorem sLocalThetaPrincipalValue_toGlobal_tests (h₀ : S₀ ⊆ S) :
   (sAdeleSchwartzToGlobal F S).comp (sAdelePrincipalValue F h₀) =
   (adelePrincipalValue F S₀).comp (sAdeleSchwartzToGlobal F S)`.
   - `e := (sAdeleTailSchwartz_inductiveTensor_equiv F S).choose`, `he := ….choose_spec`
     (`Ch02_AdelicTheta/Sec1.lean:5805`): `e (f ⊗ₜ g) (ofAdd x) = f (ofAdd (adeleProjection F S x)) *
     g (ofAdd (finiteAdeleTailProjection F S x.2))`.
   - A test `k₀ : ℬₛ(S)` with `k₀ (ofAdd 0) = 1`. No public lemma gives one directly
     (`schwartzBruhat_exists_test` and `finiteAdeleTail_indicator` are private). Slice the global
     Gaussian: `G := adelicStandardGaussian (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F))`,
     `M : ℬₛ(S) ⊗[ℂ] Tl →ₗ[ℂ] ℬₛ(S) := TensorProduct.lift ((LinearMap.lsmul ℂ _).comp ev₀).flip`
     with `ev₀ b = b (ofAdd 0)`, `k₁ := M (e.symm G)`. Then `k₁ (ofAdd 0) = G (ofAdd 0)` by
     `TensorProduct.ext'` and `he a b 0` (`map_zero` for `adeleProjection`, `rfl` for the tail), and
     `G (ofAdd 0) ≠ 0` by `adelicStandardGaussian_trivial_zero` (`Ch03_IdelicZeta/Sec4.lean:1970`).
     `k₀ := (k₁ (ofAdd 0))⁻¹ • k₁`.
   - The tail indicator `c := L (e.symm (sAdeleSchwartzToGlobal F S k₀))` with
     `L := TensorProduct.lift ((LinearMap.lsmul ℂ Tl).comp ev)`, the facts `hc` (c is the indicator
     of the integral tail) and `hslice : e (a ⊗ₜ c) = sAdeleSchwartzToGlobal F S a`: lines 483–541
     of the Ch11 proof, which use `sAdeleSchwartzToGlobal_apply` (`Ch02_AdelicTheta/Sec1.lean`,
     public) and the definitional unfolding of `adeleProjection` and `finiteAdeleTailProjection`
     (both in `@[expose] public` sections).
   - Conclude: `LinearMap.ext k`, rewrite both sides with `hslice`, close with
     `adelePrincipalValue_tmul h₀ k c` (`Sec3a.lean:908`).
2. The theorem: `unfold sLocalThetaToGlobal sLocalThetaPrincipalValue globalThetaPrincipalValue`,
   `apply sLocalThetaPrincipalValue_transition_mapQ` (`Sec3a.lean:1098`, the abstract `mapQ`
   commutation already used for the sibling `sLocalThetaPrincipalValue_transition`),
   `exact sLocalThetaPrincipalValue_toGlobal_tests h₀`.

Dependencies that are still `sorry`: `adelePrincipalValue_tmul` (#4149) and the kernel-preservation
lemmas inside the definitions. `#print axioms` will show `sorryAx`; `prompts/prover.md` accepts
that, and the merged `globalThetaPrincipalValue_equivariant` (`Sec3a.lean:1244`) depends on
`adelePrincipalValue_tmul` in the same way.

Expected hard step: none mathematically. Elaboration risk is in step 1: the `rfl`/`dif_pos`/`dif_neg`
steps of the Ch11 proof must still go through in Sec3a (Ch11 has `open scoped Classical` file-wide
and an `import all` of `AppA_AlgebraicNT.Sec3`; neither should matter, since everything unfolded is
exposed). No new import is needed; PR #5855 died on an import line, so do not touch the import
block.

Collision: the neighbouring declaration `sLocalThetaPrincipalValue_equivariant` (#4160, l.1127) is
claimed by the automated runner, which inserts helpers above its own theorem; one unchanged line
separates the two hunks.

## Pick 2: #4394 + #4403 (Sec5.lean:579, 712)

Statements: `VectorHolomorphicOn (fun s ↦ sLocalThetaEigendistribution (chartₛ(χ) s)) univ` and
`VectorHolomorphicOn (fun s ↦ globalThetaEigendistribution (ideleClassNormTwist χ s)) univ`.
`VectorHolomorphicOn` is `DifferentiableOn ℂ` (`AppC_LCTVS/Sec5b.lean`).

The same file already has, above both targets, the tool that makes this assembly:
`sLocalNormalizedEigendistribution_holomorphic_pointwise` (private, `Sec5.lean:465`): on a Hausdorff
polynormable Montel space with complete polynormable strong dual, a family `T : ℂ → StrongDual ℂ E`
is holomorphic once `z ↦ T z x` is differentiable for every `x`. It needs no private lemma from
another file, which is what sank PR #5954.

Steps:

1. One private helper above `sLocalThetaEigendistribution_holomorphic`, stated for an abstract
   module `M` so that no instance of the theta quotient is compared (#5398):
   `(K : Submodule ℂ M) (T : ℂ → StrongDual ℂ M) (U : ℂ → StrongDual ℂ (M ⧸ K))
   (hU : ∀ z f, U z (K.mkQL f) = T z f) (hT : ∀ f, DifferentiableOn ℂ (fun z ↦ T z f) univ) (x : M ⧸ K) :
   DifferentiableOn ℂ (fun z ↦ U z x) univ`, by `obtain ⟨f, rfl⟩ := K.mkQ_surjective x` and
   `(hT f).congr fun z _ ↦ hU z f`. The file's existing `quotientLine` helpers use the same shape.
2. #4394: install the instances on `SLocalAdelicThetaSpace F S` exactly as the proved sibling
   `sLocalNormalizedEigendistribution_holomorphic` (l.484) does on `ℬ(Aₛ)`:
   `IsTopologicalAddGroup.rightUniformSpace _`, `isUniformAddGroup_of_addCommGroup`,
   `sLocalAdelicThetaSpace_nuclear.1` (T2) and `.2.1` (polynormable), `sLocalAdelicThetaSpace_montel`,
   `sLocalAdelicThetaSpace_strongDual_complete`, `sLocalAdelicThetaSpace_strongDual_nuclear.2.1`
   (all public, `Sec2.lean:122, 187, 198, 254`). Apply the pointwise lemma, then the helper with
   `hU := fun z f ↦ sLocalThetaEigendistribution_mk _ f` (l.544, `rfl`) and
   `hT f := (ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) f).differentiable.comp_differentiableOn
   (sLocalNormalizedEigendistribution_holomorphic χ)` (evaluation at `f` as a continuous functional
   on the strong dual, as in `ForMathlib/Analysis/LocallyConvex/StrongBidual.lean:82`). If that does
   not elaborate, copy the eight lines `he` of the sibling proof (l.494–501) with
   `sLocalNormalizedZFunction_entire f χ`.
3. #4403: the same with `globalAdelicThetaSpace_nuclear`, `globalAdelicThetaSpace_montel`,
   `globalAdelicThetaSpace_strongDual_complete`, `globalAdelicThetaSpace_strongDual_nuclear`
   (`Sec2.lean:116, 2703, 192, 2708`), `globalThetaEigendistribution_mk` (l.679) and
   `adelicNormalizedEigendistribution_holomorphic χ` (l.637).

Fallback for #4403 only, also with public lemmas: holomorphy descends through the closed embedding
`pull(K𝔽)` (`globalThetaQuotient_transpose_isEmbedding`, `Sec2.lean:2733`;
`globalThetaQuotient_transpose_isClosed_range`, `Sec2.lean:300`) by `vectorHolomorphicOn_iff_tendsto`.
This is the argument of PR #5954; its S-local half needs the private
`isEmbedding_transpose_quotient_of_strictLF` (`Sec2.lean:202`), so the pointwise route is the one
that works for both.

Expected hard step: instance and universe plumbing in step 2 (`IsNuclearTVS.{_, 0}`), nothing else.
`sorryAx` enters through `sLocalAdelicThetaSpace_strictLF` (#3916) and the eigendistribution
definitions.

Collision: Filimoa holds every other claim in the file, has eight open pull requests on it, proved
these two himself and was invited to resubmit. A second proof may arrive from him at any time.

## Pick 3: #4230 `complexArchimedeanMellin_existsUnique` (Sec3b.lean:1891)

Statement: for `f : 𝓢(ℂ, ℂ)`, `n : ℤ`, a unique `L` in meromorphic normal form on ℂ with
`HasMellin (complexProfile(f, n)) s (L s)` for `Re s > 0`, where
`complexProfile(f, n) t = ∫ θ in 0..2π, e^{inθ} f(√t e^{iθ})`.

The real sibling is proved from `realArchimedeanMellin_existsUnique_schwartz (G : 𝓢(ℝ, ℂ))`
(private, l.1837, above the target). Reduce to it:

1. `G(t) := ∫ θ in Ioo (-π) π, e^{inθ} f(t e^{iθ})` is a Schwartz function on ℝ. Smoothness and the
   derivative formula `deriv G_{g,r} = G_{∂g,r+1} + G_{∂̄g,r−1}` are proved privately in
   `Ch03_IdelicZeta/Sec3b.lean` (`angularProfile_smooth` l.2718 via `ContDiff.parametric_integral`,
   `directional_wirtinger` l.2907, `angularProfile_deriv` l.2922, with `holD`/`antiD` l.2868);
   port them under new names. Decay: `|t|^k ‖G_{g,r} t‖ ≤ 2π · SchwartzMap.seminorm ℝ k 0 g`
   because `‖t e^{iθ}‖ = |t|`; all derivatives by induction on the order with the derivative formula.
2. `mellin (complexProfile(f, n)) s = 2 * mellin G (2 s)` and convergence: `mellin_comp_rpow`,
   `MellinConvergent.comp_rpow` (Mathlib `Analysis/MellinTransform.lean:115, 74`). The identity is
   proved at l.2375 (`complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_change`), below the
   target; duplicate it above under a new name.
3. With `L_G` from the real theorem, take `L := toMeromorphicNFOn (fun s ↦ 2 * L_G (2 * s)) univ`
   (`MeromorphicAt.comp_analyticAt`, Mathlib `Analysis/Meromorphic/Basic.lean:442`), and repeat the
   last ten lines of the real proof (l.1848–1860): normal form, value on `Re s > 0` through
   analyticity there, uniqueness by `realArchimedeanMellin_existsUnique_eqNF` (l.1822).

Expected hard step: step 1, building the `SchwartzMap` (all-order derivative bounds for a
parametric integral). Everything else is plumbing that exists in the file.

Collision: Sec3b has six claimants and five open pull requests; the nearest claimed declarations
(#4223 l.1588, #4235 l.2560) are far from l.1650–1895.

## Reusable

- A label without `claimed` does not mean untouched. `gh api repos/mccorvie/riemann-masullo/issues/<n>/timeline`
  shows cross-referenced pull requests; a closed, unmerged PR that built is the strongest signal
  that an issue is tractable, and its closing comment says what to avoid.
- Open pull requests cover issues without labelling them: check
  `gh pr list --state open --json number,title,files,body` for `Closes #<n>` and for the file.
- The merger closes any pull request whose conflict or check feedback is unanswered for four hours,
  and refuses any new `import all` line (#6103). Both recent A-grade proofs in these files were
  lost that way. A proof should add no import and no `import all`; if a private lemma of another
  file is needed, making it public there in the same PR is allowed but waits for a human reader.
- Declaration order blocks proofs: a theorem cannot use a sibling proved later in the same file
  (#4167, #4192, and the `_change` lemma for #4230), and the rules forbid reordering.
- Lemmas wanted in a lower file often already exist as private lemmas in a higher chapter
  (Ch11 for #4159, Ch03 for #4230): grep the whole library for the conclusion before writing it.
- State quotient-space steps for an abstract module `M ⧸ K` and then apply them (#5398); naming a
  representative of a theta class directly has timed out for others (comment on #4350).
- Saved material: `01-scout-ch05/issues/pr5855.diff`, `pr5954.diff` (the two closed proofs, other
  contributors' work), and the comments of the eight issues that had any.
