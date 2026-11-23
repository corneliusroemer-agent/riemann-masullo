# Scout 02: Ch07 Sec2, Sec3a, Sec3b, Sec4, Sec5

`$R` = `<repo>`,
`$C` = `$R/RiemannMasullo/Ch07_SchauderBasesZeta`. Line numbers are those of the checkout.

## Result

One grade-A issue: **#4774 `sLocalGammaOrbitalQuotient_dual_directSum`** (`$C/Sec3b.lean:2647`). It is
pure assembly of proved, public lemmas, and `archNuclearityStrongDual_finest` (`$C/Sec4.lean:1191`) is
a compiled proof of the same shape to copy from. One grade B: **#5110 `archNuclearityAction_nuclear_iff`**
(`$C/Sec4.lean:1529`). Everything else is C.

## Label state and crowding

All 37 issues named in the prompt are still free in `.agent/proof-issues.jsonl`. Two are free by label
but in practice taken or stale:

- #5128 (Sec5) has open PR #6183 (cobalt8814, a split). Treat as taken.
- Sec4 has open PR #6120 (CalebAlbers), which closes #5081/#5082 and adds many private helpers to
  `Sec4.lean`; its author left "stuck" notes on #5080 #5083 #5088 #5090 #5094.

| File | free | `claimed` on other issues of the file | open PR on the file |
|---|---|---|---|
| Sec2.lean | 2 | 2 (#4555 #4557) | none |
| Sec3a.lean | 6 | 5 (#4594 #4595 #4604 #4612 #4614) | #5996 (closes four of them) |
| Sec3b.lean | 10 | 6 (#4741 #4742 #4748 #4753 #6095 #6096), all in lines 259-1070 | none |
| Sec4.lean | 14 | 3 (#5081 #5082 #5086) | #6120 |
| Sec5.lean | 5 | 2 (#5147 #5148) | #6183 |

The `_Printed.lean` files are separate modules; almost all of their issues are claimed (free: #5114,
#5150, both heavy explicit counterexamples, grade C).

## Grades

### Sec2.lean
- #4554 `sLocalPrincipalValue_tfae` (2374): four-way equivalence between vanishing of selected local
  Laurent coefficients, a global zero-order bound, and membership in the local and the global
  principal-value image. **C.** (1)<->(3) is the content of #6115 (stated later, in Sec3a, so not
  usable here); (2) and (4) are global and need the converse theorems of Ch06 Sec3. 0 comments.
- #4558 `sLocalPolarPrincipalValue_tfae` (2432): the same on the zero-moment subspace. **C.**

### Sec3a.lean
- #6115 `sLocalThetaPoleBound_le_orbitalPrincipalValue` (399): a theta class whose zeta has the
  reduced pole bound is a principal value. **C.** Needs division by Euler factors inside the Mellin
  image, i.e. a description of that image; nothing in the library gives it.
- #6117 `exists_sLocalOrbitalPrincipalPart_dual` (551): for each index a class with coefficient 1
  there and 0 at all (infinitely many) others. **C.** Simultaneous interpolation.
- #4606 `sLocalPolarOrbital_bases_of_laurent_bounds` (1527), #4607 `sLocalFourierOrbital_bases`
  (1549): Schauder bases of the primary quotient and its dual. **C.**
- #4608 `sLocalFourierOrbital_biorthogonal_growth` (1575): polynomial growth of biorthogonal
  vectors. **C.**
- #4609 `sLocalOrbitalFourierJet_lattice_schwartz` (1595): Fourier jets along a pole lattice form a
  Schwartz sequence. **C.** Needs vertical decay of derivatives of the zeta transform.

### Sec3b.lean
- **#4774 `sLocalGammaOrbitalQuotient_dual_directSum` (2647): A.** See pick 1.
- #4768 `sLocalGammaFiltration_coeff_independent` (1754): finitely many archimedean Laurent
  coefficient functionals, linearly independent. **B-/C.** See pick 3.
- #4771 `sLocalGamma_all_coeff_surjective` (2379): every array of coefficients is realised. **C.**
  Borel/Mittag-Leffler; the released note reduces it to a step as hard as the target.
- #4740 `sLocalAbsolutePW_seqDense` (429): band-limited inserted tests are sequentially dense in the
  theta space. **C.** Needs the stage isomorphism of 6.2 and density of band-limited tests under the
  zero-moment constraint. (`sLocalInvariantPW_seqDense` is proved from it.)
- #4751 `sLocalAbsolutePW_principalValue` (1026), #4752 `sLocalInvariantPW_principalValue` (1038):
  PV maps level X into level size(R)*X. **C.** The natural proof writes PV on an inserted test as an
  alternating sum of uniformizer translates and reuses `sLocalAbsolutePW_translate_level` (545); the
  library has no such formula for `sAdelePrincipalValue` (defined through tensor equivalences and a
  unit average), and the translate lemma only covers norm >= 1.
- #4755 `sLocalPWOrbital_eventually_equiv`, #4756 `sLocalPWOrbital_bases`,
  #4757 `sLocalPWOrbital_biorthogonal_growth`, #4758 `sLocalPWOrbital_fourier_decay` (1156-1244):
  **C.** #4758 is #4609 without its saturation and Picard hypotheses, so #4609 cannot be applied.

### Sec4.lean
- **#5110 `archNuclearityAction_nuclear_iff` (1529): B.** See pick 2.
- #5100 `archNuclearityJet_basis` (1003): the jet index is countably infinite and every enumeration
  gives a Schauder basis of the dual. **C** as placed: the basis half is the pattern of
  `sLocalGammaOrbitalQuotient_dual_basis_pi` applied to `archNuclearityQuotient_jetEquiv`, but that
  theorem is declared later (1158); the enumeration needs infinitely many gamma poles.
- #5080 isotype model (387), #5083 spectral trace (438), #5084 `exists_polarThetaNuclearityAction`
  (465), #5088 finite denominator closed/invariant (568), #5089 finite trace (580), #5090
  `globalArchimedeanFlatTests_isClosed` (628), #5092 flat/polar image (692), #5094 denominator
  nonzero and closed (749), #5099 `archNuclearityJet_span` (995), #5103 Mellin range (1151), #5104
  `archNuclearityQuotient_jetEquiv` (1158), #5107 `archNuclearity_trace` (1286): **C.** Paley-Wiener
  isomorphisms, zero counting, closedness in inductive tensor topologies, interpolation. The released
  notes on #5080 #5083 #5088 #5090 #5092 #5094 each name a missing fact.

### Sec5.lean
- #5128 `exists_strongCoprimalityThetaEmbedding` (73): taken by PR #6183.
- #5134 `strongCoprimality` (319), #5138 `exists_strongCoprimalityFourierJet_full` (533), #5146
  `strongCoprimalityPrimaryQuotient_local_equiv` (1458), #5149 `strongCoprimality_bezout` (1507):
  **C.** #5149 is a Bezout identity in the Schwartz-Bergman space with interpolation on the zeros of
  the Euler polynomial. The comment on #5149 that the Lean differs from (7.5.0.17) is mistaken:
  `reciprocalPartialHeckeEulerProduct` (`AppB_AnalyticNT/Sec5.lean:1365`) is the product of
  `(finiteHeckeEulerFactor)⁻¹`, and `finiteHeckeEulerFactor` (`Ch03_IdelicZeta/Sec2.lean:109`) is
  `(1 - chi q^-s)⁻¹`, so the Lean factor is the printed polynomial.

No statement in these files looked false or vacuous (no F).

## Pick 1: #4774 `sLocalGammaOrbitalQuotient_dual_directSum` (Sec3b.lean:2647), grade A

Statement: `Nonempty (StrongDual ℂ (E ⧸ P) ≃L[ℂ] FinestLocallyConvex (depths →₀ ℂ))` with
`E = fullPV(ω)`, `P = Γker(ω)`, `depths = InfinitePlace F → ℕ`.

All ingredients exist, are public and visible from Sec3b (checked by a public-import walk):

- `sLocalGammaOrbitalQuotient_product ω` (Sec3b.lean:2627, proved, directly above):
  `Nonempty ((E ⧸ P) ≃L[ℂ] (depths → ℂ))`.
- `realSchwartzTaylor_equiv` (`Ch05_ThetaZSpaces/Sec3a.lean:1874`, proved):
  `(𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) ≃L[ℂ] PowerSeries ℂ`.
- `realDiracDerivatives_polynomialEquiv` (same file, 2022, proved):
  `FinestLocallyConvex (Polynomial ℂ) ≃L[ℂ] StrongDual ℂ (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin)`.
- `ContinuousLinearEquiv.arrowCongr` (Mathlib `Topology/Algebra/Module/Spaces/ContinuousLinearMap.lean:546`,
  no normed-space assumption) and `ContinuousLinearEquiv.piCongrLeft` (`.../Module/Equiv/Pi.lean:59`).
- `continuous_of_finestLocallyConvex`, `finestLocallyConvex_t2` (`AppC_LCTVS/Sec2b.lean:4811, 4785`).

Template: `archNuclearityStrongDual_finest` and its helper `archNuclearityStrongDual_finest_of_equiv`
(`Sec4.lean:1164-1203`) build `FinestLocallyConvex (Polynomial ℂ) ≃L StrongDual ℂ Q` from a
`Q ≃L (ℕ → ℂ)` in eight lines. They are in a later file, so copy the lines, do not call them.

Steps:

1. Private helper directly above the theorem, over an abstract space with every binder written out:
   `{Q ι : Type*} [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q] (Ψ : Q ≃L[ℂ] (ι → ℂ)) (σ : ℕ ≃ ι) :
   Nonempty (StrongDual ℂ Q ≃L[ℂ] FinestLocallyConvex (ι →₀ ℂ))`. If applying it to the concrete
   quotient is slow, restate it for `E ⧸ P` with `{_ : AddCommGroup E} {_ : Module ℂ E}
   {_ : TopologicalSpace E} (P : Submodule ℂ E)`, as `sLocalGammaOrbitalQuotient_dual_basis_quot`
   (2740) does.
2. In the helper: `q := Ψ.trans (piCongrLeft ℂ (fun _ : ℕ ↦ ℂ) σ.symm) : Q ≃L (ℕ → ℂ)`; then lines
   1196-1201 of Sec4 verbatim (`t`, `p`, the `let : TopologicalSpace (PowerSeries ℂ)`, `idx`,
   `series`, `e := (q.trans series).trans t.symm`); `d := p.trans (e.symm.arrowCongr (refl ℂ ℂ)) :
   FinestLocallyConvex (Polynomial ℂ) ≃L StrongDual ℂ Q`.
3. `l : Polynomial ℂ ≃ₗ[ℂ] (ι →₀ ℂ) := (AddMonoidAlgebra.coeffLinearEquiv ℂ).trans (Finsupp.domLCongr σ)`.
   In this Mathlib `R[X]` is `R[ℕ]` (`Polynomial.toFinsuppIsoLinear` is `.refl`, deprecated as a
   tautology) and `AddMonoidAlgebra` is a structure with `coeffLinearEquiv`
   (`Algebra/MonoidAlgebra/Module.lean:73`). `Polynomial.basisMonomials` is not visible from Sec3b.
4. Turn `l` into `FinestLocallyConvex (Polynomial ℂ) ≃L FinestLocallyConvex (ι →₀ ℂ)`: both
   directions are continuous by `continuous_of_finestLocallyConvex` after
   `let := finestLocallyConvex_t2 _` for both spaces (exactly `Sec4.lean:1168-1173`).
5. Result `d.symm.trans (that equivalence)`.
6. Main theorem: `intro E P; obtain ⟨Ψ⟩ := sLocalGammaOrbitalQuotient_product ω`, the two
   `Encodable.ofCountable depths` / `Denumerable.ofEncodableOfInfinite depths` lines from 2637-2638,
   `exact helper Ψ (Denumerable.eqv depths).symm`.

Expected hard step: none mathematical. Risks are elaboration only: the `Polynomial`/`AddMonoidAlgebra`
coercion in step 3 (fallback: a hand-written `LinearEquiv`, or a non-public
`import Mathlib.Algebra.Polynomial.Basis`), and unification against the concrete quotient in step 6.
`#print axioms` will show `sorryAx` through `sLocalGammaOrbitalQuotient_product` ->
`sLocalGamma_all_coeff_surjective` (#4771), which the rules accept.

The released attempt on the issue tried a direct proof (bounding a strong-dual neighbourhood by a
supremum over a bounded box) and did not use the Schwartz/Dirac equivalences.

Collision: the edit is confined to lines ~2643-2650; the six claimed issues of the file are in lines
259-1070 and no PR is open on the file.

## Pick 2: #5110 `archNuclearityAction_nuclear_iff` (Sec4.lean:1529), grade B

Statement: for `T` on `Q = ArchNuclearityQuotient χ` induced by the test action `Aθ(φ)`,
`Nonempty (NuclearPresentation T) ↔ {z | ∃ k : Fin (archNuclearityMultiplicity χ τ hτ z),
iteratedDeriv k (nuclearityTestMellin χ φ) z ≠ 0}.Finite`.

Ingredients, all in the same file above the theorem:

- `archNuclearityQuotient_nuclear_iff_finiteRank` (1517, proved): nuclear presentation <-> finite
  rank. Its `letI` is the same `IsTopologicalAddGroup.rightUniformSpace Q`.
- `archNuclearityQuotient_jetEquiv χ τ hτ` (1158, sorry, #5104): `e : Q ≃L (J → ℂ)` with
  `e (mk x) j = archNuclearityJet j x`.
- `(exists_polarThetaNuclearityAction χ τ hτ φ).choose_spec.1` (465, sorry, #5084):
  `Z (Aθ x) s = M s * Z x s`, `M = nuclearityTestMellin χ φ`.
- `archNuclearityDenominator_closed_invariant_multiplier χ φ : Differentiable ℂ M` (1208, private).
- The `hjet`, `hprod`, `iteratedDeriv_mul` block of `archNuclearityDenominator_closed_invariant`
  (1245-1273), which already computes `jet (z,k) (Aθ x) = Σ_{i ≤ k} C(k,i) M^(i)(z) · jet (z,k-i) x`.
- Mathlib: `iteratedDeriv_mul` (`Analysis/Calculus/IteratedDeriv/Lemmas.lean:418`),
  `LinearIndependent.finite` (`LinearAlgebra/Dimension/Finite.lean`), `linearIndependent_iff'`.

Steps:

1. Rewrite the left side with `archNuclearityQuotient_nuclear_iff_finiteRank`.
2. Coordinate formula (*): `e (T (mk x)) ⟨(z,k),_⟩ = Σ_{i ∈ range (k+1)} C(k,i) * M^(i)(z) *
   iteratedDeriv (k-i) (Z x).val z`, and `e (mk x) ⟨(z,k),_⟩ = iteratedDeriv k (Z x).val z`.
3. State the linear algebra as a private lemma over abstract spaces (a surjection `mk : Θ →ₗ Q`, a
   linear equivalence `e : Q ≃ₗ (J → ℂ)`, coefficients `a i z`, the formula (*)):
   `FiniteDimensional ℂ (range T) ↔ {z | ∃ k : Fin (m z), a k z ≠ 0}.Finite`.
   - `<-`: with `S` the finite set, `e (T y) j = 0` when `j.1 ∉ S` (every `i ≤ j.2 < m j.1` has
     `a i j.1 = 0`). `{j : J // j.1 ∈ S}` is finite, restriction to it is injective on `range T`,
     so `FiniteDimensional.of_injective`.
   - `->`: if `S` is infinite, pick for `z ∈ S` an order `k_z` with `a k_z z ≠ 0` and `x_z` with
     `e (mk x_z) = Pi.single ⟨(z,0),_⟩ 1`. By (*), `e (T (mk x_z))` vanishes off the block of `z`
     and equals `a k_z z ≠ 0` at `(z,k_z)` (only `i = k` survives). Evaluating a vanishing finite
     combination at `(z₀,k_{z₀})` gives linear independence; `LinearIndependent.finite` contradicts
     `S.Infinite`.
4. Instantiate.

Expected hard step: step 3 `->` (the dependent index `⟨(z,k-i),_⟩` and the `Pi.single` bookkeeping),
about 100-150 lines in all. The result rests on three sorries (#5104, #5084, and #5100 through the
finite-rank theorem). Collision: PR #6120 adds helpers for the spectral section (around 402) and the archimedean jets and regularized L (973-1140); #5110 is the last
declaration of the file.

## Pick 3: #4768 `sLocalGammaFiltration_coeff_independent` (Sec3b.lean:1754), grade B-/C, stretch

Not a few-hours job; listed because the two lemmas the released attempt reported missing exist.

- `Finite` half: proved inline in `sLocalGammaFiltration_dual_span` (1968; `hU_fin`, `hι_fin`); lift it.
- Independence: `exists_sLocalIdelicZFunction_principalValue_attaining_poles χ`
  (`Ch05_ThetaZSpaces/Sec3b.lean:3877`, proved) gives one test whose principal value has the exact
  archimedean pole order at every centre of the component.
  `sLocalPrincipalPartCoeff_translate` (`Sec2.lean:529`, proved) gives the coefficients of a
  translate: `c g * Σ_j Coeff(c, k+j) f * (log ‖g‖)^j / j!`. `sLocalThetaPrincipalValue_equivariant`
  (`Ch05_ThetaZSpaces/Sec3a.lean:1127`, sorry) keeps translates inside the principal-value range.
  Applying a vanishing combination to translates along a one-parameter norm section gives
  `Σ_c e^{t s_c} P_c(t) = 0` for all real `t`, with distinct `s_c`; the leading coefficient of `P_c`
  is `a_{c,K} · (nonzero top coefficient)`.
- Missing: linear independence of `t ↦ t^j e^{s t}` for distinct complex `s` (neither in Mathlib nor
  in the project), and the passage of the equivariance from `Θₛ(S)` to the homogeneous quotient.

## Reusable

- `StrongDual ℂ (ℕ → ℂ) ≃L FinestLocallyConvex (Polynomial ℂ)` is available without new analysis by
  composing `realSchwartzTaylor_equiv` and `realDiracDerivatives_polynomialEquiv` (Ch05 Sec3a) with
  `ContinuousLinearEquiv.arrowCongr`; `Sec4.lean:1191-1203` is the compiled model. Any "strong dual of
  a countable product is the finest direct sum" statement reduces to it.
- `finestStrongDualEquiv` (`AppC_LCTVS/Sec2b.lean:5194`, `StrongDual ℂ (FinestLocallyConvex E) ≃L
  (basis index → ℂ)`) is `private`; `finestLocallyConvex_strongBidual` (5183) is public.
- In this Mathlib pin `Polynomial R` is `AddMonoidAlgebra R ℕ` and `AddMonoidAlgebra` is a structure;
  use `AddMonoidAlgebra.coeffLinearEquiv`, not `toFinsuppIsoLinear` (deprecated).
- A `free` label is not enough: #5128 has an open PR. Check `gh pr list` for the file before claiming.
- Theorems can only use what is declared above them; several "follows from a sibling" candidates
  fail on order alone (#5100 vs `archNuclearityQuotient_jetEquiv`, #4768 vs
  `sLocalGamma_all_coeff_surjective`).
- Scripts in `02-scout-ch07/`: `sorries.py FILE` prints every sorry'd declaration with its docstring;
  `reach.py ROOT START TARGET...` and `reach_all.py` (also walks `.lake/packages`) report whether a
  module is visible from another through direct plus transitive public imports.
