# Priority 1: independence of exponential polynomials t^j e^{zt}

## Answer

Not in Mathlib v4.36.0 (local grep: no `LinearIndependent` statement about `Complex.exp`/`cexp`, no
"exponential polynomial" development). But a ready, sorry-free, same-pin proof of the discrete form exists:

**`LeanPool.StrongSix.M2.expPoly_indep`** in `LeanPool/lean-pool`
(https://github.com/LeanPool/lean-pool), file `LeanPool/RoyStrongSix/M2/ExpPoly.lean`,
last changed in commit `5dd712603d49049c7a5198e5dd725f768c5a510b` (repo HEAD `de53f08745423586a7dd5aa5be8c00016cb6e8c3`
on 2026-11-23). Licence **Apache-2.0** (header: Copyright (c) 2026 Shawn Krisman). Toolchain
`leanprover/lean4:v4.36.0`, Mathlib `inputRev v4.36.0` -- **the same pin as riemann-masullo**, so it
should paste in unchanged (it is a `module` file with `public import`s and `@[expose] public section`).
Verified by reading the file (0 `sorry`); not compiled here.

```lean
variable {K : Type*} [Field K] [CharZero K]
theorem expPoly_indep (R : Finset K) (h0 : ∀ ρ ∈ R, ρ ≠ 0) :
    ∀ Q : K → K[X], (∀ n : ℕ, ∑ ρ ∈ R, (Q ρ).eval (n : K) * ρ ^ n = 0) → ∀ ρ ∈ R, Q ρ = 0
```

Self-contained: needs only its helpers `pw`, `pw_zero`, `pw_of_ne`, `shift_natDegree`,
`shift_leadingCoeff`, `shift_ne_zero`, `pw_shift_sub_lt`, `pw_twist_le`, `eq_zero_of_eval_nat`
(lines 1-160 of the file, ~110 lines of proof). Proof: strong induction on Σ(deg Q_ρ + 1) applying
f(n) ↦ f(n+1) − ρ₀ f(n). Record it in `External/ATTRIBUTION.md` (Apache-2.0).

## Reduction from the continuous statement (Σ_z P_z(t) e^{zt} = 0 for all real t)

1. Pick real h > 0 with z ↦ exp(h z) injective on the finite set S of exponents. E.g.
   h = 1 / (1 + Σ_{z,z'∈S} ‖z − z'‖): if exp(hz) = exp(hz') then by `Complex.exp_eq_exp_iff_exists_int`
   h(z − z') = n·2πi; n = 0 gives z = z', n ≠ 0 gives 2π ≤ |n|·2π = h‖z−z'‖ < 1, contradiction.
2. Put ρ_z = exp(h z) (nonzero, `Complex.exp_ne_zero`), Q_z = (P_z).comp (C (h:ℂ) * X).
   At t = n·h: (Q_z).eval n * ρ_z^n = P_z(n h) * exp(z n h) (`Polynomial.eval_comp`, `eval_mul`,
   `eval_C`, `eval_X`, `← Complex.exp_nat_mul`). Reindex the sum over `S.image (fun z => exp (h*z))`
   with `Finset.sum_image` (injectivity from step 1), defining Q on ρ via `Function.invFunOn` or
   by summing over S directly after a small restatement.
3. `expPoly_indep` gives Q_z = 0; then `Polynomial.comp_C_mul_X_eq_zero_iff` (needs (h:ℂ) ∈
   nonZeroDivisors ℂ, i.e. h ≠ 0) gives P_z = 0.
   For linear independence of the family (z, j) ↦ (t ↦ t^j * exp(z t)): a vanishing finite
   combination Σ c_{z,j} t^j e^{zt} is the case P_z = Σ_j c_{z,j} X^j; coefficients from
   `Polynomial.coeff` of P_z = 0. Use `linearIndependent_iff'` / `Fintype.linearIndependent_iff`.

## Alternative Mathlib-only route (if not porting)

Generalized eigenspaces of the ℂ-linear shift T f = f(· + h) on (ℝ → ℂ) (build with
`LinearMap.funLeft ℂ ℂ (· + h)`): t^j e^{zt} ∈ `Module.End.genEigenspace T (exp (h z)) (j+1)`, and
`Module.End.independent_genEigenspace` / `independent_maxGenEigenspace`
(Mathlib/LinearAlgebra/Eigenspace/Basic.lean:692,732) with `iSupIndep.dfinsupp_lsum_injective`
or `iSupIndep.linearIndependent` (Mathlib/LinearAlgebra/DFinsupp.lean:546,640). The degree drop uses
`Polynomial.fwdDiff_iter_eq_zero_of_degree_lt` (Mathlib/Algebra/Group/ForwardDiff.lean:268), which
is stated for step 1 on R → R, so rescale t = h s first. More glue than the port; prefer the port.

Other building blocks (verified names): `linearIndependent_monoidHom`
(LinearAlgebra/LinearIndependent/Basic.lean:516; Dedekind, handles only j = 0, needs a monoid hom
into a field), `AddChar.linearIndependent` (Analysis/Fourier/FiniteAbelian/Orthogonality.lean:74,
finite groups only -- not usable), `Polynomial.eq_zero_of_infinite_isRoot` (Roots.lean:170),
`Polynomial.funext` (Roots.lean:486), `Module.End.eigenvectors_linearIndependent'`.

## Side note (tooling): cold clone without the 45-minute build

The project's own `Main state` workflow uploads `.lake/build` of main as the artifact `main-state`
(~370 MB zstd, retention 1 day, one per push to main; 115 present on 2026-11-23, newest 08:03Z).
`scripts/ci/base_state.py` restores it: after `lake exe cache get`, run
`GH_TOKEN=$(gh auth token) GH_REPO=mccorvie/riemann-masullo REPO_ID=1465783492 python3 scripts/ci/base_state.py --work . --base <sha of main checked out> --out ./tmp/base-state`
(read-only GitHub API use). It unpacks into `./.lake/build`; Lake then rebuilds only changed modules.
