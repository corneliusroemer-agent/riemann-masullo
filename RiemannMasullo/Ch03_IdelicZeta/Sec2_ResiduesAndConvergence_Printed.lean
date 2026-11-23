module

public import RiemannMasullo.Ch03_IdelicZeta.Sec2
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Chapter 3.2: printed residues and absolute convergence -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Filter MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "ℬ[" F "]" => SchwartzBruhat (Multiplicative 𝔸[F])

local instance printedCh03Sec2ResiduesIdeleMeasurableSpace
    (F : Type) [Field F] [NumberField F] : MeasurableSpace 𝕀[F] := borel _

local instance printedCh03Sec2ResiduesClassMeasurableSpace
    (F : Type) [Field F] [NumberField F] : MeasurableSpace C[F] := borel _

/-- Paper: Proposition 3.2.1.3(2), p. 123. As printed: for every number field and
every character χ trivial on the norm-one classes, write χ = |·|^(-it).
The residues of the Hecke L-function at it and 1 + it are minus the norm-one
class volume and that volume divided by the square root of the absolute norm
of the different, respectively. This is the residue clause of
`completedHeckeL_continuation_simplePoles`. See ERRATA F209. -/
def Printed.completedHeckeL_residues : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C[F]),
    χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 →
    ∀ (L : ℂ → ℂ), MeromorphicNFOn L univ →
      (∀ s : Complex.re ⁻¹' Ioi (1 : ℝ), L s = completedHeckeL χ s) →
      ∀ (t : ℝ),
        ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : PontryaginDual C[F])
          (-Complex.I * (t : ℂ)) →
        let z := Complex.I * (t : ℂ)
        let m : ℝ := (normOneIdeleClassTamagawaMeasure F univ).toReal
        let d : ℝ := (differentIdeal ℤ (𝓞 F)).absNorm
        Tendsto (fun s : ℂ ↦ (s - z) * L s) (𝓝[≠] z) (𝓝 (-(m : ℂ))) ∧
          Tendsto (fun s : ℂ ↦ (s - (1 + z)) * L s) (𝓝[≠] (1 + z))
            (𝓝 ((d ^ (-(1 / 2) : ℝ) * m : ℝ) : ℂ))

/-- Paper: Proposition 3.2.1.3(2), p. 123. Take F = ℚ(√5), χ = 1, t = 0 and
φ = (1 + √5)/2. The norm-one class volume is 2 log φ/√5. For the product
π^(-s) Γ(s/2)² ζ_F(s), the class number formulas give residues −2 log φ at 0
and 2 log φ/√5 at 1. The printed values are −2 log φ/√5 and 2 log φ/5. -/
theorem Printed.completedHeckeL_residues_false :
    ¬ Printed.completedHeckeL_residues := by sorry

/-- Paper: Theorem 3.2.2.1(2)(b), p. 125. As printed: for every number field
and every adelic Schwartz–Bruhat function, the theta Mellin integral (3.2.2.3)
converges absolutely at every quasi-character on a nontrivial norm-one
component. This is the pointwise absolute convergence clause. See
`globalIdelicZFunction_entire_of_nontrivial` and ERRATA F210. -/
def Printed.globalThetaMellinIntegral_integrable_of_nontrivial : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (f : ℬ[F]) (χ : PontryaginDual C[F]),
    χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1 →
    ∀ s : ℂ, Integrable (fun g : C[F] ↦ adelicTheta f g * ideleClassNormTwist χ s g)
      (ideleClassTamagawaMeasure F)

/-- Paper: Theorem 3.2.2.1(2)(b), p. 125. Take F = ℚ, the standard Gaussian
at infinity, the indicator of ℤ̂ at the finite places, and χ induced by the
quadratic Dirichlet character of conductor 5. At s = 0 the character has modulus
one and takes the value −1 at the norm-one idele with component 2 at 5 and 1
elsewhere. At norm t, the theta sum is
Σ_{n ≠ 0} exp(−πn²t²) ∼ 1/t as t tends to zero, so its integral against dt/t diverges. -/
theorem Printed.globalThetaMellinIntegral_integrable_of_nontrivial_false :
    ¬ Printed.globalThetaMellinIntegral_integrable_of_nontrivial := by sorry

/-- Paper: Remark 3.2.2.2, p. 125. As printed: the domain of each truncated
idele integral with norm in [1/n, n] is compact. This is the compactness
assertion used to justify holomorphy. See `globalIdelicZetaIntegral_normBand_entire`
and ERRATA F210. -/
def Printed.ideleNormBand_isCompact : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 1 ≤ n →
    IsCompact (ideleNormBand F (n : ℝ)⁻¹ (n : ℝ))

open IsDedekindDomain Rat in
/-- Paper: Remark 3.2.2.2, p. 125. For F = ℚ and n = 2, the norm band contains every
principal idele (2^k). The 2-adic norm at that place is a continuous map sending the
band into ℝ; it sends the principal ideles to ‖2‖^k with 0 < ‖2‖ < 1, which tends to 0.
A compact image would be closed and thus contain 0, but the norm of the component of a
unit is strictly positive. -/
theorem Printed.ideleNormBand_isCompact_false :
    ¬ Printed.ideleNormBand_isCompact := by
  intro hband
  obtain hD : IsCompact (ideleNormBand ℚ (2 : ℝ)⁻¹ 2) := hband (F := ℚ) (n := 2) (by norm_num)
  -- The place of ℚ above 2: its natural generator is 2.
  obtain ⟨v₂, hv₂gen⟩ : ∃ v : HeightOneSpectrum (𝓞 ℚ), HeightOneSpectrum.natGenerator v = 2 :=
    ⟨HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) |>.symm ⟨2, Nat.prime_two⟩, by
      exact congrArg Subtype.val
        ((HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨2, Nat.prime_two⟩)⟩
  obtain ⟨r, hrmem, hrint⟩ :
      ∃ r : 𝓞 ℚ, r ∈ v₂.asIdeal ∧ IsIntegralClosure.intEquiv (𝓞 ℚ) r = (2 : ℤ) := by
    have h2 : (2 : ℤ) ∈ v₂.asIdeal.map (IsIntegralClosure.intEquiv (𝓞 ℚ)) := by
      rw [← HeightOneSpectrum.span_natGenerator v₂, hv₂gen]
      exact Ideal.mem_span_singleton_self 2
    exact Ideal.mem_map_iff_of_surjective
      (IsIntegralClosure.intEquiv (𝓞 ℚ)).toRingHom (RingEquiv.surjective _) |>.mp h2
  have hrq : (r : ℚ) = 2 := by
    rw [show (r : ℚ) = algebraMap (𝓞 ℚ) ℚ r from rfl, ← Rat.ringOfIntegersEquiv_apply_coe,
      ← Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv, hrint]
    rfl
  have hv2lt : v₂.valuation ℚ (r : ℚ) < 1 := by
    rw [show (r : ℚ) = algebraMap (𝓞 ℚ) ℚ r from rfl,
      HeightOneSpectrum.valuation_lt_one_iff_mem v₂ r]
    exact hrmem
  rw [hrq] at hv2lt
  -- The two coercion instances of ℚ into the completion agree with the embedding.
  have hbrM : ∀ x : ℚ, ((x : ℚ) : v₂.adicCompletion ℚ) =
      (FinitePlace.embedding v₂) x := by
    intro x
    simp
  -- The 2-adic norm at that place: continuous, positive on ideles, smaller than 1 on 2.
  have hval : Valued.v ((2 : ℚ) : v₂.adicCompletion ℚ) < 1 := by
    rw [hbrM 2]
    calc Valued.v ((FinitePlace.embedding v₂) (2 : ℚ)) = v₂.valuation ℚ 2 :=
          HeightOneSpectrum.adicCompletion.valued_coe (K := ℚ) (v := v₂) (2 : ℚ)
      _ < 1 := hv2lt
  have h2lt : ‖((2 : ℚ) : v₂.adicCompletion ℚ)‖ < 1 :=
    Valued.toNormedField.norm_lt_one_iff.mpr hval
  have h2pos : 0 < ‖((2 : ℚ) : v₂.adicCompletion ℚ)‖ := by
    rw [hbrM 2, FinitePlace.norm_embedding]
    exact (HeightOneSpectrum.adicAbv ℚ v₂).pos two_ne_zero
  set φ : IdeleGroup (𝓞 ℚ) ℚ → ℝ := fun g ↦ ‖(g.val.2 v₂ : v₂.adicCompletion ℚ)‖ with hφdef
  have hφcont : Continuous φ := by
    have h1 : Continuous fun x : AdeleRing (𝓞 ℚ) ℚ ↦ (x.2 v₂ : v₂.adicCompletion ℚ) :=
      (RestrictedProduct.continuous_eval v₂).comp continuous_snd
    exact (continuous_norm.comp h1).comp Units.continuous_val
  have himg : IsCompact (φ '' (ideleNormBand ℚ (2 : ℝ)⁻¹ 2)) := hD.image hφcont
  have hclosed : IsClosed (φ '' (ideleNormBand ℚ (2 : ℝ)⁻¹ 2)) := himg.isClosed
  -- The principal ideles (2^k) lie in the band, with φ-values ‖2‖^k tending to 0.
  have hvalk : ∀ k : ℕ,
      φ (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ (Units.mk0 (2 : ℚ) two_ne_zero ^ k)) =
        ‖((2 : ℚ) : v₂.adicCompletion ℚ)‖ ^ k := by
    intro k
    have hcoe : ∀ y : ℚˣ,
        (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ y).val.2 v₂ =
          (FinitePlace.embedding v₂) (y : ℚ) := by
      intro y
      have h1 : (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ y).val.2 v₂ =
          ((algebraMap ℚ 𝔸[𝓞 ℚ, ℚ]) (y : ℚ)).2 v₂ := rfl
      rw [h1, AdeleRing.algebraMap_snd_apply (𝓞 ℚ) ℚ y.val v₂]
      exact (FinitePlace.embedding_apply v₂ (y : ℚ)).symm
    show ‖((IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ
        (Units.mk0 (2 : ℚ) two_ne_zero ^ k)).val.2 v₂ : v₂.adicCompletion ℚ)‖ =
      ‖((2 : ℚ) : v₂.adicCompletion ℚ)‖ ^ k
    rw [hcoe, Units.val_pow_eq_pow_val, Units.val_mk0, hbrM 2, map_pow, norm_pow]
  have hbandk : ∀ k : ℕ,
      IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ (Units.mk0 (2 : ℚ) two_ne_zero ^ k) ∈
        ideleNormBand ℚ (2 : ℝ)⁻¹ 2 := by
    intro k
    have h1 : ideleNorm ℚ (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ
        (Units.mk0 (2 : ℚ) two_ne_zero ^ k)) = 1 :=
      MonoidHom.mem_ker.mp ((ideleNorm_spec ℚ).2 ⟨_, rfl⟩)
    rw [ideleNormBand, Set.mem_ofPred_eq, h1]
    exact mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  have htendsto : Tendsto (fun k : ℕ ↦ ‖((2 : ℚ) : v₂.adicCompletion ℚ)‖ ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h2pos.le h2lt
  have h0 : (0 : ℝ) ∈ φ '' (ideleNormBand ℚ (2 : ℝ)⁻¹ 2) :=
    hclosed.mem_of_tendsto htendsto
      (Filter.Eventually.of_forall fun k ↦ ⟨_, hbandk k, hvalk k⟩)
  obtain ⟨g, -, hgzero⟩ := h0
  obtain ⟨-, h2ne, -⟩ := AdeleRing.isUnit_iff.mp g.isUnit
  have hpos : 0 < φ g := norm_pos_iff.mpr (h2ne v₂)
  exact absurd hgzero (ne_of_lt hpos).symm

end RiemannMasullo
