module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3b
public import RiemannMasullo.Ch06_LocalGlobal.Sec3
public import RiemannMasullo.AppC_LCTVS.Sec3a

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import RiemannMasullo.Ch02_AdelicTheta.Sec2b
import RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Distribution.TemperedDistribution
import RiemannMasullo.ForMathlib.Topology.Algebra.Module.OpenMapping
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.SeparatingDual
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.ChangeVariables
import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec2
import RiemannMasullo.Ch02_AdelicTheta.Sec1
import RiemannMasullo.Ch07_SchauderBasesZeta.Sec1b
import Mathlib.Analysis.Normed.Group.Tannery
import RiemannMasullo.ForMathlib.Analysis.MellinTransform.Holomorphic
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import RiemannMasullo.ForMathlib.MeasureTheory.Integral.Bochner.Regular
import RiemannMasullo.AppD_SchwartzBruhat.Sec2b
import RiemannMasullo.AppD_SchwartzBruhat.Sec3b

import RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.Ch06_LocalGlobal.Sec3
import RiemannMasullo.AppA_AlgebraicNT.Sec3
import RiemannMasullo.Ch03_IdelicZeta.Sec3b
import RiemannMasullo.Ch05_ThetaZSpaces.Sec3b

import RiemannMasullo.ForMathlib.Analysis.Meromorphic.VerticalStripZeros
import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3a

/-! # §7.4 Nuclearity: spectral and orbital quotients

The first part of `RiemannMasullo.Ch07_SchauderBasesZeta.Sec4`, split off so that modules
that need only these declarations do not wait for the rest of that file.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NNReal NumberField.AdeleRing TensorProduct

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 150000
set_option Elab.async false

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "ω(" χ ")" => (χ : U).comp
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : (ideleClassNorm F).ker →ₜ* C𝔽)
local notation "P" => adelePolarSubspace F
local notation "B" => SchwartzBergman (univ : Set ℝ)
local notation "Entire" => entireContinuousMapSubalgebra

local instance instIdeleClassT2Sec4 : T2Space C𝔽 :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1

local instance instIdeleClassLocallyCompactSec4 : LocallyCompactSpace C𝔽 :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1

local instance instIdeleClassMeasurableSec4 (F : Type*) [Field F] [NumberField F] :
    MeasurableSpace (IdeleClassGroup (𝓞 F) F) := borel _
local instance instNuclearitySecondCountable : SecondCountableTopology C𝔽 :=
  letI := idele_secondCountable F
  inferInstanceAs (SecondCountableTopology
    (IdeleGroup (𝓞 F) F ⧸ IdeleGroup.principalSubgroup (𝓞 F) F))

local notation "𝒟" => BruhatCompactSupport (IdeleClassGroup (𝓞 F) F)
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "Π(" χ ")" => LinearMap.ker ((homogeneousAdelicThetaLinearMap F (ω(χ))).domRestrict P)
local notation "Θ₀(" χ ")" => ↥P ⧸ Π(χ)
local notation "mkΘ(" χ ", " f ")" => (Submodule.Quotient.mk f : Θ₀(χ))
local notation "Z(" χ ", " τ ", " hτ ")" => (exists_globalPolarThetaMellin χ τ hτ).choose
local notation "testIntegrand(" χ ", " φ ", " s ")" =>
  (fun g : C𝔽 ↦ (φ : 𝒟).val g * (ideleClassNormTwist χ s) g)

/-- Paper: Equation (7.4.1.1), p. 366.
The class-group Mellin transform of a Bruhat test uses the norm twist of the given character
and the idèle-class Tamagawa measure. -/
def nuclearityTestMellin (χ : U) (φ : 𝒟) (s : ℂ) : ℂ :=
  ∫ g, testIntegrand(χ, φ, s) g ∂μ𝔽

/-- Paper: Equation (7.4.1.1), p. 366.
The test integral converges absolutely throughout the norm chart.
At the trivial quasi-character it gives the integral of the test. -/
theorem nuclearityTestMellin_integrable (χ : U) (φ : 𝒟) :
    (∀ s : ℂ, Integrable (testIntegrand(χ, φ, s)) μ𝔽) ∧
      nuclearityTestMellin 1 φ 0 = ∫ g, φ.val g ∂μ𝔽 := by
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let : (ideleClassTamagawaMeasure F).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  have hc : Continuous φ.val :=
    continuous_schwartzBruhat (⟨φ.val, bruhatCompactSupport_mem_schwartz φ.property⟩ : SchwartzBruhat C𝔽)
  constructor
  · intro s
    exact (hc.mul (ideleClassNormTwist χ s).continuous).integrable_of_hasCompactSupport
      (show HasCompactSupport φ.val from φ.property.2).mul_right
  · apply integral_congr_ae
    filter_upwards with g
    change φ.val g * (1 * _ ^ (0 : ℂ)) = φ.val g
    simp

/-- Absolute convergence on every norm line makes the Mellin multiplier entire. -/
theorem differentiable_nuclearityTestMellin
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (φ : 𝒟) :
    Differentiable ℂ (nuclearityTestMellin χ φ) := by
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let n := fun g : C𝔽 ↦ ((ideleClassNorm F g).val : ℝ)
  let f := fun g : C𝔽 ↦ φ.val g * (χ g : ℂ)
  have hn : Continuous n :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have heq (s : ℂ) (g : C𝔽) : f g * (n g : ℂ) ^ s = testIntegrand(χ, φ, s) g :=
    mul_assoc _ _ _
  have h := analyticOnNhd_integral_mul_cpow_of_integrable μ𝔽 f n hn.measurable
    (fun g ↦ NNReal.coe_pos.mpr (Units.zero_lt _)) isOpen_univ
    (fun s _ ↦ by simpa only [heq] using (nuclearityTestMellin_integrable χ φ).1 s)
  have hfun : nuclearityTestMellin χ φ = fun s ↦ ∫ g, f g * (n g : ℂ) ^ s ∂μ𝔽 := by
    funext s
    simp only [heq, nuclearityTestMellin]
  rw [hfun]
  exact fun s ↦ (h s (mem_univ _)).differentiableAt

/-- Paper: Theorem 7.4.1.1(2), pp. 366–367.
An operator of order zero admits a nuclear presentation with rapidly decreasing
coefficients. The presentation includes equicontinuity and a common Banach disc. -/
def IsStronglyNuclearOperator {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
    (A : E →L[ℂ] E) : Prop :=
  ∃ r : NuclearPresentation A, ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
    ‖r.coeff n‖ * ((n : ℝ) + 1) ^ k ≤ C

/-- Paper: Theorem 7.4.1.1(2), pp. 366–367.
Every continuous rank-one operator is of order zero. -/
theorem isStronglyNuclearOperator_rankOne {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [PolynormableSpace ℂ E] [T2Space E]
    (ℓ : StrongDual ℂ E) (x : E) : IsStronglyNuclearOperator (ℓ.smulRight x) := by
  obtain ⟨r, hr, _, _, htail⟩ := nuclearPresentation_smulRight ℓ x 1 one_ne_zero
  refine ⟨r, fun k ↦ ⟨1, ?_⟩⟩
  intro n
  cases n with
  | zero => simp [hr]
  | succ n => simp [htail n]

/-- Membership in `schwartzBergmanDivisible g`: the function is `g` times an entire function. -/
theorem mem_schwartzBergmanDivisible_iff (g : Entire) (φ : B) :
    φ ∈ schwartzBergmanDivisible g ↔
      ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, φ.val s = g.val s * u s := by
  rw [schwartzBergmanDivisible, Submodule.mem_comap, Submodule.restrictScalars_mem,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a.val, a.property, fun s ↦ ?_⟩
    have h := congrArg (fun e : Entire ↦ e.val s) ha
    change a.val s * g.val s = (schwartzBergmanEntireInclusion φ).val s at h
    rw [schwartzBergmanEntireInclusion_apply] at h
    rw [← h, mul_comm]
  · rintro ⟨u, hu, h⟩
    refine ⟨⟨⟨u, hu.continuous⟩, hu⟩, ?_⟩
    apply Subtype.ext
    ext s
    change u s * g.val s = (schwartzBergmanEntireInclusion φ).val s
    rw [schwartzBergmanEntireInclusion_apply, h, mul_comm]

private theorem specDenom_B_ext (φ ψ : B) (h : ∀ s, φ.val s = ψ.val s) : φ = ψ :=
  Subtype.ext (funext h)

private theorem specDenom_shift_mem (φ : B) (c : ℂ) :
    (fun w ↦ φ.val (w - c)) ∈ schwartzBergmanSubmodule (univ : Set ℝ) := by
  obtain ⟨-, hd, hb⟩ := φ.property
  refine ⟨fun z hz ↦ absurd (mem_univ _) hz, ?_, ?_⟩
  · have hd' : Differentiable ℂ φ.val := fun z ↦
      (hd z (mem_univ _)).differentiableAt (Filter.univ_mem' fun _ ↦ mem_univ _)
    exact (hd'.comp (differentiable_id.sub_const c)).differentiableOn
  · intro a b hab _ N
    obtain ⟨A, hA⟩ := hb (a - c.re) (b - c.re) (by linarith) (subset_univ _) N
    obtain ⟨A₀, hA₀⟩ := hb (a - c.re) (b - c.re) (by linarith) (subset_univ _) 0
    refine ⟨2 ^ N * (A + ‖c‖ ^ N * A₀), ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have hz : w - c ∈ Complex.re ⁻¹' Icc (a - c.re) (b - c.re) := by
      simp only [mem_preimage, mem_Icc, Complex.sub_re] at hw ⊢
      constructor <;> linarith [hw.1, hw.2]
    have h1 := hA ⟨w - c, hz, rfl⟩
    have h0 := hA₀ ⟨w - c, hz, rfl⟩
    simp only [pow_zero, one_mul] at h0
    change ‖(w - c) ^ N * φ.val (w - c)‖ ≤ A at h1
    change ‖w ^ N * φ.val (w - c)‖ ≤ _
    set z := w - c
    have hwz : w = z + c := by simp [z]
    rw [hwz, norm_mul, norm_pow]
    rw [norm_mul, norm_pow] at h1
    have hn : ‖z + c‖ ^ N ≤ 2 ^ N * (‖z‖ ^ N + ‖c‖ ^ N) := by
      calc ‖z + c‖ ^ N ≤ (‖z‖ + ‖c‖) ^ N := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) N
        _ ≤ (2 * max ‖z‖ ‖c‖) ^ N := by
          apply pow_le_pow_left₀ (by positivity)
          linarith [le_max_left ‖z‖ ‖c‖, le_max_right ‖z‖ ‖c‖]
        _ = 2 ^ N * max ‖z‖ ‖c‖ ^ N := mul_pow _ _ _
        _ ≤ 2 ^ N * (‖z‖ ^ N + ‖c‖ ^ N) := by
          gcongr
          rcases le_total ‖z‖ ‖c‖ with h | h
          · rw [max_eq_right h]; linarith [pow_nonneg (norm_nonneg z) N]
          · rw [max_eq_left h]; linarith [pow_nonneg (norm_nonneg c) N]
    calc ‖z + c‖ ^ N * ‖φ.val z‖ ≤ 2 ^ N * (‖z‖ ^ N + ‖c‖ ^ N) * ‖φ.val z‖ :=
          mul_le_mul_of_nonneg_right hn (norm_nonneg _)
      _ = 2 ^ N * (‖z‖ ^ N * ‖φ.val z‖ + ‖c‖ ^ N * ‖φ.val z‖) := by ring
      _ ≤ 2 ^ N * (A + ‖c‖ ^ N * A₀) := by
          gcongr

private theorem specDenom_gen_bwd {X Y Q Bm : Type*} (ι : X → Y) (q : Y → Q) (c : X → Q)
    (hc : Surjective c) (hcq : ∀ x, c x = q (ι x)) (ZB : Q → Bm) (S : Set Bm)
    (hr : Set.range ZB = S) (φ : Bm) (hφ : φ ∈ S) : ∃ x : X, ZB (q (ι x)) = φ := by
  rw [← hr] at hφ
  obtain ⟨y, rfl⟩ := hφ
  obtain ⟨x, rfl⟩ := hc y
  exact ⟨x, by rw [hcq]⟩

private theorem specDenom_gen_mem {M Q Bm : Type*} (mk : M → Q) (hmk : Surjective mk) (Zf : Q → Bm)
    (ev : Bm → ℂ → ℂ) (hev : Injective ev) (zf : M → ℂ → ℂ)
    (hspec : ∀ f s, ev (Zf (mk f)) s = zf f s) (G' : ℂ → ℂ)
    (hv : ∃ G : ℂ → ℂ, G' = G ∧
      (∀ f : M, ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, zf f s = G s * u s) ∧
      (∀ φ : Bm, (∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, ev φ s = G s * u s) →
        ∃ f : M, ∀ s, ev φ s = zf f s)) (φ : Bm) :
    (∃ x, Zf x = φ) ↔ ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, ev φ s = G' s * u s := by
  obtain ⟨G, rfl, hfwd, hbwd⟩ := hv
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨f, rfl⟩ := hmk x
    obtain ⟨u, hu, h⟩ := hfwd f
    exact ⟨u, hu, fun s ↦ (hspec f s).trans (h s)⟩
  · intro h
    obtain ⟨f, hf⟩ := hbwd φ h
    exact ⟨mk f, hev (funext fun s ↦ (hspec f s).trans (hf s).symm)⟩

private theorem specDenom_gen_range_eq {Q Bm : Type*} {_ : AddCommGroup Q} {_ : Module ℂ Q}
    {_ : TopologicalSpace Q} {_ : AddCommGroup Bm} {_ : Module ℂ Bm} {_ : TopologicalSpace Bm}
    (Zc : Q →L[ℂ] Bm) (D : Submodule ℂ Bm) (h : ∀ φ, (∃ x, Zc x = φ) ↔ φ ∈ D) :
    Zc.toLinearMap.range = D := by
  ext φ
  rw [LinearMap.mem_range]
  exact h φ

private theorem specDenom_gen_shift {Q Bm : Type*} (Zf : Q → Bm) (ev : Bm → ℂ → ℂ) (L : ℂ → ℂ)
    (c : ℂ)
    (hrange : ∀ φ : Bm, (∃ x, Zf x = φ) ↔
      ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, ev φ s = L s * u s)
    (hshift : ∀ φ : Bm, ∃ ψ : Bm, ∀ w, ev ψ w = ev φ (w - c)) (f : Bm) :
    (∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, ev f s = L (s + c) * u s) ↔
      ∃ x : Q, ∀ s, ev f s = ev (Zf x) (s + c) := by
  constructor
  · rintro ⟨u, hu, h⟩
    obtain ⟨ψ, hψ⟩ := hshift f
    obtain ⟨x, hx⟩ := (hrange ψ).mpr ⟨fun w ↦ u (w - c), hu.comp (differentiable_id.sub_const c),
      fun w ↦ by rw [hψ, h, sub_add_cancel]⟩
    exact ⟨x, fun s ↦ by rw [hx, hψ, add_sub_cancel_right]⟩
  · rintro ⟨x, hx⟩
    obtain ⟨u, hu, h⟩ := (hrange (Zf x)).mp ⟨x, rfl⟩
    exact ⟨fun s ↦ u (s + c), hu.comp (differentiable_id.add_const c), fun s ↦ by rw [hx, h]⟩

section Spectral

variable (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
  (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))

local notation "Λ(" χ ", " τ ", " hτ ")" => regularizedCompletedHeckeL χ τ hτ
  (continuedCompletedHeckeL χ) (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2

/-- Paper: Equation (7.4.0.1), p. 366.
In Mellin coordinates the norm-power twist shifts the regularized completed generator
by translation of the argument by a. The shifted generator is entire. -/
theorem spectralNuclearityGenerator_differentiable (a : ℝ) :
    Differentiable ℂ (fun s ↦ (Λ(χ, τ, hτ)).val (s + (a : ℂ))) := by
  exact (Λ(χ, τ, hτ)).property.comp (differentiable_id.add_const (a : ℂ))

/-- Paper: Equation (7.4.0.1), p. 366.
The denominator is the shifted theta image in the Schwartz–Bergman model of the
exponentially decaying isotype. -/
def spectralNuclearityDenominator (a : ℝ) : Submodule ℂ B :=
  let h := spectralNuclearityGenerator_differentiable χ τ hτ a
  schwartzBergmanDivisible ⟨⟨_, h.continuous⟩, h⟩

/-- Paper: Equation (7.4.0.1), p. 366.
This is the spectral quotient with its quotient topology, in Mellin coordinates. -/
abbrev SpectralNuclearityQuotient (a : ℝ) := B ⧸ spectralNuclearityDenominator χ τ hτ a

open Classical in
private theorem specDenom_Lambda_val :
    ⇑(Λ(χ, τ, hτ)).val = toMeromorphicNFOn (fun s ↦
      (s + ((existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose : ℂ) *
        Complex.I) ^ (if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0) *
      (1 - s - ((existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose : ℂ) *
        Complex.I) ^ (if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0) *
      continuedCompletedHeckeL χ s) univ := rfl


/-- A character nontrivial on the norm-one ideles restricts to a nontrivial homomorphism there. -/
theorem normOneRestrict_ne_one (hω : ¬ ω(χ) = 1) :
    ¬ χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 := by
  intro h
  apply hω
  ext g
  exact congrArg Subtype.val (DFunLike.congr_fun h g)

/-- A character trivial on the norm-one ideles restricts to the trivial homomorphism there. -/
theorem normOneRestrict_eq_one (hω : ω(χ) = 1) :
    χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 := by
  ext g
  exact congrArg Subtype.val (DFunLike.congr_fun hω g)

open Classical in
private theorem specDenom_L0 (hδ : ¬ χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1) :
    ⇑(Λ(χ, τ, hτ)).val = continuedCompletedHeckeL χ := by
  rw [specDenom_Lambda_val, ite_eq_right_of_eq_false _ _ (eq_false hδ)]
  simp only [pow_zero, one_mul]
  exact toMeromorphicNFOn_eq_self.mpr (continuedCompletedHeckeL_spec χ).1

open Classical in
private theorem specDenom_L1 (t : ℝ) (hω : ω(χ) = 1)
    (ht : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U) (((t : ℝ) : ℂ) * Complex.I)) :
    ⇑(Λ(χ, τ, hτ)).val = toMeromorphicNFOn (fun s ↦ ((s + (t : ℂ) * Complex.I) *
      (1 - s - (t : ℂ) * Complex.I)) * continuedCompletedHeckeL χ s) univ := by
  have hphase := existsUnique_ideleNormSection_character_phase χ τ hτ
  have ht' : ∀ u : ℝ≥0ˣ, (χ (QuotientGroup.mk (τ u)) : ℂ) =
      (((u : ℝ≥0) : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) := by
    intro u
    have he := DFunLike.congr_fun ht (QuotientGroup.mk (τ u))
    change (χ (QuotientGroup.mk (τ u)) : ℂ) * _ ^ (0 : ℂ) =
      1 * ((((ideleNorm F (τ u)).val : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) at he
    rw [Complex.cpow_zero, mul_one, one_mul, hτ u] at he
    exact he
  have hx : hphase.exists.choose = t := hphase.unique hphase.exists.choose_spec ht'
  rw [specDenom_Lambda_val, hx, ite_eq_left_of_eq_true _ _ (eq_true (normOneRestrict_eq_one χ hω))]
  simp only [pow_one]

open Classical in
private theorem specDenom_values :
    ∃ G : ℂ → ℂ, ⇑(Λ(χ, τ, hτ)).val = G ∧
      (∀ f : P, ∃ u : ℂ → ℂ, Differentiable ℂ u ∧
        ∀ s, globalIdelicZFunction f.val (ideleClassNormTwist χ s) = G s * u s) ∧
      (∀ φ : B, (∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, φ.val s = G s * u s) →
        ∃ f : P, ∀ s, φ.val s = globalIdelicZFunction f.val (ideleClassNormTwist χ s)) := by
  by_cases hω : ω(χ) = 1
  · have h1 := (globalConverse_existsUnique_normTwist χ hω).exists
    obtain ⟨t, ht⟩ := h1
    have h2 := globalConverse_normTwist χ t ht
    obtain ⟨ZB, h3⟩ := h2
    have hZB := h3.2.2.1
    have hrange := h3.2.2.2.1
    refine ⟨_, specDenom_L1 χ τ hτ t hω ht, ?_, ?_⟩
    · intro f
      have hm : ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, (ZB f).val s =
          toMeromorphicNFOn (fun s ↦ ((s + (t : ℂ) * Complex.I) *
            (1 - s - (t : ℂ) * Complex.I)) * continuedCompletedHeckeL χ s) univ s * u s :=
        (Set.ext_iff.mp hrange (ZB f)).mp ⟨f, rfl⟩
      obtain ⟨u, hu, h⟩ := hm
      exact ⟨u, hu, fun s ↦ (hZB f s).symm.trans (h s)⟩
    · intro φ hφ
      have hm : φ ∈ Set.range ZB := (Set.ext_iff.mp hrange φ).mpr hφ
      obtain ⟨f, hf⟩ := hm
      refine ⟨f, fun s ↦ ?_⟩
      rw [← hf]
      exact hZB f s
  · have h2 := globalConverse_nontrivial χ hω
    obtain ⟨ZB, h3⟩ := h2
    have hZB := h3.2.1
    have hrange := h3.2.2
    refine ⟨_, specDenom_L0 χ τ hτ (normOneRestrict_ne_one χ hω), ?_, ?_⟩
    · intro f
      have hm : ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s,
          (ZB ((LinearMap.ker (homogeneousAdelicThetaLinearMap F (ω(χ)))).mkQ f.val)).val s =
          continuedCompletedHeckeL χ s * u s :=
        (Set.ext_iff.mp hrange _).mp ⟨_, rfl⟩
      obtain ⟨u, hu, h⟩ := hm
      exact ⟨u, hu, fun s ↦ (hZB f.val s).symm.trans (h s)⟩
    · intro φ hφ
      have hs0 := globalConverse_nontrivial_exact (F := F) _ hω
      have hs := hs0.surjective
      have hx := specDenom_gen_bwd (fun f : P ↦ f.val) _ _ hs (fun _ ↦ rfl) ZB _ hrange φ hφ
      obtain ⟨f, hf⟩ := hx
      refine ⟨f, fun s ↦ ?_⟩
      rw [← hf]
      exact hZB f.val s


/-- The range of the theta Mellin map: the functions that are `Λ` times an entire function. -/
theorem mem_range_globalPolarThetaMellin_iff (φ : B) :
    (∃ x : Θ₀(χ), (Z(χ, τ, hτ)) x = φ) ↔
      ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, φ.val s = (Λ(χ, τ, hτ)).val s * u s :=
  specDenom_gen_mem (fun f : P ↦ (Submodule.Quotient.mk f : Θ₀(χ)))
    (Submodule.Quotient.mk_surjective _) (fun x ↦ (Z(χ, τ, hτ)) x) (fun φ : B ↦ φ.val)
    (fun φ ψ h ↦ specDenom_B_ext φ ψ fun s ↦ congrFun h s)
    (fun (f : P) s ↦ globalIdelicZFunction f.val (ideleClassNormTwist χ s))
    (fun f s ↦ ((exists_globalPolarThetaMellin χ τ hτ).choose_spec f s).2)
    (⇑(Λ(χ, τ, hτ)).val) (specDenom_values χ τ hτ) φ

private theorem specDenom_mem_D (a : ℝ) (f : B) :
    f ∈ spectralNuclearityDenominator χ τ hτ a ↔
      ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, f.val s = (Λ(χ, τ, hτ)).val (s + (a : ℂ)) * u s :=
  mem_schwartzBergmanDivisible_iff _ f

/-- Paper: Equation (7.4.0.1), p. 366.
The unshifted denominator is precisely the image of the pole-free theta Mellin map. -/
theorem spectralNuclearityDenominator_zero :
    spectralNuclearityDenominator χ τ hτ 0 = (Z(χ, τ, hτ)).toLinearMap.range :=
  (specDenom_gen_range_eq (Z(χ, τ, hτ)) (spectralNuclearityDenominator χ τ hτ 0) fun φ ↦
    (mem_range_globalPolarThetaMellin_iff χ τ hτ φ).trans ((specDenom_mem_D χ τ hτ 0 φ).trans
      (exists_congr fun u ↦ and_congr_right fun _ ↦ forall_congr' fun s ↦ by
        rw [Complex.ofReal_zero, add_zero])).symm).symm

/-- Paper: Equation (7.4.0.1), p. 366.
The denominator consists precisely of the Mellin transforms of norm-twisted theta classes. -/
theorem mem_spectralNuclearityDenominator_iff (a : ℝ) (f : B) :
    f ∈ spectralNuclearityDenominator χ τ hτ a ↔
      ∃ x : Θ₀(χ), ∀ s : ℂ, f.val s = ((Z(χ, τ, hτ)) x).val (s + (a : ℂ)) :=
  (specDenom_mem_D χ τ hτ a f).trans
    (specDenom_gen_shift (fun x : Θ₀(χ) ↦ (Z(χ, τ, hτ)) x) (fun φ : B ↦ φ.val) (⇑(Λ(χ, τ, hτ)).val)
      (a : ℂ) (mem_range_globalPolarThetaMellin_iff χ τ hτ)
      (fun φ ↦ ⟨⟨_, specDenom_shift_mem φ (a : ℂ)⟩, fun _ ↦ rfl⟩) f)

/-- A fixed first factor defines a continuous map into the completed inductive tensor. -/
private theorem spectralNuclearityDenominator_isotypeModel_tensor
    {X Y Z : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    [UniformContinuousConstSMul ℂ (InductiveTensor X Y)]
    (e : UniformSpace.Completion (InductiveTensor X Y) ≃L[ℂ] Z) (u : X) :
    ∃ J : Y →L[ℂ] Z, ∀ p, J p = e (UniformSpace.Completion.coe' (α := InductiveTensor X Y) (u ⊗ₜ[ℂ] p)) := by
  let j : InductiveTensor X Y →L[ℂ] UniformSpace.Completion (InductiveTensor X Y) :=
    UniformSpace.Completion.toComplL
  let hs := withGeneratingSeminorms_spec (X ⊗[ℂ] Y)
    (fun q : {q : Seminorm ℂ (X ⊗[ℂ] Y) // (∀ x : X, Continuous (fun y : Y ↦ q (x ⊗ₜ[ℂ] y))) ∧
      (∀ y : Y, Continuous (fun x : X ↦ q (x ⊗ₜ[ℂ] y)))} ↦ q.val)
  exact ⟨e.toContinuousLinearMap.comp (j.comp ⟨TensorProduct.mk ℂ X Y u,
    hs.continuous_of_continuous_comp (TensorProduct.mk ℂ X Y u) fun q ↦ q.property.1 u⟩), fun _ ↦ rfl⟩

/-- Lift a scalar logarithmic profile by its tensor with the inverse compact character. -/
private theorem spectralNuclearityDenominator_isotypeModel_lift
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
    (χ : PontryaginDual G) :
    let K := m.toMonoidHom.ker
    let ω := χ.comp (⟨K.subtype, continuous_subtype_val⟩ : K →ₜ* G)
    let E := modulatedDecayIsotype m univ (mem_univ 0) ω
    ∃ J : PositiveRealExponentialDecay univ →L[ℂ] E, ∀ p t,
      (J p).val.val (τ t) = p.val (Real.log (t.val : ℝ)) := by
  intro K ω E
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨oneK, hone⟩ := compact_schwartzBruhat_one (H := K)
  obtain ⟨M, hM⟩ := schwartzBruhat_mul_unitaryCharacter (A := K) ω⁻¹
  let u := M oneK
  have hu (k : K) : u k = ((χ k.val : ℂ))⁻¹ := by
    rw [hM, hone, mul_one]
    exact Circle.coe_inv _
  let : UniformContinuousConstSMul ℂ (InductiveTensor (SchwartzBruhat K) (PositiveRealExponentialDecay univ)) :=
    uniformContinuousConstSMul_of_continuousConstSMul _ _
  have hB := modulatedExponentialDecay_tensor_equiv m univ hm ordConnected_univ univ_nonempty τ hτ
  let D := ModulatedExponentialDecay m univ
  let Profile := PositiveRealExponentialDecay univ
  have hJ : ∃ J : Profile →L[ℂ] D, ∀ p (k : K) t,
      (J p).val (k.val * τ t) = ((χ k.val : ℂ))⁻¹ * p.val (Real.log (t.val : ℝ)) := by
    have h := spectralNuclearityDenominator_isotypeModel_tensor
      (X := SchwartzBruhat K) (Y := Profile) (Z := D) hB.choose u
    obtain ⟨J, hJ⟩ := h
    refine ⟨J, fun p k t ↦ ?_⟩
    let ev (w : D) := w.val (k.val * τ t)
    have he : ev (J p) = u k * p.val (Real.log (t.val : ℝ)) := by
      with_reducible_and_instances exact (congrArg ev (hJ p)).trans (hB.choose_spec u p k t)
    exact he.trans (congrArg (· * _) (hu k))
  obtain ⟨J, hJ⟩ := hJ
  have hmem (p : Profile) : J p ∈ E := by
    apply (mem_modulatedDecayIsotype_iff m ω univ (mem_univ _) _).mpr
    intro k g
    let v : K := ⟨g / τ (m g), by change m (g / τ (m g)) = 1; rw [map_div, hτ _, div_self']⟩
    have hv : v.val * τ (m g) = g := div_mul_cancel _ _
    have hk : (k⁻¹ * v : K).val * τ (m g) = k.val⁻¹ * g := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, hv]
    rw [← hk, hJ, show (J p).val g = _ from (congrArg (J p).val hv.symm).trans (hJ p v (m g))]
    change (↑(χ ((k.val)⁻¹ * v.val)) : ℂ)⁻¹ * _ = (χ k.val : ℂ) * (_ * _)
    rw [map_mul, map_inv, Circle.coe_mul, Circle.coe_inv, mul_inv_rev, inv_inv]
    ac_rfl
  refine ⟨J.codRestrict E hmem, fun p t ↦ ?_⟩
  change (J p).val (τ t) = _
  have he := hJ p (1 : K) t
  simpa only [Subgroup.coe_one, one_mul, map_one, Circle.coe_one, inv_one] using he

/-- The compact character integral of an isotype vector is its section value when
the compact Haar measure has mass one. -/
private theorem spectralNuclearityDenominator_isotypeModel_average
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* G) (χ : PontryaginDual G)
    (μ₁ : Measure m.toMonoidHom.ker) (hv : μ₁ univ = 1) :
    let K := m.toMonoidHom.ker
    let ω := χ.comp (⟨K.subtype, continuous_subtype_val⟩ : K →ₜ* G)
    let E := modulatedDecayIsotype m univ (mem_univ 0) ω
    ∀ (u : E) t, (∫ k : K, (χ k.val : ℂ) * u.val.val (k.val * τ t) ∂μ₁) = u.val.val (τ t) := by
  intro K ω E u t
  have hv' (k : K) : (χ k.val : ℂ) * u.val.val (k.val * τ t) = u.val.val (τ t) := by
    have he := (mem_modulatedDecayIsotype_iff m ω univ (mem_univ _) u.val).mp u.property k (k.val * τ t)
    change (ω k : ℂ) * u.val.val (k.val * τ t) = u.val.val (τ t)
    exact he.symm.trans (congrArg u.val.val (inv_mul_cancel_left k.val (τ t)))
  rw [integral_congr_ae (.of_forall hv'), integral_const, measureReal_def, hv, ENNReal.toReal_one, one_smul]

/-- The unitary phase on the positive reals is an imaginary power. -/
private theorem spectralNuclearityDenominator_isotypeModel_phase (ψ : PontryaginDual ℝ≥0ˣ) :
    ∃ b : ℝ, ∀ t, ψ t = Circle.exp (b * Real.log (t.val : ℝ)) := by
  let c := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ψ
  obtain ⟨z, ⟨hz0, hz⟩, -⟩ := existsUnique_unitaryComplexPower c (fun t ↦ Circle.norm_coe (ψ t))
  have hz' : (z.im : ℂ) * Complex.I = z := by apply Complex.ext <;> simp [hz0]
  refine ⟨z.im, fun t ↦ Circle.ext ((hz t).trans ?_)⟩
  have hpos : 0 < (t.val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt t)
  rw [Circle.coe_exp, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'),
    ← Complex.ofReal_log hpos.le]
  conv_lhs => rw [← hz']
  congr 1
  push_cast
  ring

/-- The compact average realizes the section profile of the isotype. Its inverse
inserts the inverse compact character in the split tensor product. -/
private theorem spectralNuclearityDenominator_isotypeModel_mellin
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
    (χ : PontryaginDual G) :
    let K := m.toMonoidHom.ker
    let ω := χ.comp (⟨K.subtype, continuous_subtype_val⟩ : K →ₜ* G)
    let E := modulatedDecayIsotype m univ (mem_univ 0) ω
    ∃ M : E ≃L[ℂ] SchwartzBergman univ, ∀ (u : E) (s : ℂ),
      let v (t : ℝ≥0ˣ) := u.val.val (τ t) * ((χ (τ t) : ℂ) * ((t.val : ℝ) : ℂ) ^ s)
      Integrable v positiveRealHaar ∧ (M u).val s = ∫ t, v t ∂positiveRealHaar := by
  intro K ω E
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let μ₁ : Measure K := Measure.haarMeasure ⊤
  have hμ₁ : μ₁ univ = 1 := Measure.haarMeasure_self
  let μ := canonicalModulatedHaar m hm
  let : μ.IsHaarMeasure := (Classical.choose_spec (existsUnique_canonicalModulatedHaar m hm).exists).1
  have hμ := canonicalModulatedHaar_eq_map_prod m hm τ hτ μ₁ hμ₁
  obtain ⟨b, hb⟩ := spectralNuclearityDenominator_isotypeModel_phase (χ.comp τ)
  obtain ⟨A, F, T, e, hA, hF, _, he, hT⟩ := modulatedMellin_isotypicDiagram
    m hm hτ.surjective univ isOpen_univ ordConnected_univ univ_nonempty τ hτ μ₁ μ hμ χ b hb
  obtain ⟨J, hJ⟩ := spectralNuclearityDenominator_isotypeModel_lift m hm τ hτ χ
  have hp (u : E) (t : ℝ≥0ˣ) : (A u.val).val (Real.log (t.val : ℝ)) = u.val.val (τ t) :=
    (hA u.val t).trans (spectralNuclearityDenominator_isotypeModel_average m τ χ μ₁ hμ₁ u t)
  let R := A.comp E.subtypeL
  have hleft (u : E) : J (R u) = u := by
    refine Subtype.ext (Subtype.ext (funext fun g ↦ ?_))
    let k : K := ⟨τ (m g) / g, by change m (τ (m g) / g) = 1; rw [map_div, hτ _, div_self']⟩
    have hk : k.val⁻¹ * τ (m g) = g := by change (_ / _)⁻¹ * _ = _; rw [inv_div, div_mul_cancel]
    have hact (v : E) := (mem_modulatedDecayIsotype_iff m ω univ (mem_univ _) v.val).mp v.property k (τ (m g))
    change (J (R u)).val.val g = u.val.val g
    rw [← hk, hact, hact, hJ]
    exact congrArg ((ω k : ℂ) * ·) (hp u (m g))
  have hright (p : PositiveRealExponentialDecay univ) : R (J p) = p := by
    apply Subtype.ext
    funext x
    let t : ℝ≥0ˣ := Units.mk0 (Real.exp x).toNNReal (by positivity)
    have ht : Real.log (t.val : ℝ) = x := by
      change Real.log ((Real.exp x).toNNReal : ℝ) = x
      rw [Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp]
    exact ht ▸ (hp (J p) t).trans (hJ p t)
  let r := ContinuousLinearEquiv.equivOfInverse R J hleft hright
  let scalarMellin := positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty
  let M := (r.trans scalarMellin).trans T.symm
  refine ⟨M, fun u s ↦ ?_⟩
  let avg (t : ℝ≥0ˣ) := ∫ k : K, (χ k.val : ℂ) * u.val.val (k.val * τ t) ∂μ₁
  have havg (t : ℝ≥0ˣ) : avg t = u.val.val (τ t) :=
    spectralNuclearityDenominator_isotypeModel_average m τ χ μ₁ hμ₁ u t
  have hval (t : ℝ≥0ˣ) : ((t.val : ℝ) : ℂ) ^ s * (χ (τ t) : ℂ) * avg t =
      u.val.val (τ t) * ((χ (τ t) : ℂ) * ((t.val : ℝ) : ℂ) ^ s) := by rw [havg]; ring
  have hsplit := modulatedMellin_split m hm hτ.surjective univ isOpen_univ ordConnected_univ
    univ_nonempty τ hτ μ₁ μ hμ χ u.val s (mem_univ _)
  have hFT : M u = F u.val := by
    apply T.injective
    change T (T.symm (scalarMellin (A u.val))) = _
    rw [T.apply_symm_apply, hT, he]
  exact ⟨hsplit.2.1.congr (.of_forall hval), (congrArg (fun H : SchwartzBergman univ ↦ H.val s) hFT).trans
    ((hF u.val s (mem_univ _)).trans (hsplit.2.2.trans (integral_congr_ae (.of_forall hval))))⟩

/-- Continuous integrable positive-real profiles are determined by their
integrals against the unitary powers. -/
private theorem spectralNuclearityDenominator_isotypeModel_unique (f h : ℝ≥0ˣ → ℂ)
    (hf : Continuous f) (hh : Continuous h) (hi : Integrable f positiveRealHaar)
    (hj : Integrable h positiveRealHaar)
    (he : ∀ z : ℂ, z.re = 0 →
      ∫ t : ℝ≥0ˣ, f t * ((t.val : ℝ) : ℂ) ^ z ∂positiveRealHaar =
        ∫ t : ℝ≥0ˣ, h t * ((t.val : ℝ) : ℂ) ^ z ∂positiveRealHaar) : f = h := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let : LocallyCompactSpace ℝ≥0ˣ := e.symm.isOpenEmbedding.locallyCompactSpace
  let : SecondCountableTopology ℝ≥0ˣ := e.symm.isEmbedding.secondCountableTopology
  let ev (x : ℝ≥0ˣ) : PontryaginDual ℝ≥0ˣ →* Circle :=
    { toFun := fun η ↦ η x, map_one' := rfl, map_mul' := fun _ _ ↦ rfl }
  have hsep : Injective ev := fun _ _ e ↦ pontryaginDual_pairing_separates.1 (funext (DFunLike.congr_fun e))
  have hzero : f - h =ᵐ[positiveRealHaar] 0 := by
    apply ae_eq_zero_of_integral_mul_circle_eq_zero ev (fun η ↦ η.continuous) hsep (hi.sub hj)
    intro η
    let c := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η
    obtain ⟨z, ⟨hz, hη⟩, _⟩ := existsUnique_unitaryComplexPower c (fun t ↦ Circle.norm_coe (η t))
    have iχ (q : ℝ≥0ˣ → ℂ) (hq : Continuous q) (i : Integrable q positiveRealHaar) :
        Integrable (fun t ↦ q t * (η t : ℂ)) positiveRealHaar :=
      i.norm.mono' (hq.mul (continuous_subtype_val.comp η.continuous)).aestronglyMeasurable
        (.of_forall fun t ↦ by rw [norm_mul, Circle.norm_coe, mul_one])
    have hc (t) : (η t : ℂ) = ((t.val : ℝ) : ℂ) ^ z := hη t
    change ∫ t, (f t - h t) * (η t : ℂ) ∂positiveRealHaar = 0
    simp_rw [sub_mul]
    rw [integral_sub (iχ f hf hi) (iχ h hh hj), sub_eq_zero]
    simpa only [hc] using he z hz
  exact sub_eq_zero.mp (Measure.eq_of_ae_eq hzero (hf.sub hh) continuous_const)

/-- Shifting the Mellin argument by a real exponent inserts the corresponding
norm power in the integrand of a polar homogeneous theta transform. -/
private theorem spectralNuclearityDenominator_isotypeModel_shift (hτ : RightInverse τ (ideleNorm F)) (a : ℝ) (f : P) (s : ℂ) :
    let σ (t : ℝ≥0ˣ) : C𝔽 := QuotientGroup.mk (τ t)
    let H (t : ℝ≥0ˣ) := ((((t.val : ℝ) ^ a : ℝ) : ℂ) * homogeneousAdelicTheta (ω(χ)) f.val (σ t)) *
      (χ (σ t) : ℂ)
    let v (t : ℝ≥0ˣ) := H t * ((t.val : ℝ) : ℂ) ^ s
    Integrable v positiveRealHaar ∧
      homogeneousThetaMellinIntegral τ (ω(χ)) f.val (ideleClassNormTwist χ (s + a)) = ∫ t, v t ∂positiveRealHaar := by
  intro σ H v
  let c := ideleClassNormTwist χ (s + a)
  have hc (t : ℝ≥0ˣ) : homogeneousAdelicTheta (ω(χ)) f.val (σ t) * c (σ t) = v t := by
    change _ * ((χ (σ t) : ℂ) * (((ideleNorm F (τ t)).val : ℝ) : ℂ) ^ (s + (a : ℂ))) =
      (((((t.val : ℝ) ^ a : ℝ) : ℂ) * _) * _) * _
    rw [hτ, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr t.ne_zero)),
      Complex.ofReal_cpow (NNReal.coe_nonneg _) a]
    ring
  have hi := homogeneousThetaMellinIntegral_integrable_on_component τ (ω(χ)) f.val hτ (Or.inl f.property) c
    ⟨mem_univ _, fun g ↦ normOneRestriction_unitaryChart (ideleClassNorm F)
      (isProperMap_ideleClassNorm F).continuous χ (s + a) g⟩
  exact ⟨hi.congr (.of_forall hc), integral_congr_ae (.of_forall hc)⟩

/-- Paper: Equation (7.4.0.1), p. 366.
The section Mellin transform identifies the decay isotype with the full
Schwartz–Bergman space and takes the norm-twisted theta image to the denominator.
The section integral uses the quotient Haar measure dt/t of §3.2. -/
theorem spectralNuclearityDenominator_isotypeModel (a : ℝ) :
    let m : C𝔽 →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
    let E := modulatedDecayIsotype m (Set.univ : Set ℝ) (Set.mem_univ 0) (ω(χ))
    ∃ M : ↥E ≃L[ℂ] B,
      (∀ (u : E) s, (M u).val s = ∫ t : ℝ≥0ˣ,
        u.val.val (QuotientGroup.mk (τ t)) *
          ideleClassNormTwist χ s (QuotientGroup.mk (τ t)) ∂positiveRealHaar) ∧
      ∀ u : E, M u ∈ spectralNuclearityDenominator χ τ hτ a ↔
        ∃ f : P, ∀ g : C𝔽, u.val.val g =
          ((((ideleClassNorm F g).val : ℝ) ^ a : ℝ) : ℂ) *
            homogeneousAdelicTheta (ω(χ)) f.val g := by
  intro m E
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let σ := q.comp τ
  have hσ : RightInverse σ m := hτ
  have hm : IsModulation m := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one⟩
  obtain ⟨M, hM⟩ := spectralNuclearityDenominator_isotypeModel_mellin m hm σ hσ χ
  have hc (s : ℂ) (t : ℝ≥0ˣ) : ideleClassNormTwist χ s (σ t) =
      (χ (σ t) : ℂ) * ((t.val : ℝ) : ℂ) ^ s := by
    change (χ (σ t) : ℂ) * (((m (σ t)).val : ℝ) : ℂ) ^ s = _
    rw [hσ]
  refine ⟨M, fun u s ↦ (hM u s).2.trans (integral_congr_ae (.of_forall fun t ↦
    congrArg (u.val.val (σ t) * ·) (hc s t).symm)), fun u ↦ ?_⟩
  let profile (t : ℝ≥0ˣ) := u.val.val (σ t) * (χ (σ t) : ℂ)
  have hU (s : ℂ) : Integrable (fun t : ℝ≥0ˣ ↦ profile t * ((t.val : ℝ) : ℂ) ^ s) positiveRealHaar ∧
      (M u).val s = ∫ t : ℝ≥0ˣ, profile t * ((t.val : ℝ) : ℂ) ^ s ∂positiveRealHaar := by
    simpa only [profile, mul_assoc] using hM u s
  let w (g : C𝔽) := ((((m g).val : ℝ) ^ a : ℝ) : ℂ)
  let H (f : P) (t : ℝ≥0ˣ) := w (σ t) * homogeneousAdelicTheta (ω(χ)) f.val (σ t) * (χ (σ t) : ℂ)
  have hH (f : P) (s : ℂ) :
      Integrable (fun t : ℝ≥0ˣ ↦ H f t * ((t.val : ℝ) : ℂ) ^ s) positiveRealHaar ∧
      ((exists_globalPolarThetaMellin χ τ hτ).choose (Submodule.Quotient.mk f)).val (s + (a : ℂ)) =
        ∫ t : ℝ≥0ˣ, H f t * ((t.val : ℝ) : ℂ) ^ s ∂positiveRealHaar := by
    have h := spectralNuclearityDenominator_isotypeModel_shift χ τ hτ a f s
    have hw (t : ℝ≥0ˣ) : w (σ t) = (((t.val : ℝ) ^ a : ℝ) : ℂ) :=
      congrArg (fun x : ℝ≥0ˣ ↦ (((x.val : ℝ) ^ a : ℝ) : ℂ)) (hσ t)
    simp only [H, hw]
    exact ⟨h.1, ((exists_globalPolarThetaMellin χ τ hτ).choose_spec f _).1.trans h.2⟩
  rw [mem_spectralNuclearityDenominator_iff]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have he : profile = H f := by
      have hu : Continuous u.val.val := by
        let z := modulatedExponentialDecayTwist m univ ⟨0, mem_univ _⟩ u.val
        exact (schwartzBruhat_continuous z).congr
          ((modulatedExponentialDecay_zeroTwist_injective m univ (mem_univ _)).2 u.val)
      have hχ : Continuous (fun t : ℝ≥0ˣ ↦ (χ (σ t) : ℂ)) :=
        continuous_subtype_val.comp (χ.continuous.comp σ.continuous)
      have hr : Continuous (fun t : ℝ≥0ˣ ↦ (((t.val : ℝ) ^ a : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp ((NNReal.continuous_coe.comp Units.continuous_val).rpow_const
          (fun t ↦ Or.inl (NNReal.coe_ne_zero.mpr t.ne_zero)))
      have hw (t : ℝ≥0ˣ) : w (σ t) = (((t.val : ℝ) ^ a : ℝ) : ℂ) := congrArg
        (fun x : ℝ≥0ˣ ↦ (((x.val : ℝ) ^ a : ℝ) : ℂ)) (hσ t)
      apply spectralNuclearityDenominator_isotypeModel_unique
      · exact (hu.comp σ.continuous).mul hχ
      · exact (((hr.congr fun t ↦ (hw t).symm).mul
          ((homogeneousAdelicTheta (ω(χ)) f.val).continuous.comp σ.continuous)).mul hχ)
      · simpa only [Complex.cpow_zero, mul_one] using (hU 0).1
      · simpa only [Complex.cpow_zero, mul_one] using (hH f 0).1
      · exact fun s _ ↦ (hU s).2.symm.trans ((hx s).trans (hH f s).2)
    have hsec (t : ℝ≥0ˣ) : u.val.val (σ t) = w (σ t) * homogeneousAdelicTheta (ω(χ)) f.val (σ t) :=
      mul_right_cancel₀ (Circle.coe_ne_zero _) (congrFun he t)
    refine ⟨f, fun g ↦ ?_⟩
    let k : m.toMonoidHom.ker := ⟨σ (m g) / g, by change m (σ (m g) / g) = 1; rw [map_div, hσ _, div_self']⟩
    have hk : k.val⁻¹ * σ (m g) = g := by change (_ / _)⁻¹ * _ = _; rw [inv_div, div_mul_cancel]
    have hr := (mem_modulatedDecayIsotype_iff m (ω(χ)) univ (mem_univ _) u.val).mp u.property k (σ (m g))
    have ht := homogeneousAdelicTheta_homogeneous (ω(χ)) f.val k (σ (m g))
    rw [hk] at hr ht
    change u.val.val g = w g * _
    rw [hr, ht, hsec, mul_left_comm, show w (σ (m g)) = w g from congrArg
      (fun x : ℝ≥0ˣ ↦ (((x.val : ℝ) ^ a : ℝ) : ℂ)) (hσ _)]
  · rintro ⟨f, hf⟩
    refine ⟨Submodule.Quotient.mk f, fun s ↦ (hU s).2.trans <| (_root_.Eq.trans ?_ (hH f s).2.symm)⟩
    apply integral_congr_ae (.of_forall fun t ↦ ?_)
    change (u.val.val (σ t) * _ ) * _ = ((w (σ t) * _) * _) * _
    rw [hf]
    rfl

private theorem spectralNuclearityDenominator_closed_invariant_mellinAux {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] (φ c : X → ℂ) (n : X → ℝ) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hc : Continuous c) (hn : Continuous n) (hpos : ∀ x, 0 < n x) :
    Differentiable ℂ (fun s : ℂ ↦ ∫ x, φ x * (c x * (n x : ℂ) ^ s) ∂μ) ∧
      ∀ a b : ℝ, ∃ C, ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖∫ x, φ x * (c x * (n x : ℂ) ^ s) ∂μ‖ ≤ C := by
  have hjoint : Continuous (fun p : ℂ × X ↦ ((n p.2 : ℂ)) ^ p.1) :=
    Continuous.cpow (Complex.continuous_ofReal.comp (hn.comp continuous_snd)) continuous_fst
      (fun p ↦ Complex.ofReal_mem_slitPlane.2 (hpos p.2))
  have hφi : Integrable φ μ := hφ.integrable_of_hasCompactSupport hφc
  have hpow (s : ℂ) : Continuous (fun x ↦ (n x : ℂ) ^ s) :=
    hjoint.comp (continuous_const.prodMk continuous_id)
  have hlog : Continuous (fun x ↦ Complex.log (n x : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuousOn_log.comp_continuous hn
      fun x ↦ (hpos x).ne') |>.congr fun x ↦ Complex.ofReal_log (hpos x).le
  constructor
  · intro s₀
    obtain ⟨C, hC⟩ := ((isCompact_closedBall s₀ 1).prod hφc).exists_bound_of_continuousOn
      (f := fun p : ℂ × X ↦ c p.2 * ((n p.2 : ℂ) ^ p.1 * Complex.log (n p.2 : ℂ)))
      ((hc.comp continuous_snd).mul (hjoint.mul (hlog.comp continuous_snd))).continuousOn
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun s x ↦ φ x * (c x * (n x : ℂ) ^ s))
      (F' := fun s x ↦ φ x * (c x * ((n x : ℂ) ^ s * Complex.log (n x : ℂ))))
      (x₀ := s₀) (bound := fun x ↦ ‖φ x‖ * C) (Metric.ball_mem_nhds s₀ one_pos)
      (Filter.Eventually.of_forall fun s ↦ (hφ.mul (hc.mul (hpow s))).aestronglyMeasurable)
      ((hφ.mul (hc.mul (hpow s₀))).integrable_of_hasCompactSupport hφc.mul_right)
      (hφ.mul (hc.mul ((hpow s₀).mul hlog))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x s hs ↦ by
        by_cases hx : x ∈ tsupport φ
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_left
            (hC (s, x) ⟨Metric.ball_subset_closedBall hs, hx⟩) (norm_nonneg _)
        · simp [image_eq_zero_of_notMem_tsupport hx])
      (hφi.norm.mul_const C)
      (Filter.Eventually.of_forall fun x s _ ↦ by
        have h := (hasDerivAt_id s).const_cpow (c := (n x : ℂ))
          (Or.inl (Complex.ofReal_ne_zero.2 (hpos x).ne'))
        simpa only [id, mul_one] using (h.const_mul (c x)).const_mul (φ x))
    exact key.2.differentiableAt
  · intro a b
    obtain ⟨C, hC⟩ := hφc.isCompact.exists_bound_of_continuousOn
      (f := fun x ↦ ‖c x‖ * (n x ^ a + n x ^ b))
      ((hc.norm.mul ((hn.rpow_const fun x ↦ Or.inl (hpos x).ne').add
        (hn.rpow_const fun x ↦ Or.inl (hpos x).ne'))).continuousOn)
    refine ⟨∫ x, ‖φ x‖ * C ∂μ, fun s ha hb ↦ ?_⟩
    refine norm_integral_le_of_norm_le (hφi.norm.mul_const C) (Filter.Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ tsupport φ
    · rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hpos x)]
      have hp : n x ^ s.re ≤ n x ^ a + n x ^ b := by
        rcases le_total 1 (n x) with h1 | h1
        · exact (Real.rpow_le_rpow_of_exponent_le h1 hb).trans
            (le_add_of_nonneg_left (Real.rpow_nonneg (hpos x).le _))
        · exact (Real.rpow_le_rpow_of_exponent_ge (hpos x) h1 ha).trans
            (le_add_of_nonneg_right (Real.rpow_nonneg (hpos x).le _))
      have h := hC x hx
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _)
        (add_nonneg (Real.rpow_nonneg (hpos x).le _) (Real.rpow_nonneg (hpos x).le _)))] at h
      calc ‖φ x‖ * (‖c x‖ * n x ^ s.re) ≤ ‖φ x‖ * (‖c x‖ * (n x ^ a + n x ^ b)) := by gcongr
        _ ≤ ‖φ x‖ * C := by gcongr
    · simp [image_eq_zero_of_notMem_tsupport hx]

private theorem spectralNuclearityDenominator_closed_invariant_mellin (χ : U) (φ : 𝒟) :
    Differentiable ℂ (nuclearityTestMellin χ φ) ∧
      ∀ a b : ℝ, ∃ C, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖nuclearityTestMellin χ φ s‖ ≤ C := by
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let : (ideleClassTamagawaMeasure F).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  have hc : Continuous φ.val :=
    continuous_schwartzBruhat (⟨φ.val, bruhatCompactSupport_mem_schwartz φ.property⟩ : SchwartzBruhat C𝔽)
  have hn : Continuous (fun g : C𝔽 ↦ (((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  exact spectralNuclearityDenominator_closed_invariant_mellinAux μ𝔽 φ.val (fun g ↦ (χ g : ℂ))
    (fun g : C𝔽 ↦ (((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ)) hc φ.property.2
    (continuous_subtype_val.comp χ.continuous) hn
    (fun g ↦ NNReal.coe_pos.2 (pos_iff_ne_zero.2 (Units.ne_zero _)))

private theorem spectralNuclearityDenominator_closed_invariant_mem (m : ℂ → ℂ)
    (hm : Differentiable ℂ m)
    (hb : ∀ a b : ℝ, ∃ C, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖m s‖ ≤ C) (f : ℂ → ℂ)
    (hf : f ∈ schwartzBergmanSubmodule (univ : Set ℝ)) :
    (fun s ↦ m s * f s) ∈ schwartzBergmanSubmodule (univ : Set ℝ) := by
  obtain ⟨-, hd, hbd⟩ := hf
  refine ⟨fun z hz ↦ absurd (mem_univ _) hz, hm.differentiableOn.mul hd, ?_⟩
  intro a b hab hI N
  obtain ⟨A, hA⟩ := hbd a b hab hI N
  obtain ⟨C, hC⟩ := hb a b
  refine ⟨max C 0 * A, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have h1 : ‖z ^ N * f z‖ ≤ A := hA ⟨z, hz, rfl⟩
  change ‖z ^ N * (m z * f z)‖ ≤ _
  rw [mul_left_comm, norm_mul]
  exact mul_le_mul (le_max_of_le_left (hC z hz.1 hz.2)) h1 (norm_nonneg _) (le_max_right _ _)

private theorem spectralNuclearityDenominator_closed_invariant_trace (m f : ℂ → ℂ) (a : ℝ)
    (N : ℕ) (C : ℝ) (hC : ∀ s : ℂ, s.re = a → ‖m s‖ ≤ C) (hc : Continuous (fun s ↦ m s * f s))
    (hf : MemLp (weightedVerticalTrace a N f) 2 volume) :
    (eLpNorm (weightedVerticalTrace a N (fun s ↦ m s * f s)) 2 volume).toReal ≤
      max C 0 * (eLpNorm (weightedVerticalTrace a N f) 2 volume).toReal := by
  have hz : Continuous (fun x : ℝ ↦ (a : ℂ) + (x : ℂ) * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hmeas : AEStronglyMeasurable (weightedVerticalTrace a N (fun s ↦ m s * f s)) volume :=
    ((hz.pow N).mul (hc.comp hz)).aestronglyMeasurable
  let c : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have h := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (c := c) hmeas
    (g := weightedVerticalTrace a N f) (Filter.Eventually.of_forall fun x ↦ by
      rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnNorm, coe_nnNorm]
      change ‖((a : ℂ) + (x : ℂ) * Complex.I) ^ N * (m _ * f _)‖ ≤
        max C 0 * ‖((a : ℂ) + (x : ℂ) * Complex.I) ^ N * f _‖
      rw [mul_left_comm, norm_mul]
      exact mul_le_mul_of_nonneg_right (le_max_of_le_left (hC _ (by simp))) (norm_nonneg _)) 2
  have hne : c • eLpNorm (weightedVerticalTrace a N f) 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hf.eLpNorm_ne_top
  refine (ENNReal.toReal_mono hne h).trans_eq ?_
  rw [ENNReal.toReal_smul, NNReal.smul_def, smul_eq_mul]
  rfl

private theorem spectralNuclearityDenominator_closed_invariant_cont {X ι : Type*}
    [AddCommGroup X] [Module ℂ X] (p : SeminormFamily ℂ X ι)
    (L : WithGeneratingSeminorms X p →ₗ[ℂ] WithGeneratingSeminorms X p)
    (h : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, p i (L x) ≤ C * p i x) : Continuous L :=
  WithSeminorms.continuous_of_isBounded (withGeneratingSeminorms_spec X p)
    (withGeneratingSeminorms_spec X p) L (Seminorm.IsBounded.of_real fun i ↦ by
      obtain ⟨C, hC0, hC⟩ := h i
      exact ⟨{i}, C, fun x ↦ (hC x).trans (mul_le_mul_of_nonneg_left
        (Seminorm.le_def.mp (Finset.le_sup (f := p) (Finset.mem_singleton_self i)) x) hC0)⟩)

/-- Paper: Theorem 7.4.1.1(1), p. 366.
The twisted theta image is closed. Compactly supported Bruhat tests act by continuous
Mellin multiplication, which preserves that image. -/
theorem spectralNuclearityDenominator_closed_invariant (a : ℝ) (φ : 𝒟) :
    let D := spectralNuclearityDenominator χ τ hτ a
    IsClosed (D : Set B) ∧
      ∃ A : B →L[ℂ] B,
        (∀ f s, (A f).val s = nuclearityTestMellin χ φ s * f.val s) ∧
        Set.MapsTo A (D : Set B) D := by
  intro D
  obtain ⟨hMd, hMb⟩ := spectralNuclearityDenominator_closed_invariant_mellin χ φ
  refine ⟨schwartzBergmanDivisible_isClosed _, ?_⟩
  let L : B →ₗ[ℂ] B :=
    { toFun := fun f ↦ ⟨fun s ↦ nuclearityTestMellin χ φ s * f.val s,
        spectralNuclearityDenominator_closed_invariant_mem _ hMd hMb f.val f.property⟩
      map_add' := fun f g ↦ Subtype.ext (funext fun s ↦ mul_add _ _ _)
      map_smul' := fun c f ↦ Subtype.ext (funext fun s ↦ mul_left_comm _ _ _) }
  have hL : Continuous L := by
    refine spectralNuclearityDenominator_closed_invariant_cont _ L fun i ↦ ?_
    obtain ⟨C, hC⟩ := hMb i.1.val i.1.val
    refine ⟨max C 0, le_max_right _ _, fun f ↦ ?_⟩
    have hfc : Continuous (f.val : ℂ → ℂ) := continuousOn_univ.mp (f.property.2.1.continuousOn.mono fun _ _ ↦ trivial)
    exact spectralNuclearityDenominator_closed_invariant_trace _ f.val i.1.val i.2 C
      (fun s hs ↦ hC s hs.ge hs.le) (hMd.continuous.mul hfc)
      (schwartzBergman_trace_memLp _ i.1 2 (by norm_num) (by norm_num) i.2 f)
  refine ⟨⟨L, hL⟩, fun f s ↦ rfl, ?_⟩
  intro f hf
  obtain ⟨u, hu, h⟩ := (specDenom_mem_D χ τ hτ a f).mp hf
  refine (specDenom_mem_D χ τ hτ a _).mpr ⟨fun s ↦ nuclearityTestMellin χ φ s * u s, hMd.mul hu,
    fun s ↦ ?_⟩
  change nuclearityTestMellin χ φ s * f.val s = _
  rw [h s]
  ring

local notation "zeros(" χ ", " τ ", " hτ ")" =>
  {z : ℂ // 0 < analyticOrderAt ((Λ(χ, τ, hτ)).val : ℂ → ℂ) z}
local notation "multiplicity(" χ ", " τ ", " hτ ", " z ")" =>
  (analyticOrderAt ((Λ(χ, τ, hτ)).val : ℂ → ℂ) (z : ℂ)).toNat
local notation "jets(" χ ", " τ ", " hτ ")" =>
  Σ z : zeros(χ, τ, hτ), Fin (multiplicity(χ, τ, hτ, z))
local notation "Q(" a ")" => SpectralNuclearityQuotient χ τ hτ a
local notation "D(" a ")" => spectralNuclearityDenominator χ τ hτ a

private theorem exists_spectralNuclearityBiorthogonal_vanish (G u f : ℂ → ℂ)
    (hG : Differentiable ℂ G) (hu : Differentiable ℂ u) (a : ℂ)
    (hf : ∀ s, f s = G (s + a) * u s) (z : ℂ) (k : ℕ)
    (hk : k < (analyticOrderAt G z).toNat) : iteratedDeriv k f (z - a) = 0 := by
  have hg : AnalyticAt ℂ (fun s ↦ s + a) (z - a) := by fun_prop
  have hd : deriv (fun s ↦ s + a) (z - a) ≠ 0 := by simp
  have hcomp : analyticOrderAt (G ∘ fun s ↦ s + a) (z - a) = analyticOrderAt G z := by
    rw [analyticOrderAt_comp_of_deriv_ne_zero hg hd, sub_add_cancel]
  have hfe : f = (G ∘ fun s ↦ s + a) * u := funext fun s ↦ hf s
  have hGa : AnalyticAt ℂ (G ∘ fun s ↦ s + a) (z - a) :=
    (hG.comp (differentiable_id.add_const a)).analyticAt _
  have hua : AnalyticAt ℂ u (z - a) := hu.analyticAt _
  have hord : analyticOrderAt f (z - a) =
      analyticOrderAt G z + analyticOrderAt u (z - a) := by
    rw [hfe, analyticOrderAt_mul hGa hua, hcomp]
  have hle : ((k + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt f (z - a) := by
    rw [hord]
    refine le_trans ?_ le_self_add
    cases h : analyticOrderAt G z with
    | top => exact le_top
    | coe n =>
      rw [h] at hk
      exact_mod_cast (show k + 1 ≤ n by simpa using hk)
  have hfa : AnalyticAt ℂ f (z - a) := by rw [hfe]; exact hGa.mul hua
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hfa).mp hle k (Nat.lt_succ_self k)

open Classical in
/-- Paper: Theorem 7.4.1.1(2), p. 366, using Theorem 7.1.4.2(3).
For each jet index there is a Schwartz–Bergman function whose derivative jets at the
shifted zeros of the regularized completed generator are the corresponding coordinate vector:
the `i.2`-th derivative at `i.1 − a` is `1` for `i = j` and `0` for every other jet index. -/
theorem exists_spectralNuclearityBiorthogonal_vectors (a : ℝ) (j : jets(χ, τ, hτ)) :
    ∃ f : B, ∀ i : jets(χ, τ, hτ),
      iteratedDeriv i.2.val f.val (i.1.val - (a : ℂ)) = if i = j then 1 else 0 := by
  classical
  have h := orbitalSchwartzBergman_biorthogonal χ τ hτ (continuedCompletedHeckeL χ)
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2 ∅
  rw [orbitalHeckeGenerator_empty] at h
  obtain ⟨b,hb⟩ := h
  let J := {p : ℂ × ℕ // (p.2 : ℕ∞) < analyticOrderAt ((Λ(χ,τ,hτ)).val : ℂ → ℂ) p.1}
  have emb {r : ℕ} {n : ℕ∞} (hr : r < n.toNat) : (r : ℕ∞) < n := by
    cases n using ENat.recTopCoe with
    | top => exact ENat.natCast_lt_top r
    | coe n => exact_mod_cast (by simpa using hr : r < n)
  let idx (i : jets(χ,τ,hτ)) : J := ⟨(i.1.val,i.2.val),emb i.2.isLt⟩
  have hinj : Injective idx := by
    rintro ⟨z,k⟩ ⟨w,l⟩ h
    have ez : z = w := Subtype.ext (congrArg (fun x : J ↦ x.val.1) h)
    subst w
    have ek : k = l := Fin.ext (congrArg (fun x : J ↦ x.val.2) h)
    subst l
    rfl
  let g := b (idx j)
  refine ⟨⟨fun s ↦ g.val (s - -(a:ℂ)),specDenom_shift_mem g (-a)⟩,fun i ↦ ?_⟩
  change iteratedDeriv i.2.val (fun s ↦ g.val (s - -(a:ℂ))) (i.1.val-(a:ℂ)) = _
  rw [iteratedDeriv_comp_sub_const]
  change iteratedDeriv i.2.val g.val ((i.1.val-(a:ℂ))- -(a:ℂ)) = _
  rw [sub_neg_eq_add,sub_add_cancel]
  simpa only [hinj.eq_iff] using hb (idx i) (idx j)

open Classical in
/-- Paper: Theorem 7.4.1.1(2), p. 366, using Theorem 7.1.4.2(3).
The jet functionals and their full biorthogonal families transport to the shifted
quotient. A zero z of the unshifted generator has its jets at z − a. -/
theorem exists_spectralNuclearityBiorthogonal (a : ℝ) :
    ∃ (d : jets(χ, τ, hτ) → StrongDual ℂ (Q(a))) (b : jets(χ, τ, hτ) → Q(a)),
      (∀ i f, d i ((D(a)).mkQ f) = iteratedDeriv i.2.val f.val (i.1.val - (a : ℂ))) ∧
      ∀ i j, d i (b j) = if i = j then 1 else 0 := by
  choose b hb using exists_spectralNuclearityBiorthogonal_vectors χ τ hτ a
  let J : jets(χ, τ, hτ) → B →L[ℂ] ℂ := fun i ↦
    (entireJet (i.1.val - (a : ℂ)) i.2.val).comp schwartzBergmanEntireInclusion
  have hJv (i : jets(χ, τ, hτ)) (f : B) :
      J i f = iteratedDeriv i.2.val f.val (i.1.val - (a : ℂ)) :=
    congrArg (fun g ↦ iteratedDeriv i.2.val g (i.1.val - (a : ℂ)))
      (funext (schwartzBergmanEntireInclusion_apply f))
  have hJ (i : jets(χ, τ, hτ)) : D(a) ≤ (J i).ker := fun f hf ↦ by
    obtain ⟨u, hu, h⟩ := (specDenom_mem_D χ τ hτ a f).mp hf
    refine LinearMap.mem_ker.mpr ((hJv i f).trans ?_)
    exact exists_spectralNuclearityBiorthogonal_vanish _ u f.val (Λ(χ, τ, hτ)).property hu
      (a : ℂ) h i.1.val i.2.val i.2.isLt
  refine ⟨fun i ↦ (D(a)).liftQL (J i) (hJ i), fun j ↦ (D(a)).mkQ (b j),
    fun i f ↦ hJv i f, fun i j ↦ (hJv i (b j)).trans (hb j i)⟩

section SpectralTraceEstimates

open Filter
open scoped SchwartzMap FourierTransform ContDiff
local notation "C₁" => (ideleClassNorm F).ker
local notation "σ₀(" r ")" => (QuotientGroup.mk (canonicalIdeleNormSection F
  (Units.mk0 (Real.exp r).toNNReal (by positivity))) : C𝔽)

private theorem spectralNuclearity_trace_section_norm (r : ℝ) :
    ideleClassNorm F (σ₀(r)) =
      Units.mk0 (Real.exp r).toNNReal (by positivity) :=
  canonicalIdeleNormSection_rightInverse F _

private theorem spectralNuclearity_trace_coset_norm (r : ℝ) (h : C₁) :
    (((ideleClassNorm F (σ₀(r) * h.val)).val : ℝ≥0) : ℝ) = Real.exp r := by
  rw [map_mul, show ideleClassNorm F h.val = 1 from h.property, mul_one, spectralNuclearity_trace_section_norm,
    Units.val_mk0, Real.coe_toNNReal _ (Real.exp_pos r).le]

/-- A Schwartz–Bruhat function on a group identified with the positive real line has a Schwartz
profile in logarithmic coordinates. -/
private theorem spectralNuclearity_trace_schwartz_log {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (d : G ≃ₜ* ℝ≥0ˣ) (f : SchwartzBruhat G) :
    ∃ b : 𝓢(ℝ, ℂ), ∀ x : G, b (Real.log ((d x).val : ℝ)) = f x := by
  let m : G →ₜ* ℝ≥0ˣ := ⟨d.toMulEquiv.toMonoidHom, d.continuous⟩
  let s : ℝ≥0ˣ →ₜ* G := ⟨d.symm.toMulEquiv.toMonoidHom, d.symm.continuous⟩
  have hm : IsModulation m := ⟨d.toHomeomorph.isProperMap, by
    obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
    exact ⟨d.symm t, fun h ↦ ht ((d.apply_symm_apply t).symm.trans h)⟩⟩
  let : MeasurableSpace G := borel _
  let : BorelSpace G := ⟨rfl⟩
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SecondCountableTopology G := d.toHomeomorph.isEmbedding.secondCountableTopology
  let K := m.toMonoidHom.ker
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let μ : Measure K := Measure.haar
  let proj := schwartzBruhatIsotypicProjector m hm μ 1
  have hPf (u : SchwartzBruhat G) : proj u = u := by
    apply schwartzBruhatIsotypicProjector_apply_isotype
    apply (mem_actionIsotype _ _ _).2
    intro k
    have hk : (k : G) = 1 := d.injective (k.property.trans d.map_one.symm)
    change schwartzBruhatTranslationAction (G := G) (k : G) u = ((1 : PontryaginDual K) k : ℂ) • u
    rw [hk, map_one, PontryaginDual.one_apply, Circle.coe_one, one_smul]
    rfl
  obtain ⟨w, e, hw, he⟩ := schwartzBruhat_positiveReal_isotype_equiv m hm μ s d.apply_symm_apply 1
  let v := e.symm (proj.ker.mkQ f)
  have h : proj.ker.mkQ (w v) = proj.ker.mkQ f := (he v).symm.trans (e.apply_symm_apply _)
  have hmem := (Submodule.Quotient.eq _).mp h
  change proj (w v - f) = 0 at hmem
  have hwv : w v = f := sub_eq_zero.mp ((hPf _).symm.trans hmem)
  have hv (x : G) : v (d x) = f x := by
    have hh := hw v 1 (d x)
    change w v (1 * d.symm (d x)) = _ at hh
    simpa [hwv] using hh.symm
  let I : Set ℝ := {0}
  let idm := ContinuousMonoidHom.id ℝ≥0ˣ
  let u : ModulatedExponentialDecay idm I := ⟨v.val, by
    change v.val ∈ modulatedExponentialDecaySubmodule idm {0}
    rw [modulatedExponentialDecaySubmodule_singleton_zero]
    exact v.property⟩
  obtain ⟨L,hL⟩ := identityModulationExponentialDecay_equiv I (ordConnected_singleton)
    (singleton_nonempty 0)
  let z := L.symm u
  let a : I := ⟨0, rfl⟩
  refine ⟨logExponentialDecayTwist I a z, fun x ↦ ?_⟩
  refine (logExponentialDecayTwist_apply I a z _).trans ?_
  change (Real.exp (0 * _) : ℂ) * z.val _ = _
  simp only [zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul]
  exact (hL z (d x)).symm.trans ((congrArg (fun t : ModulatedExponentialDecay idm I ↦ t.val (d x))
    (L.apply_symm_apply u)).trans (hv x))

/-- The character-weighted coset integral is smooth on the logarithmic norm line. -/
private theorem spectralNuclearity_trace_coset_profile (χ : PontryaginDual C𝔽) (φ : 𝒟) :
    ∃ b : 𝓢(ℝ, ℂ), ∀ x : ℝ, b x = ∫ h : C₁,
      (χ (σ₀(x) * h.val) : ℂ) * φ.val (σ₀(x) * h.val)
        ∂normOneIdeleClassTamagawaMeasure F := by
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let c : ℝ≥0ˣ → C𝔽 := fun u ↦ QuotientGroup.mk (canonicalIdeleNormSection F u)
  have hc : Continuous c :=
    QuotientGroup.continuous_mk.comp (canonicalIdeleNormSection_continuous F)
  have hcr : RightInverse c (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  let e : (C𝔽 ⧸ C₁) ≃ₜ* ℝ≥0ˣ :=
    { QuotientGroup.quotientKerEquivOfRightInverse (ideleClassNorm F) c hcr with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
        (isProperMap_ideleClassNorm F).continuous
      continuous_invFun := QuotientGroup.continuous_mk.comp hc }
  let f₀ : SchwartzBruhat C𝔽 := ⟨φ.val, bruhatCompactSupport_mem_schwartz φ.property⟩
  obtain ⟨proj, hP⟩ := schwartzBruhat_mul_unitaryCharacter χ
  have hK : IsCompact (C₁ : Set C𝔽) :=
    (isProperMap_ideleClassNorm F).isCompact_preimage isCompact_singleton
  let : LocallyCompactSpace C₁ := hK.isClosed.locallyCompactSpace
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : (normOneIdeleClassTamagawaMeasure F).Regular :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.2.1
  let f₁ := schwartzBruhatCosetIntegral C₁ (normOneIdeleClassTamagawaMeasure F) hK.isClosed (proj f₀)
  let : CommGroup (C𝔽 ⧸ C₁) := QuotientGroup.Quotient.commGroup C₁
  let : T2Space (C𝔽 ⧸ C₁) := e.toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace (C𝔽 ⧸ C₁) := e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  obtain ⟨b, hb⟩ := spectralNuclearity_trace_schwartz_log e f₁
  refine ⟨b, fun x ↦ ?_⟩
  let q : C𝔽 ⧸ C₁ := QuotientGroup.mk (σ₀(x))
  have hq : Real.log ((e q).val : ℝ) = x := by
    change Real.log ((ideleClassNorm F (σ₀(x))).val : ℝ) = x
    rw [spectralNuclearity_trace_section_norm, Units.val_mk0, Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp]
  calc
      b x = f₁ q := (congrArg b hq.symm).trans (hb q)
      _ = ∫ h : C₁, (proj f₀) (σ₀(x) * h.val) ∂normOneIdeleClassTamagawaMeasure F :=
        schwartzBruhatCosetIntegral_mk C₁ (normOneIdeleClassTamagawaMeasure F) hK.isClosed (proj f₀) _
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with h
        exact hP f₀ (σ₀(x) * h.val)

/-- Disintegrate idèle-class Tamagawa measure over the norm-one classes and the real logarithmic
norm. -/
private theorem spectralNuclearity_trace_integral_log_norm (σ : ℝ≥0ˣ → C𝔽) (hσ : Continuous σ)
    (hσnorm : RightInverse σ (ideleClassNorm F)) (f : C𝔽 → ℂ)
    (hfc : Continuous f) (hf : Integrable f (ideleClassTamagawaMeasure F)) :
    (∫ g, f g ∂ideleClassTamagawaMeasure F) = ∫ y : ℝ,
      ∫ h : C₁, f (σ (Units.mk0 (Real.exp y).toNNReal (by positivity)) * h.val)
        ∂normOneIdeleClassTamagawaMeasure F := by
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let : (ideleClassTamagawaMeasure F).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : MeasurableSpace (C𝔽 ⧸ C₁) := borel _
  let : BorelSpace (C𝔽 ⧸ C₁) := ⟨rfl⟩
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let d : C𝔽 ⧸ C₁ ≃ₜ* ℝ≥0ˣ :=
    { QuotientGroup.quotientKerEquivOfRightInverse (ideleClassNorm F) σ hσnorm with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
        (isProperMap_ideleClassNorm F).continuous
      continuous_invFun := QuotientGroup.continuous_mk.comp hσ }
  let D := d.toHomeomorph.toMeasurableEquiv
  let ν := positiveRealHaar.comap (QuotientGroup.kerLift (ideleClassNorm F))
  have hν : positiveRealHaar.map D.symm = ν := D.map_symm
  have hWeil := normOneIdeleClassTamagawaMeasure_isWeil F
  have havg := weilQuotientIntegral_L1 C₁
    (isClosed_singleton.preimage (isProperMap_ideleClassNorm F).continuous)
    (ideleClassTamagawaMeasure F) (normOneIdeleClassTamagawaMeasure F) ν hWeil hf
  let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have he (y : ℝ) : e y = Units.mk0 (Real.exp y).toNNReal (by positivity) :=
    Units.ext (NNReal.eq (Real.coe_toNNReal _ (Real.exp_pos y).le).symm)
  have hE : positiveRealHaar = volume.map e := by
    unfold positiveRealHaar
    congr 1
    exact funext fun y ↦ (he y).symm
  rw [havg.2.2, ← hν, integral_map_equiv, hE]
  change (∫ t, lcaCosetIntegral C₁ (normOneIdeleClassTamagawaMeasure F) f (D.symm t)
    ∂volume.map e) = _
  rw [show (⇑e) = ⇑e.toMeasurableEquiv from rfl, integral_map_equiv]
  apply integral_congr_ae
  filter_upwards with y
  change lcaCosetIntegral C₁ _ f (D.symm (e y)) = _
  rw [he]
  change lcaCosetIntegral C₁ _ f (QuotientGroup.mk (σ _)) = _
  apply lcaCosetIntegral_mk
  exact (hfc.comp (continuous_const.mul continuous_subtype_val)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The test Mellin transform is the ordinary Mellin transform of a compactly supported smooth
logarithmic profile. -/
private theorem spectralNuclearity_trace_mellin_profile (χ : PontryaginDual C𝔽) (φ : 𝒟) :
    ∃ b : 𝓢(ℝ, ℂ), HasCompactSupport (b : ℝ → ℂ) ∧ ∀ s : ℂ,
      nuclearityTestMellin χ φ s = mellin (fun t : ℝ ↦ b (Real.log t)) s := by
  obtain ⟨b, hb⟩ := spectralNuclearity_trace_coset_profile χ φ
  let L (g : C𝔽) := Real.log ((ideleClassNorm F g).val : ℝ)
  have hL : Continuous L :=
    Real.continuousOn_log.comp_continuous (NNReal.continuous_coe.comp
      (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous))
      fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  have hK : IsCompact (L '' tsupport φ.val) := φ.property.2.image hL
  have hbc : HasCompactSupport (b : ℝ → ℂ) := by
    apply hK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hK.isClosed
    intro t ht
    by_contra hno
    apply ht
    rw [hb]
    apply integral_eq_zero_of_ae
    filter_upwards with g
    have ht' : σ₀(t) * g.val ∉ tsupport φ.val := fun hsup ↦
      hno ⟨_, hsup, by dsimp [L]; rw [spectralNuclearity_trace_coset_norm, Real.log_exp]⟩
    simp only [image_eq_zero_of_notMem_tsupport ht', mul_zero, Pi.zero_apply]
  refine ⟨b, hbc, fun s ↦ ?_⟩
  let σ : ℝ≥0ˣ → C𝔽 := fun u ↦ QuotientGroup.mk (canonicalIdeleNormSection F u)
  have hσ : Continuous σ := QuotientGroup.continuous_mk.comp (canonicalIdeleNormSection_continuous F)
  have hφ : Continuous φ.val :=
    schwartzBruhat_continuous (⟨φ.val, bruhatCompactSupport_mem_schwartz φ.property⟩ : SchwartzBruhat C𝔽)
  refine (spectralNuclearity_trace_integral_log_norm σ hσ (canonicalIdeleNormSection_rightInverse F)
    (fun g ↦ φ.val g * ideleClassNormTwist χ s g) (hφ.mul (ideleClassNormTwist χ s).continuous)
    ((nuclearityTestMellin_integrable χ φ).1 s)).trans ?_
  rw [mellin, ← integral_comp_exp]
  apply integral_congr_ae
  filter_upwards with y
  simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
  rw [hb, ← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with g
  let w := σ₀(y) * g.val
  change φ.val w * ((χ w : ℂ) * (((ideleClassNorm F w).val : ℝ) : ℂ) ^ s) = _
  rw [show ((ideleClassNorm F w).val : ℝ) = Real.exp y from spectralNuclearity_trace_coset_norm y g]
  have hp : (Real.exp y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos y).ne'
  rw [Complex.cpow_sub _ _ hp, Complex.cpow_one]
  dsimp [w]
  field_simp

/-- On each bounded vertical strip the Mellin transform of a compactly supported test decays
faster than any fixed inverse power of the height. -/
private theorem spectralNuclearity_trace_vertical_decay (χ : PontryaginDual C𝔽) (φ : 𝒟) (a b : ℝ)
    (hab : a < b) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C > (0 : ℝ), ∀ᶠ y : ℝ in comap abs atTop, ∀ σ ∈ Icc a b,
      ‖nuclearityTestMellin χ φ ((σ : ℂ) + y * Complex.I)‖ ≤ C / |y| ^ k := by
  obtain ⟨f, hs, hf⟩ := spectralNuclearity_trace_mellin_profile χ φ
  have hwt (r : ℝ) (_ : r ∈ Icc a b) : ∃ g : 𝓢(ℝ, ℂ), ∀ x : ℝ, g x = (Real.exp (r * x) : ℂ) * f x := by
    let v := fun x : ℝ ↦ (Real.exp (r * x) : ℂ) * f x
    have hv : ContDiff (ℝ) (∞) v :=
      (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))).mul
        (f.smooth _)
    have hvc : HasCompactSupport v := hs.mul_left
    exact ⟨hvc.toSchwartzMap hv, fun _ ↦ rfl⟩
  simpa only [hf] using mellin_eventualHeightBound_of_weighted_schwartz f a b hab hwt k hk

/-- A summable weighted zero count dominates functions that decay quadratically outside bounded
height. -/
private theorem spectralNuclearity_trace_summable_of_decay {ι : Type*} (y m : ι → ℝ)
    (hm : ∀ i, 1 ≤ m i) (hmw : Summable (fun i ↦ m i / (1 + |y i|) ^ 2))
    (f : ι → ℂ) (C : ℝ) (hC : 0 < C)
    (hf : ∀ᶠ t : ℝ in comap abs atTop, ∀ i, y i = t → ‖f i‖ ≤ C / |t| ^ 2) :
    Summable (fun i ↦ m i * ‖f i‖) := by
  have hy : Tendsto (fun i ↦ |y i|) cofinite atTop := by
    apply tendsto_atTop.2
    intro T
    let R := max T 1
    have hp : 0 < R := zero_lt_one.trans_le (le_max_right _ _)
    have he : 0 < 1 / (1 + R) ^ 2 := by positivity
    filter_upwards [hmw.tendsto_cofinite_zero.eventually_lt_const he] with i hi
    by_contra! h
    have hlt : |y i| < R := lt_of_lt_of_le h (le_max_left _ _)
    have hle : (1 + |y i|) ^ 2 ≤ (1 + R) ^ 2 := by gcongr
    have hh := div_le_div_of_nonneg_left (zero_le_one : (0 : ℝ) ≤ 1) (by positivity : 0 < (1 + |y i|) ^ 2) hle
    exact (not_lt_of_ge (hh.trans (div_le_div_of_nonneg_right (hm i) (by positivity)))) hi
  have hfreq : Tendsto y cofinite (comap abs atTop) := tendsto_comap_iff.mpr hy
  refine (hmw.mul_left (4 * C)).of_norm_bounded_eventually ?_
  filter_upwards [hfreq.eventually hf, hy.eventually_ge_atTop 1] with i hi hi1
  rw [Real.norm_of_nonneg (mul_nonneg (zero_le_one.trans (hm i)) (norm_nonneg _))]
  have hp : 0 < |y i| := zero_lt_one.trans_le hi1
  have hsq : (1 + |y i|) ^ 2 ≤ 4 * |y i| ^ 2 := by nlinarith
  have hdom : C / |y i| ^ 2 ≤ (4 * C) / (1 + |y i|) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hsq hC.le]
  calc _ ≤ m i * ((4 * C) / (1 + |y i|) ^ 2) :=
           mul_le_mul_of_nonneg_left ((hi i rfl).trans hdom) (zero_le_one.trans (hm i))
       _ = _ := by ring

local notation "right(" a ")" => (Complex.re ⁻¹' Ioi (a : ℝ))
local notation "zeroOrder(" χ ", " s ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ s
local notation "windowZeros(" χ ", " d ")" =>
  {s : ℂ // 0 < zeroOrder(χ, s) ∧ |s.re - 1 / 2| < (d : ℝ)}
/-- Removing the gamma factor gives a continuation of the finite L-function. The entire
reciprocal gamma factor can only increase the order at a zero. -/
private theorem spectralNuclearity_trace_finite_companion (χ : U) :
    ∃ L : ℂ → ℂ, MeromorphicNFOn L univ ∧ (∀ z : right(1), L z = finiteHeckeL χ z) ∧
      ∀ z, meromorphicOrderAt (continuedCompletedHeckeL χ) z ≤ meromorphicOrderAt L z := by
  let Λ := continuedCompletedHeckeL χ
  let G (z : ℂ) := (heckeGammaFactor χ z)⁻¹
  let product := G * Λ
  obtain ⟨hΛ, hval⟩ := continuedCompletedHeckeL_spec χ
  have hG := differentiable_inv_heckeGammaFactor χ
  have hm : MeromorphicOn product univ := fun z hz ↦
    (hG.analyticAt z).meromorphicAt.mul (hΛ hz).meromorphicAt
  refine ⟨toMeromorphicNFOn product univ, meromorphicNFOn_toMeromorphicNFOn _ _, ?_, ?_⟩
  · intro z
    have hγ := heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans z.property)
    have hNF : MeromorphicNFAt product z :=
      (meromorphicNFAt_mul_iff_right (hG.analyticAt z) (inv_ne_zero hγ)).2 (hΛ (mem_univ _))
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ _), toMeromorphicNFAt_eq_self.mpr hNF]
    simp [product, Λ, G, hval z, completedHeckeL, finiteHeckeL, hγ]
  · intro z
    rw [meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ _),
      show meromorphicOrderAt product z = _ from meromorphicOrderAt_mul
        (hG.analyticAt z).meromorphicAt (hΛ (mem_univ z)).meromorphicAt]
    exact le_add_of_nonneg_left (hG.analyticAt z).meromorphicOrderAt_nonneg

/-- Zeros in a vertical strip, counted with multiplicity, have a summable quadratic weight. -/
private theorem spectralNuclearity_trace_zero_count (χ : U) (a : ℝ) :
    Summable (fun r : windowZeros(χ, a) ↦ (zeroOrder(χ, r.val) : ℝ) / (1 + |r.val.im|) ^ 2) := by
  obtain ⟨L, hL, hSeries, hOrder⟩ := spectralNuclearity_trace_finite_companion χ
  obtain ⟨hLine, k, _, hInv⟩ := finiteHeckeL_inv_isBigO_oneLine χ L hL hSeries
  exact summable_divisor_div_one_add_abs_im_sq (k := k) (σ := 1)
    (continuedCompletedHeckeL_spec χ).1.meromorphicOn hL hOrder
    (finiteHeckeL_continuation_isBigO_rpow χ L hL hSeries) (hLine.mono fun _ ht ↦ ht.2)
    hInv (1 / 2) a

private theorem spectralNuclearity_trace_zero_re_lt_one (χ : PontryaginDual C𝔽) {z : ℂ}
    (hz : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) z) : z.re < 1 := by
  rcases le_or_gt z.re 0 with h | h
  · exact h.trans_lt zero_lt_one
  · obtain ⟨hL, heq⟩ := continuedCompletedHeckeL_spec χ
    exact completedHeckeL_continuation_zeros χ _ hL heq h hz

private theorem spectralNuclearity_trace_zero_strip (χ : U) {z : ℂ} (hz : 0 < zeroOrder(χ, z)) :
    0 < z.re ∧ z.re < 1 := by
  obtain ⟨hL, hLh⟩ := continuedCompletedHeckeL_spec χ
  have hp : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) z := by
    rw [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _)] at hz
    cases he : meromorphicOrderAt (continuedCompletedHeckeL χ) z with
    | top => simp
    | coe k =>
      rw [he, WithTop.untop₀_coe] at hz
      exact_mod_cast hz
  have hu := spectralNuclearity_trace_zero_re_lt_one χ hp
  obtain ⟨hD, hDh⟩ := continuedCompletedHeckeL_spec χ⁻¹
  obtain ⟨ε, hε, hne, hfe⟩ :=
    completedHeckeL_continuation_functionalEquation χ _ _ hL hLh hD hDh
  have hcomp : meromorphicOrderAt (fun s ↦ continuedCompletedHeckeL χ⁻¹ (1 - s)) z =
      meromorphicOrderAt (continuedCompletedHeckeL χ⁻¹) (1 - z) := by
    simpa [Function.comp_def] using
      meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL χ⁻¹)
        (show AnalyticAt ℂ (fun s : ℂ ↦ 1 - s) z by fun_prop)
        (show deriv (fun s : ℂ ↦ 1 - s) z ≠ 0 by simp)
  rw [show (fun s ↦ continuedCompletedHeckeL χ⁻¹ (1 - s)) =
      ε * continuedCompletedHeckeL χ from funext hfe,
    meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt z) (hne z)] at hcomp
  have hl := spectralNuclearity_trace_zero_re_lt_one χ⁻¹ (hcomp ▸ hp)
  rw [Complex.sub_re, Complex.one_re] at hl
  exact ⟨by linarith, hu⟩

/-- The trace terms for the untruncated divisor are absolutely summable throughout the shifted
critical strip. -/
private theorem spectralNuclearity_trace_divisor_summable (χ : U) (φ : 𝒟) (a : ℝ) :
    Summable (fun z : {s : ℂ // 0 < zeroOrder(χ, s)} ↦
      ‖(zeroOrder(χ, z.val) : ℂ) * nuclearityTestMellin χ φ (z.val - (a : ℂ))‖) := by
  let Z := {s : ℂ // 0 < zeroOrder(χ, s)}
  have hstrip (z : Z) : 0 < z.val.re ∧ z.val.re < 1 := spectralNuclearity_trace_zero_strip χ z.property
  let e (z : Z) : windowZeros(χ, 1) := ⟨z.val, z.property, by
    obtain ⟨hl, hu⟩ := hstrip z
    exact abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  have he : Injective e := fun _ _ h ↦ Subtype.ext (congrArg (fun r : windowZeros(χ, 1) ↦ r.val) h)
  have hs := (spectralNuclearity_trace_zero_count χ 1).comp_injective he
  have hm (z : Z) : 1 ≤ (zeroOrder(χ, z.val) : ℝ) := by
    exact_mod_cast (show (1 : ℤ) ≤ zeroOrder(χ, z.val) from z.property)
  obtain ⟨C, hC, hf⟩ := spectralNuclearity_trace_vertical_decay χ φ (-a) (1 - a) (by linarith) 2 (by decide)
  have H := spectralNuclearity_trace_summable_of_decay (ι := Z) (fun z ↦ z.val.im)
    (fun z ↦ (zeroOrder(χ, z.val) : ℝ)) hm hs
    (fun z ↦ nuclearityTestMellin χ φ (z.val - (a : ℂ))) C hC (by
      filter_upwards [hf] with t ht z heq
      have hre := hstrip z
      have hb : (z.val - (a : ℂ)).re ∈ Icc (-a) (1 - a) := by
        simp only [Complex.sub_re, Complex.ofReal_re, mem_Icc]
        constructor <;> linarith [hre.1, hre.2]
      have hh := ht _ hb
      have him : (z.val - (a : ℂ)).im = t := by simpa using heq
      rwa [← him, Complex.re_add_im, him] at hh)
  apply H.congr
  intro z
  rw [norm_mul, Complex.norm_intCast, abs_of_nonneg (zero_le_one.trans (hm z))]

/-- At a zero of the regularized completed function, its finite analytic multiplicity is exactly
the order in the original divisor. -/
private theorem spectralNuclearity_trace_zero_order (χ : U) (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F)
    (hτ : RightInverse τ (ideleNorm F)) (z : zeros(χ, τ, hτ)) :
    ∃ k : ℕ, 0 < k ∧ analyticOrderAt ((Λ(χ, τ, hτ)).val : ℂ → ℂ) z.val = k ∧
      zeroOrder(χ, z.val) = k := by
  classical
  let G := Λ(χ, τ, hτ)
  let L := continuedCompletedHeckeL χ
  obtain ⟨hL, heq⟩ := continuedCompletedHeckeL_spec χ
  let x := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
  let b := (x : ℂ) * Complex.I
  let δ : ℕ := if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0
  let product (s : ℂ) := (s + b) ^ δ * (1 - s - b) ^ δ
  have hA : AnalyticAt ℂ (G.val : ℂ → ℂ) z.val := G.property.analyticAt _
  have hP (s : ℂ) : AnalyticAt ℂ product s := by
    dsimp only [product]
    fun_prop
  have hG0 : G.val z.val = 0 := hA.analyticOrderAt_ne_zero.mp z.property.ne'
  have hP0 : product z.val ≠ 0 := by
    by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
    · obtain ⟨h₀, h₁⟩ := regularizedCompletedHeckeL_ne_zero_at_canceled_poles χ τ hτ L hL heq hχ
      have hn₀ : z.val ≠ -b := fun e ↦ h₀ (e ▸ hG0)
      have hn₁ : z.val ≠ 1 - b := fun e ↦ h₁ (e ▸ hG0)
      have hsum : z.val + b ≠ 0 := fun e ↦ hn₀ (by linear_combination e)
      have hdiff : 1 - z.val - b ≠ 0 := fun e ↦ hn₁ (by linear_combination -e)
      simpa [product, δ, hχ] using mul_ne_zero hsum hdiff
    · simp [product, δ, hχ]
  have hmer : MeromorphicOn (product * L) univ := fun s hs ↦
    (hP s).meromorphicAt.mul (hL hs).meromorphicAt
  have horder : meromorphicOrderAt (G.val : ℂ → ℂ) z.val = meromorphicOrderAt L z.val := by
    change meromorphicOrderAt (toMeromorphicNFOn (product * L) univ) z.val = _
    rw [meromorphicOrderAt_toMeromorphicNFOn hmer (mem_univ _),
      meromorphicOrderAt_mul (hP _).meromorphicAt (hL (mem_univ _)).meromorphicAt,
      (hP _).meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr hP0)]
    simp [L]
  have htwo : meromorphicOrderAt L 2 ≠ ⊤ := by
    intro h
    have hp : 0 < meromorphicOrderAt L 2 := h ▸ WithTop.coe_lt_top (0 : ℤ)
    have hb := completedHeckeL_continuation_zeros χ _ hL heq (by norm_num : 0 < (2 : ℂ).re) hp
    norm_num at hb
  have hfin := hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ z.val) htwo
  rw [hA.meromorphicOrderAt_eq] at horder
  have hne : analyticOrderAt (G.val : ℂ → ℂ) z.val ≠ ⊤ := by
    intro h
    rw [h] at horder
    exact hfin horder.symm
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
  have hz := z.property
  change 0 < analyticOrderAt (G.val : ℂ → ℂ) z.val at hz
  rw [← hk] at hz horder
  refine ⟨k, by exact_mod_cast hz, hk.symm, ?_⟩
  rw [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _), ← horder]
  simp

private theorem spectralNuclearity_trace_term_summable (χ : U) (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F)
    (hτ : RightInverse τ (ideleNorm F)) (a : ℝ) (N : ℕ) (φ : 𝒟) :
    Summable (fun z : zeros(χ, τ, hτ) ↦
      ‖((min N (analyticOrderAt ((Λ(χ, τ, hτ)).val : ℂ → ℂ) z.val).toNat : ℕ) : ℂ) *
        nuclearityTestMellin χ φ (z.val - (a : ℂ))‖) := by
  classical
  let ι (z : zeros(χ, τ, hτ)) : {s : ℂ // 0 < zeroOrder(χ, s)} :=
    ⟨z.val, by
      obtain ⟨k, hk, _, he⟩ := spectralNuclearity_trace_zero_order χ τ hτ z
      rw [he]
      exact_mod_cast hk⟩
  have hinj : Injective ι := fun _ _ e ↦ Subtype.ext (congrArg (fun r : {s : ℂ // 0 < zeroOrder(χ, s)} ↦ r.val) e)
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _
    ((spectralNuclearity_trace_divisor_summable χ φ a).comp_injective hinj)
  intro z
  obtain ⟨k, _, hord, hdiv⟩ := spectralNuclearity_trace_zero_order χ τ hτ z
  change _ ≤ ‖(zeroOrder(χ, z.val) : ℂ) * nuclearityTestMellin χ φ (z.val - (a : ℂ))‖
  rw [hord, hdiv, ENat.toNat_natCast, Int.cast_natCast, norm_mul, norm_mul,
    Complex.norm_natCast, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.min_le_right N k) (norm_nonneg _)

end SpectralTraceEstimates

open Classical in
/-- By the Leibniz rule, vanishing of the retained jets is invariant under Mellin multiplication.
The action therefore descends through both quotients. -/
private theorem spectralNuclearity_trace_descends (a : ℝ) (N : ℕ) (φ : 𝒟)
    (d : jets(χ, τ, hτ) → StrongDual ℂ (Q(a)))
    (hd : ∀ i f, d i ((D(a)).mkQ f) = iteratedDeriv i.2.val f.val (i.1.val - (a : ℂ)))
    (A : B →L[ℂ] B) (hA : ∀ f s, (A f).val s = nuclearityTestMellin χ φ s * f.val s)
    (hD : Set.MapsTo A (D(a) : Set B) (D(a))) :
    let K := ⨅ i : {i : jets(χ, τ, hτ) // i.2.val < N}, (d i.val).toLinearMap.ker
    let E := Q(a) ⧸ K
    ∃ (Aq : Q(a) →L[ℂ] Q(a)) (T : E →L[ℂ] E),
      (∀ f, Aq ((D(a)).mkQ f) = (D(a)).mkQ (A f)) ∧
      ∀ x, T (K.mkQ x) = K.mkQ (Aq x) := by
  intro K E
  let S := (D(a)).mapQ (D(a)) A.toLinearMap fun x hx ↦ hD hx
  let Aq : Q(a) →L[ℂ] Q(a) := ⟨S, (Submodule.isQuotientMap_mkQ (D(a))).continuous_iff.mpr
    ((Submodule.isQuotientMap_mkQ (D(a))).continuous.comp A.continuous)⟩
  have hAq (f : B) : Aq ((D(a)).mkQ f) = (D(a)).mkQ (A f) := rfl
  have hK (x : Q(a)) (hx : x ∈ K) : Aq x ∈ K := by
    obtain ⟨f, rfl⟩ := (D(a)).mkQ_surjective x
    rw [Submodule.mem_iInf] at hx ⊢
    intro i
    change d i.val (Aq ((D(a)).mkQ f)) = 0
    rw [hAq, hd]
    have hf : Differentiable ℂ f.val := fun z ↦
      (f.property.2.1 z (mem_univ _)).differentiableAt (Filter.univ_mem' fun _ ↦ mem_univ _)
    have hprod : (A f).val = nuclearityTestMellin χ φ * f.val := funext (hA f)
    rw [hprod, iteratedDeriv_mul
      (differentiable_nuclearityTestMellin χ φ).contDiff.contDiffAt
      hf.contDiff.contDiffAt]
    apply Finset.sum_eq_zero
    intro k _
    let j : jets(χ, τ, hτ) := ⟨i.val.1, i.val.2.val - k, (Nat.sub_le _ _).trans_lt i.val.2.isLt⟩
    have hzero : d j ((D(a)).mkQ f) = 0 :=
      hx ⟨j, (Nat.sub_le _ _).trans_lt i.property⟩
    rw [hd] at hzero
    exact mul_eq_zero_of_right _ hzero
  let T₀ := K.mapQ K Aq.toLinearMap hK
  let T : E →L[ℂ] E := ⟨T₀, (Submodule.isQuotientMap_mkQ K).continuous_iff.mpr
    ((Submodule.isQuotientMap_mkQ K).continuous.comp Aq.continuous)⟩
  exact ⟨Aq, T, hAq, fun _ ↦ rfl⟩

-- TODO(paper-gap): The proof on p. 367 gives no uniform boundedness estimate for
-- the rescaled biorthogonal vectors. Discreteness does not control zero counts,
-- enumeration order, or separation. It also does not imply N(z)! = O(|Im z|).

/-- The entire Schwartz–Bergman space is nuclear through the Fourier–Mellin equivalence. -/
private theorem spectralJet_sb_nuclear :
    IsNuclearTVS.{0} (SchwartzBergman (univ : Set ℝ)) := by
  let : PolynormableSpace ℂ (SchwartzBergman (univ : Set ℝ)) :=
    (schwartzBergman_frechet univ isOpen_univ ordConnected_univ univ_nonempty).choose_spec.1
  exact nuclear_of_equiv
    (positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty)
    (positiveRealExponentialDecay_nuclear univ ordConnected_univ univ_nonempty)

/-- In the actual retained quotient all nuclear presentations give the same trace. -/
private theorem spectralJet_unique_presentation_sum (a : ℝ) (N : ℕ) (d : jets(χ, τ, hτ) → StrongDual ℂ (Q(a))) :
    let Q := Q(a)
    let K := ⨅ i : {i : jets(χ, τ, hτ) // i.2.val < N}, (d i.val).toLinearMap.ker
    let E := Q ⧸ K
    letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    ∀ T : E →L[ℂ] E, Nonempty (NuclearPresentation T) → ∃! t : ℂ, ∀ r : NuclearPresentation T,
      Summable (fun n ↦ ‖r.coeff n * r.functional n (r.vector n).val‖) ∧
      HasSum (fun n ↦ r.coeff n * r.functional n (r.vector n).val) t := by
  intro Q K E T hr
  let D := D(a)
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsClosed (D : Set B) := schwartzBergmanDivisible_isClosed _
  have hB : IsNuclearTVS.{0} B := spectralJet_sb_nuclear
  let : T2Space B := hB.1
  let : PolynormableSpace ℂ B := hB.2.1
  let : T2Space Q := inferInstanceAs (T2Space (B ⧸ D))
  have hQ : IsNuclearTVS.{0} Q := isNuclearTVS_quotient hB D
  let : PolynormableSpace ℂ Q := hQ.2.1
  let : IsClosed (K : Set Q) := by
    change IsClosed (↑(⨅ i : {i : jets(χ, τ, hτ) // i.2.val < N}, (d i.val).toLinearMap.ker) : Set Q)
    rw [Submodule.coe_iInf]
    exact isClosed_iInter (fun i ↦ (d i.val).isClosed_ker)
  let : T2Space E := inferInstanceAs (T2Space (Q ⧸ K))
  have hE : IsNuclearTVS.{0} E := isNuclearTVS_quotient hQ K
  let : PolynormableSpace ℂ E := hE.2.1
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have hAP := dense_finiteRank_of_isNuclearTVS E hE
  exact exists_nuclearTrace_hasSum hAP T ((isNuclearOperator_iff_nonempty_presentation T).mpr hr)

open Classical in
/-- Paper: Theorem 7.4.1.1(2), pp. 366–367. Every finite set of zero sites has a
unique continuous projector onto its retained jets. Its range is finite dimensional
and invariant under the multiplier, whose restriction has the finite divisor trace. -/
private theorem spectralNuclearity_trace_finite_cluster (a : ℝ) (N : ℕ) (φ : 𝒟)
    (d : jets(χ,τ,hτ) → StrongDual ℂ (Q(a)))
    (hd : ∀ i f, d i ((D(a)).mkQ f) = iteratedDeriv i.2.val f.val (i.1.val-(a:ℂ))) :
    let Q := Q(a)
    let I := {i : jets(χ,τ,hτ) // i.2.val < N}
    let K := ⨅ i : I, (d i.val).toLinearMap.ker
    let E := Q ⧸ K
    ∀ (A : B →L[ℂ] B) (Aq : Q →L[ℂ] Q) (T : E →L[ℂ] E),
      (∀ f s, (A f).val s = nuclearityTestMellin χ φ s * f.val s) →
      (∀ f, Aq ((D(a)).mkQ f) = (D(a)).mkQ (A f)) →
      (∀ x, T (K.mkQ x) = K.mkQ (Aq x)) →
      ∀ (L : I → StrongDual ℂ E), (∀ i x, L i (K.mkQ x) = d i.val x) →
      ∀ C : Finset (zeros(χ,τ,hτ)), ∃ proj : E →L[ℂ] E,
        (∀ i x, L i (proj x) = if i.val.1 ∈ C then L i x else 0) ∧
        (∀ x, proj (proj x) = proj x) ∧ (∀ x, T (proj x) = proj (T x)) ∧
        FiniteDimensional ℂ proj.toLinearMap.range ∧
        (∃ T' : proj.toLinearMap.range →ₗ[ℂ] proj.toLinearMap.range,
          (∀ x, (T' x).val = T x.val) ∧ LinearMap.trace ℂ _ T' =
            ∑ z ∈ C, ((min N (multiplicity(χ,τ,hτ,z)) : ℕ):ℂ) * nuclearityTestMellin χ φ (z.val-(a:ℂ))) ∧
        ∀ R : E →L[ℂ] E, (∀ i x, L i (R x) = if i.val.1 ∈ C then L i x else 0) → R=proj := by
  classical
  intro Q I K E A Aq T hA hAq hT L hL C
  let n (z : zeros(χ,τ,hτ)) := min N (multiplicity(χ,τ,hτ,z))
  let t (i : I) : Fin (n i.val.1) := ⟨i.val.2.val,lt_min i.property i.val.2.isLt⟩
  let idx (z : zeros(χ,τ,hτ)) (j : Fin (n z)) : I :=
    ⟨⟨z,j.val,j.isLt.trans_le (min_le_right N _)⟩,j.isLt.trans_le (min_le_left N _)⟩
  choose f hf using exists_spectralNuclearityBiorthogonal_vectors χ τ hτ a
  let b (i : I) : E := K.mkQ ((D(a)).mkQ (f i.val))
  have bio (i j : I) : L i (b j) = if i=j then 1 else 0 := by
    change L i (K.mkQ ((D(a)).mkQ _)) = _
    rw [hL,hd,hf]
    simp only [Subtype.val_inj]
  have sep : Injective (fun x : E ↦ fun i : I ↦ L i x) := by
    intro x y h
    apply sub_eq_zero.mp
    obtain ⟨v,hv⟩ := K.mkQ_surjective (x-y)
    rw [←hv,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,Submodule.mem_iInf]
    intro i
    change d i.val v = 0
    rw [←hL,hv,map_sub,sub_eq_zero]
    exact congrFun h i
  let S := C.biUnion fun z ↦ Finset.univ.image (idx z)
  have memS (i : I) : i ∈ S ↔ i.val.1 ∈ C := by
    constructor
    · intro h
      obtain ⟨z,hz,hj⟩ := Finset.mem_biUnion.mp h
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hj
      exact hz
    · intro h
      exact Finset.mem_biUnion.mpr ⟨i.val.1,h,Finset.mem_image.mpr ⟨t i,Finset.mem_univ _,rfl⟩⟩
  let proj : E →L[ℂ] E := ∑ j ∈ S, (L j).smulRight (b j)
  have valP (x : E) : proj x = ∑ j ∈ S, L j x • b j := by
    simp [proj]
  have hp (i : I) (x : E) : L i (proj x) = if i.val.1 ∈ C then L i x else 0 := by
    rw [valP,map_sum]
    simp only [map_smul,bio,smul_eq_mul,mul_ite,mul_one,mul_zero]
    simp [Finset.sum_ite_eq,memS]
  let lower (i : I) (k : ℕ) : I :=
    ⟨⟨i.val.1,i.val.2.val-k,(Nat.sub_le _ _).trans_lt i.val.2.isLt⟩,(Nat.sub_le _ _).trans_lt i.property⟩
  have row (i : I) (x : E) : L i (T x) = ∑ k ∈ Finset.range (i.val.2.val+1),
      (i.val.2.val.choose k : ℂ) * iteratedDeriv k (nuclearityTestMellin χ φ) (i.val.1.val-(a:ℂ)) * L (lower i k) x := by
    obtain ⟨y,rfl⟩ := K.mkQ_surjective x
    obtain ⟨f,rfl⟩ := (D(a)).mkQ_surjective y
    rw [hT,hAq,hL,hd,show (A f).val = nuclearityTestMellin χ φ * f.val from funext (hA f)]
    have hf : Differentiable ℂ f.val := fun z ↦
      (f.property.2.1 z (mem_univ _)).differentiableAt (Filter.univ_mem' fun _ ↦ mem_univ _)
    rw [iteratedDeriv_mul (differentiable_nuclearityTestMellin χ φ).contDiff.contDiffAt
      hf.contDiff.contDiffAt]
    apply Finset.sum_congr rfl
    intro k _
    rw [hL,hd]
  have idem : ∀ x, proj (proj x) = proj x := by
    intro x
    apply sep
    funext i
    change L i (proj (proj x)) = L i (proj x)
    by_cases h : i.val.1 ∈ C <;> simp [hp,h]
  have comm : ∀ x, T (proj x) = proj (T x) := by
    intro x
    apply sep
    funext i
    change L i (T (proj x)) = L i (proj (T x))
    rw [row i (proj x),hp i (T x),row i x]
    by_cases h : i.val.1 ∈ C <;> simp [hp,lower,h]
  have finite : FiniteDimensional ℂ proj.toLinearMap.range := by
    let rangeSpace := Submodule.span ℂ (b '' (S : Set I))
    let : FiniteDimensional ℂ rangeSpace := FiniteDimensional.span_of_finite ℂ (S.finite_toSet.image b)
    have hsub : proj.toLinearMap.range ≤ rangeSpace := by
      rintro _ ⟨x,rfl⟩
      change proj x ∈ rangeSpace
      rw [valP]
      exact Submodule.sum_mem rangeSpace fun i hi ↦ rangeSpace.smul_mem _ (Submodule.subset_span ⟨i,hi,rfl⟩)
    exact FiniteDimensional.of_injective (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)
  refine ⟨proj,hp,idem,comm,finite,?_,?_⟩
  · let rangeSpace := proj.toLinearMap.range
    let : FiniteDimensional ℂ rangeSpace := finite
    let ℓ (i : I) : rangeSpace →ₗ[ℂ] ℂ := (L i).toLinearMap.comp rangeSpace.subtype
    let y (i : I) : rangeSpace := ⟨proj (T (b i)),⟨_,rfl⟩⟩
    let R : rangeSpace →ₗ[ℂ] rangeSpace := ∑ i ∈ S, (ℓ i).smulRight (y i)
    have pfix (x : rangeSpace) : proj x.val = x.val := by
      obtain ⟨u,hu⟩ := x.property
      change proj u = x.val at hu
      rw [←hu,idem]
    refine ⟨R,?_,?_⟩
    · intro x
      calc
        (R x).val = ∑ i ∈ S, L i x.val • proj (T (b i)) := by
          change rangeSpace.subtype (R x) = _
          simp only [R,LinearMap.sum_apply,map_sum,LinearMap.smulRight_apply,map_smul]
          rfl
        _ = proj (T (proj x.val)) := by rw [valP x.val,map_sum,map_sum]; simp only [map_smul]
        _ = T x.val := by rw [←comm,idem,pfix]
    · have diag (i : I) : L i (T (b i)) = nuclearityTestMellin χ φ (i.val.1.val-(a:ℂ)) := by
        rw [row,Finset.sum_eq_single 0]
        · have e0 : lower i 0 = i := by rfl
          rw [e0,bio,ite_eq_left rfl]
          simp
        · intro j hj hj0
          have hn : lower i j ≠ i := by
            intro he
            have eqv : i.val.2.val-j = i.val.2.val := congrArg (fun k : I ↦ k.val.2.val) he
            have hle := Finset.mem_range.mp hj
            omega
          rw [bio,ite_eq_right hn,mul_zero]
        · simp
      have dis : (C : Set _).PairwiseDisjoint (fun z ↦ Finset.univ.image (idx z)) := by
        intro z _ w _ hzw
        apply Finset.disjoint_left.mpr
        intro i hi hi'
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨k,_,h⟩ := Finset.mem_image.mp hi'
        exact hzw (congrArg (fun x : I ↦ x.val.1) h).symm
      calc
        LinearMap.trace ℂ rangeSpace R = ∑ i ∈ S, ℓ i (y i) := by simp only [R,map_sum,LinearMap.trace_smulRight]
        _ = ∑ i ∈ S, nuclearityTestMellin χ φ (i.val.1.val-(a:ℂ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          change L i (proj (T (b i))) = _
          rw [hp,ite_eq_left ((memS i).mp hi),diag]
        _ = _ := by
          rw [show S = C.biUnion (fun z ↦ Finset.univ.image (idx z)) from rfl, Finset.sum_biUnion dis]
          apply Finset.sum_congr rfl
          intro z _
          rw [Finset.sum_image (fun j _ k _ he ↦ Fin.ext (congrArg (fun u : I ↦ u.val.2.val) he))]
          simp [idx,n,nsmul_eq_mul]
  · intro R hR
    ext x
    apply sep
    funext i
    change L i (R x) = L i (proj x)
    rw [hR,hp]

section SpectralTraceHilbert

open Filter
open scoped InnerProductSpace

/-- The inclusion of the complete gauge space of a Banach disc into the ambient space is continuous. -/
private theorem spectralTrace_banachDisc_inclusion {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [PolynormableSpace ℂ E] {D : Set E} (hD : IsBanachDisc D) :
    Continuous (fun z : WithLocalSeminorm (gaugeSeminorm hD.balanced hD.convex hD.absorbent) ↦
      (show Submodule.span ℂ D from z).val) := by
  let G := WithLocalSeminorm (gaugeSeminorm hD.balanced hD.convex hD.absorbent)
  let i : G →ₗ[ℂ] E := (Submodule.span ℂ D).subtype
  let hE := PolynormableSpace.withSeminorms ℂ E
  refine hE.continuous_of_continuous_comp i fun j ↦ ?_
  obtain ⟨R, _, hR⟩ := hE.isVonNBounded_iff_seminorm_bounded.mp hD.bounded j
  refine Seminorm.continuous' (r := R) (mem_of_superset (Metric.ball_mem_nhds (0 : G) one_pos) ?_)
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have hzD : (show Submodule.span ℂ D from z) ∈ ((↑) ⁻¹' D : Set (Submodule.span ℂ D)) :=
    setOfPred_gauge_lt_one_subset_self hD.convex hD.absorbent.zero_mem hD.absorbent hz
  rw [Seminorm.mem_closedBall_zero]
  exact (hR (i z) hzD).le

/-- Synthesis of an absolutely summable, uniformly seminorm-bounded series into a Banach space. -/
private theorem spectralTrace_boundedSeries_toBanach {E Y : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [PolynormableSpace ℂ E] [SeminormedAddCommGroup Y] [NormedSpace ℂ Y] [T2Space Y] [CompleteSpace Y]
    (L : ℕ → StrongDual ℂ E) (b : ℕ → Y) (a : ℕ → ℂ) (ha : Summable (fun n ↦ ‖a n‖))
    (q : Seminorm ℂ E) (hq : Continuous q) (hL : ∀ n x, ‖L n x‖ ≤ q x) (hb : ∀ n, ‖b n‖ ≤ 1) :
    ∃ analysisMap : E →L[ℂ] Y, ∀ x, HasSum (fun n ↦ (a n * L n x) • b n) (analysisMap x) := by
  let term (x : E) (n : ℕ) := (a n * L n x) • b n
  have bound (x : E) (n : ℕ) : ‖term x n‖ ≤ ‖a n‖*q x := by
    calc
      _ = ‖a n‖*‖L n x‖*‖b n‖ := by simp only [term,norm_smul,norm_mul]
      _ ≤ ‖a n‖*q x*1 := by gcongr <;> first | exact hL _ _ | exact hb _
      _ = _ := mul_one _
  have hs (x : E) : Summable (term x) := (ha.mul_right (q x)).of_norm_bounded (bound x)
  let analysisMap : E →ₗ[ℂ] Y := {
    toFun x := ∑' n, term x n
    map_add' x y := ((hs (x+y)).hasSum.unique <| ((hs x).hasSum.add (hs y).hasSum).congr_fun (fun n ↦
      by simp only [term,map_add,mul_add,add_smul]))
    map_smul' c x := ((hs (c • x)).hasSum.unique <| ((hs x).hasSum.const_smul c).congr_fun (fun n ↦
      by simp only [term,map_smul,smul_eq_mul,smul_smul]; ring_nf)) }
  let M := ∑' n, ‖a n‖
  have hM : 0 ≤ M := tsum_nonneg (fun _ ↦ norm_nonneg _)
  have dominated (x : E) : ‖analysisMap x‖ ≤ M * q x := by
    calc
      _ ≤ ∑' n, ‖a n‖*q x := by
        have hnorm := Summable.of_nonneg_of_le (fun n ↦ norm_nonneg (term x n)) (bound x) (ha.mul_right (q x))
        exact (norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum (bound x) (ha.mul_right (q x)))
      _ = M*q x := tsum_mul_right
  let p := M.toNNReal • q
  have hp (x : E) : p x = M*q x := by simp [p,NNReal.smul_def,hM,Real.toNNReal_of_nonneg]
  have hpcont : Continuous p := by simpa only [show (⇑p) = (fun x ↦ M*q x) from funext hp] using hq.const_mul M
  have hU : Continuous analysisMap := (PolynormableSpace.withSeminorms ℂ E).continuous_normedSpace_rng Y analysisMap
    ⟨{⟨p,hpcont⟩},1,by simpa using (show (normSeminorm ℂ Y).comp analysisMap ≤ p from fun x ↦ (dominated x).trans_eq (hp x).symm)⟩
  exact ⟨⟨analysisMap,hU⟩,fun x ↦ (hs x).hasSum⟩

/-- Factor a rapid presentation through ℓ² by giving the synthesis vectors the weights `(n + 1)⁻²`.
Project away the kernel of synthesis to obtain an injective Hilbert-to-quotient map. -/
private theorem spectralTrace_rapidPresentation_hilbert {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [PolynormableSpace ℂ E] [T2Space E]
    (T : E →L[ℂ] E) (r : NuclearPresentation T)
    (hr : ∀ k : ℕ, ∃ C : ℝ, ∀ n, ‖r.coeff n‖*((n:ℝ)+1)^k ≤ C) :
    ∃ W : Submodule ℂ (lp (fun _ : ℕ ↦ ℂ) 2), IsClosed (W : Set (lp (fun _ : ℕ ↦ ℂ) 2)) ∧
      ∃ (analysisMap : E →L[ℂ] W) (synthesisMap : W →L[ℂ] E) (a : ℕ → ℂ) (b : ℕ → W), Injective synthesisMap ∧
        (∀ x, synthesisMap (analysisMap x) = T x) ∧ Summable (fun n ↦ ‖a n‖) ∧ (∀ n, ‖b n‖ ≤ 1) ∧
        (∀ x, HasSum (fun n ↦ (a n*r.functional n x) • b n) (analysisMap x)) ∧
        ∀ n, a n • synthesisMap (b n) = r.coeff n • (r.vector n).val := by
  let H := (lp (fun _ : ℕ ↦ ℂ) 2)
  let β (n : ℕ) := (((n:ℝ)+1)^2)⁻¹
  let α (n : ℕ) : ℂ := r.coeff n * (((n:ℂ)+1)^2)
  have hβ : Summable β := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
    simpa only [β,one_div,Nat.cast_add,Nat.cast_one] using h
  have hβn (n : ℕ) : ‖(β n:ℂ)‖ = β n := by rw [Complex.norm_real,Real.norm_of_nonneg (by dsimp [β]; positivity)]
  have ha : Summable (fun n ↦ ‖α n‖) := by
    obtain ⟨C,hC⟩ := hr 4
    apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ (hβ.mul_left C)
    intro n
    have hnc : ‖(n:ℂ)+1‖ = (n:ℝ)+1 := by
      rw [←Complex.ofReal_natCast,←Complex.ofReal_one,←Complex.ofReal_add,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
    change ‖r.coeff n * (((n:ℂ)+1)^2)‖ ≤ C / _
    rw [norm_mul,norm_pow,hnc,le_div_iff₀ (by positivity)]
    simpa only [mul_assoc,←pow_add] using hC n
  have hαβ (n : ℕ) : α n*(β n:ℂ) = r.coeff n := by
    dsimp only [α,β]; push_cast; field_simp
  let e (n : ℕ) : H := lp.single 2 n (1:ℂ)
  have he (n : ℕ) : ‖e n‖ ≤ 1 := by simp only [e,lp.norm_single (by norm_num : (0:ENNReal)<2),norm_one,le_refl]
  have hqfa := ((norm_withSeminorms ℂ ℂ).equicontinuous_tfae (fun n ↦ (r.functional n).toLinearMap)).out 1 4
  obtain ⟨q,hq,hqL⟩ := (hqfa.mp r.equicontinuous) ()
  obtain ⟨analysisMap,hU⟩ := spectralTrace_boundedSeries_toBanach r.functional e α ha q hq hqL he
  let G := WithLocalSeminorm (gaugeSeminorm r.isBanachDisc.balanced r.isBanachDisc.convex r.isBanachDisc.absorbent)
  let : CompleteSpace G := r.isBanachDisc.complete
  let : T2Space G := r.isBanachDisc.separated
  let j : G →L[ℂ] E := ⟨(Submodule.span ℂ r.disc).subtype,spectralTrace_banachDisc_inclusion r.isBanachDisc⟩
  let y (n : ℕ) : G := r.vector n
  have hy (n : ℕ) : ‖y n‖ ≤ 1 := gauge_le_one_of_mem (show r.vector n ∈ ((↑) ⁻¹' r.disc : Set (Submodule.span ℂ r.disc)) from r.vector_mem n)
  let eval (n : ℕ) : H →L[ℂ] ℂ := lp.evalCLM ℂ _ 2 n
  obtain ⟨Vg,hVg⟩ := spectralTrace_boundedSeries_toBanach eval y (fun n ↦ (β n:ℂ)) (by simpa only [hβn] using hβ)
    (normSeminorm ℂ H) continuous_norm (fun n x ↦ lp.norm_apply_le_norm (by norm_num) x n) hy
  let synthesisMap := j.comp Vg
  have hVe (n : ℕ) : synthesisMap (e n) = (β n:ℂ) • (r.vector n).val := by
    have hg : Vg (e n) = (β n:ℂ) • y n := by
      apply (hVg (e n)).unique
      have heval (k : ℕ) : eval k (e n) = if k=n then 1 else 0 := by
        change (lp.single (E := fun _ : ℕ ↦ ℂ) 2 n (1:ℂ)) k = _
        simp [lp.single_apply,Pi.single_apply,eq_comm]
      have hs := hasSum_single n (f := fun k ↦ ((β k:ℂ)*eval k (e n)) • y k) (fun k hkn ↦ by simp [heval,hkn])
      exact (show (β n:ℂ) • y n = ((β n:ℂ)*eval n (e n)) • y n by rw [heval]; simp) ▸ hs
    change j (Vg (e n)) = _
    rw [hg,map_smul]; rfl
  have hVU (x : E) : synthesisMap (analysisMap x) = T x := by
    refine ((hU x).mapL synthesisMap).unique ((r.hasSum x).congr_fun (fun n ↦ ?_))
    rw [map_smul,hVe,smul_smul,mul_right_comm,hαβ]
  let K := synthesisMap.toLinearMap.ker
  let : CompleteSpace K := synthesisMap.isClosed_ker.completeSpace_coe
  let W := Kᗮ
  let : CompleteSpace W := K.isClosed_orthogonal.completeSpace_coe
  let π := W.orthogonalProjectionOnto
  have hπ (x : H) : synthesisMap (π x).val = synthesisMap x := by
    have hx : x-(π x).val ∈ K := by
      simpa only [W,K.orthogonal_orthogonal,Submodule.starProjection_apply] using Submodule.sub_starProjection_mem_orthogonal (K := W) x
    change synthesisMap (x-(π x).val) = 0 at hx
    exact ((sub_eq_zero.mp <| (map_sub synthesisMap _ _) ▸ hx)).symm
  refine ⟨W,K.isClosed_orthogonal,π.comp analysisMap,synthesisMap.comp W.subtypeL,α,fun n ↦ π (e n),?_,
    fun x ↦ (hπ (analysisMap x)).trans (hVU x),ha,fun n ↦ (W.norm_orthogonalProjectionOnto_apply_le _).trans (he n),?_,?_⟩
  · change Injective (synthesisMap.comp W.subtypeL).toLinearMap
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    exact Subtype.ext ((Submodule.disjoint_def.mp K.isCompl_orthogonal.disjoint) _ hx x.property)
  · intro x
    simpa only [map_smul,ContinuousLinearMap.comp_apply] using (hU x).mapL π
  · intro n
    change α n • synthesisMap (π (e n)).val = _
    rw [hπ,hVe,smul_smul,hαβ]

/-- The Hilbert representation of a finite spectral mask computes its algebraic trace
without any estimate on the original (possibly very oblique) mask. -/
private theorem spectralTrace_rectangular {E H : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [T2Space E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (u : E →L[ℂ] H) (v : H →L[ℂ] E)
    (p : E →L[ℂ] E) (hid : ∀ x, p (p x) = p x) (hc : ∀ x, v (u (p x)) = p (v (u x)))
    (hfin : FiniteDimensional ℂ p.toLinearMap.range)
    (R : p.toLinearMap.range →ₗ[ℂ] p.toLinearMap.range) (hR : ∀ x, (R x).val = v (u x.val)) :
    let K := (p.comp v).toLinearMap.ker
    let W := Kᗮ
    FiniteDimensional ℂ W ∧
      LinearMap.trace ℂ W ((W.orthogonalProjectionOnto.comp ((u.comp v).comp W.subtypeL)).toLinearMap) =
        LinearMap.trace ℂ _ R := by
  classical
  intro K W
  let : CompleteSpace W := K.isClosed_orthogonal.completeSpace_coe
  let : CompleteSpace K := (p.comp v).isClosed_ker.completeSpace_coe
  let A : W →ₗ[ℂ] p.toLinearMap.range := (p.toLinearMap.rangeRestrict.comp v.toLinearMap).comp W.subtype
  have hA (x : W) : (A x).val = p (v x.val) := rfl
  have hinj : Injective A := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have he : x.val ∈ K := congrArg Subtype.val hx
    exact Subtype.ext ((Submodule.disjoint_def.mp K.isCompl_orthogonal.disjoint) _ he x.property)
  let : FiniteDimensional ℂ W := FiniteDimensional.of_injective A hinj
  refine ⟨inferInstance,?_⟩
  let backward := (W.orthogonalProjectionOnto.toLinearMap.comp u.toLinearMap).comp p.toLinearMap.range.subtype
  have hpk (y : H) : p (v (W.orthogonalProjectionOnto y).val) = p (v y) := by
    have he := Submodule.sub_starProjection_mem_orthogonal (K := W) y
    have hk : y - (W.orthogonalProjectionOnto y).val ∈ K := by simpa only [W,K.orthogonal_orthogonal,Submodule.starProjection_apply] using he
    change p (v (y - (W.orthogonalProjectionOnto y).val)) = 0 at hk
    rw [map_sub,map_sub,sub_eq_zero] at hk
    exact hk.symm
  have hpu (x : E) : W.orthogonalProjectionOnto (u (p x)) = W.orthogonalProjectionOnto (u x) := by
    apply sub_eq_zero.mp
    rw [←map_sub]
    change u (p x) - u x ∈ W.orthogonalProjectionOnto.ker
    rw [Submodule.ker_orthogonalProjectionOnto]
    change u (p x)-u x ∈ Kᗮᗮ
    rw [K.orthogonal_orthogonal]
    change p (v (u (p x)-u x)) = 0
    rw [map_sub,map_sub,hc,hid,sub_self]
  have compW : backward.comp A = (W.orthogonalProjectionOnto.comp ((u.comp v).comp W.subtypeL)).toLinearMap := by
    apply LinearMap.ext
    intro x
    change W.orthogonalProjectionOnto (u (p (v x.val))) = _
    exact hpu _
  have compE : A.comp backward = R := by
    ext x
    change p (v (W.orthogonalProjectionOnto (u x.val)).val) = (R x).val
    rw [hpk,hR,←hc]
    obtain ⟨z,hz⟩ := x.property
    change p z = x.val at hz
    rw [←hz,hid]
  rw [←compW,←compE]
  exact LinearMap.trace_comp_comm' _ _

/-- Any pointwise absolutely converging rank-one expansion on a finite-dimensional Hilbert
space gives its algebraic trace by contraction. -/
private theorem spectralTrace_finiteDimensional_series {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (T : H →ₗ[ℂ] H) (a : ℕ → ℂ) (L : ℕ → StrongDual ℂ H) (b : ℕ → H)
    (hT : ∀ x, HasSum (fun n ↦ (a n * L n x) • b n) (T x)) :
    HasSum (fun n ↦ a n * L n (b n)) (LinearMap.trace ℂ H T) := by
  classical
  let e := stdOrthonormalBasis ℂ H
  let D := Fin (Module.finrank ℂ H)
  let c (i : D) := innerSL ℂ (e i)
  have hs (i : D) (_ : i ∈ (Finset.univ : Finset D)) :
      HasSum (fun n ↦ (a n * L n (e i)) * c i (b n)) (c i (T (e i))) := by
    simpa only [map_smul,smul_eq_mul] using (hT (e i)).mapL (c i)
  have hsum := hasSum_sum hs
  have he (n : ℕ) : ∑ i : D, (a n*L n (e i))*c i (b n) = a n*L n (b n) := by
    calc
      _ = a n * L n (∑ i, c i (b n) • e i) := by
        simp only [map_sum,map_smul,smul_eq_mul,Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _; ring
      _ = _ := congrArg (fun y ↦ a n * L n y) (e.sum_repr' (b n))
  have ht : LinearMap.trace ℂ H T = ∑ i : D, c i (T (e i)) := by
    rw [LinearMap.trace_eq_matrix_trace ℂ e.toBasis,Matrix.trace]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.diag_apply,LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply,OrthonormalBasis.repr_apply_apply,c,innerSL_apply_apply]
  simpa only [ht,he] using hsum

/-- Finite supported trace approximations identify the numerical trace of an already rapid
presentation, irrespective of whether the cutoff operators are equicontinuous. -/
private theorem spectralTrace_of_finiteProjections {E Z : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [PolynormableSpace ℂ E] [T2Space E]
    (T : E →L[ℂ] E) (r : NuclearPresentation T)
    (hr : ∀ k : ℕ, ∃ C : ℝ, ∀ n, ‖r.coeff n‖*((n:ℝ)+1)^k ≤ C)
    (p : Finset Z → E →L[ℂ] E) (R : (C : Finset Z) → (p C).toLinearMap.range →ₗ[ℂ] (p C).toLinearMap.range)
    (hid : ∀ C x, p C (p C x) = p C x) (hc : ∀ C x, T (p C x) = p C (T x))
    (hfin : ∀ C, FiniteDimensional ℂ (p C).toLinearMap.range) (hR : ∀ C x, (R C x).val = T x.val)
    (hanti : ∀ C D, C ⊆ D → (p D).toLinearMap.ker ≤ (p C).toLinearMap.ker)
    (hsep : ∀ x, (∀ C, p C x = 0) → x=0) (t : ℂ)
    (hlen : Tendsto (fun C ↦ LinearMap.trace ℂ _ (R C)) atTop (𝓝 t)) :
    HasSum (fun n ↦ r.coeff n * r.functional n (r.vector n).val) t := by
  classical
  obtain ⟨H,hclosed,analysisMap,synthesisMap,a,b,hV,hvu,ha,hb,hU,hvec⟩ := spectralTrace_rapidPresentation_hilbert T r hr
  let : CompleteSpace H := hclosed.completeSpace_coe
  let K (C : Finset Z) := ((p C).comp synthesisMap).toLinearMap.ker
  let W (C : Finset Z) := (K C)ᗮ
  let (C : Finset Z) : CompleteSpace (K C) := ((p C).comp synthesisMap).isClosed_ker.completeSpace_coe
  let (C : Finset Z) : CompleteSpace (W C) := (K C).isClosed_orthogonal.completeSpace_coe
  have mono : Monotone W := by
    intro c d hcd
    apply Submodule.orthogonal_le
    exact fun x hx ↦ hanti c d hcd hx
  have dense : ⊤ ≤ (⨆ C, W C).topologicalClosure := by
    apply (Submodule.topologicalClosure_eq_top_iff.mpr ?_).ge
    rw [Submodule.eq_bot_iff]
    intro x hx
    apply hV
    rw [map_zero]
    apply hsep
    intro C
    have hm : x ∈ (W C)ᗮ := Submodule.orthogonal_le (le_iSup W C) hx
    change x ∈ K C
    simpa only [W,(K C).orthogonal_orthogonal] using hm
  have limit (y : H) := Submodule.starProjection_tendsto_self W mono y dense
  -- Contract in the orthogonal Hilbert cutoffs, whose operator norms are at most one.
  have hrect (C : Finset Z) := spectralTrace_rectangular analysisMap synthesisMap (p C) (hid C)
    (fun x ↦ by rw [hvu,hvu,hc]) (hfin C) (R C) (fun x ↦ (hR C x).trans (hvu x.val).symm)
  let d (C : Finset Z) (n : ℕ) := a n * r.functional n (synthesisMap ((W C).starProjection (b n)))
  have loc (C : Finset Z) : HasSum (d C) (LinearMap.trace ℂ _ (R C)) := by
    let : FiniteDimensional ℂ (W C) := (hrect C).1
    let π := (W C).orthogonalProjectionOnto
    let S := (π.comp ((analysisMap.comp synthesisMap).comp (W C).subtypeL)).toLinearMap
    let L (n : ℕ) := (r.functional n).comp (synthesisMap.comp (W C).subtypeL)
    have row (x : W C) : HasSum (fun n ↦ (a n * L n x) • π (b n)) (S x) := by
      simpa only [L,S,ContinuousLinearMap.comp_apply,Submodule.subtypeL_apply,ContinuousLinearMap.coe_coe,map_smul] using
        (hU (synthesisMap x.val)).mapL π
    have hl := spectralTrace_finiteDimensional_series S a L (fun n ↦ π (b n)) row
    have he : LinearMap.trace ℂ _ S = LinearMap.trace ℂ _ (R C) := (hrect C).2
    rw [←he]
    exact hl
  have hqfa := ((norm_withSeminorms ℂ ℂ).equicontinuous_tfae (fun n ↦ (r.functional n).toLinearMap)).out 1 4
  obtain ⟨q,hq,hqL⟩ := (hqfa.mp r.equicontinuous) ()
  obtain ⟨M,hM,hbound⟩ := (q.comp synthesisMap.toLinearMap).bound_of_continuous_normedSpace (hq.comp synthesisMap.continuous)
  have unif (n : ℕ) (y : H) (hy : ‖y‖ ≤ 1) : ‖r.functional n (synthesisMap y)‖ ≤ M :=
    (hqL n (synthesisMap y)).trans ((hbound y).trans (mul_le_of_le_one_right hM.le hy))
  let scalar (n : ℕ) := a n * r.functional n (synthesisMap (b n))
  have normD (C : Finset Z) (n : ℕ) : ‖d C n‖ ≤ ‖a n‖*M := by
    change ‖a n * _‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (unif n _ (((W C).norm_starProjection_apply_le _).trans (hb _))) (norm_nonneg _)
  have hscalar (n : ℕ) : scalar n = r.coeff n * r.functional n (r.vector n).val := by
    simpa only [scalar,map_smul,smul_eq_mul] using congrArg (r.functional n) (hvec n)
  have limD (n : ℕ) : Tendsto (fun C ↦ d C n) atTop (𝓝 (scalar n)) :=
    (((r.functional n).continuous.comp synthesisMap.continuous).continuousAt.tendsto.comp (limit (b n))).const_mul _
  -- Tannery’s theorem exchanges the finite-cluster limit with the presentation series.
  have limTotal := tendsto_tsum_of_dominated_convergence (ha.mul_right M) limD
    (Eventually.of_forall normD)
  have hsum : Summable scalar := (ha.mul_right M).of_norm_bounded fun n ↦
    (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_left (unif n _ (hb n)) (norm_nonneg _))
  have val : (∑' n,scalar n) = t := tendsto_nhds_unique limTotal (hlen.congr fun C ↦ (loc C).tsum_eq.symm)
  exact val ▸ hsum.hasSum.congr_fun (fun n ↦ (hscalar n).symm)

open Classical in
/-- Every rapid presentation of the retained jet-endomorphism has the predicted divisor trace. -/
private theorem spectralNuclearity_trace_of_rapid_presentation (a : ℝ) (N : ℕ) (φ : 𝒟)
    (d : jets(χ,τ,hτ) → StrongDual ℂ (Q(a)))
    (hd : ∀ i f, d i ((D(a)).mkQ f) = iteratedDeriv i.2.val f.val (i.1.val-(a:ℂ))) :
    let I := {i : jets(χ,τ,hτ) // i.2.val < N}
    let K := ⨅ i : I, (d i.val).toLinearMap.ker
    let E := Q(a) ⧸ K
    letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    let Z := zeros(χ,τ,hτ)
    let term (z : Z) := ((min N (multiplicity(χ,τ,hτ,z)) : ℕ):ℂ) * nuclearityTestMellin χ φ (z.val-(a:ℂ))
    ∀ (A : B →L[ℂ] B) (Aq : Q(a) →L[ℂ] Q(a)) (T : E →L[ℂ] E),
      (∀ f s, (A f).val s = nuclearityTestMellin χ φ s * f.val s) →
      (∀ f, Aq ((D(a)).mkQ f) = (D(a)).mkQ (A f)) → (∀ x, T (K.mkQ x) = K.mkQ (Aq x)) →
      ∀ r : NuclearPresentation T, (∀ k : ℕ, ∃ C : ℝ, ∀ n, ‖r.coeff n‖*((n:ℝ)+1)^k ≤ C) →
        HasSum (fun n ↦ r.coeff n * r.functional n (r.vector n).val) (∑' z,term z) := by
  classical
  intro I K E Z term A Aq T hA hAq hT r hr
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let D := D(a)
  let : IsClosed (D : Set B) := schwartzBergmanDivisible_isClosed _
  have hB : IsNuclearTVS.{0} B := spectralJet_sb_nuclear
  let : T2Space B := hB.1
  let : PolynormableSpace ℂ B := hB.2.1
  let : T2Space (Q(a)) := inferInstanceAs (T2Space (B ⧸ D))
  have hQ : IsNuclearTVS.{0} (Q(a)) := isNuclearTVS_quotient hB D
  let : PolynormableSpace ℂ (Q(a)) := hQ.2.1
  let : IsClosed (K : Set (Q(a))) := by
    change IsClosed (↑(⨅ i : I, (d i.val).toLinearMap.ker) : Set (Q(a)))
    rw [Submodule.coe_iInf]
    exact isClosed_iInter (fun i ↦ (d i.val).isClosed_ker)
  let : T2Space E := inferInstanceAs (T2Space (Q(a) ⧸ K))
  let : PolynormableSpace ℂ E := (isNuclearTVS_quotient hQ K).2.1
  let L (i : I) : StrongDual ℂ E := ⟨K.liftQ (d i.val).toLinearMap (iInf_le _ i),
    (Submodule.isQuotientMap_mkQ K).continuous_iff.mpr (d i.val).continuous⟩
  have hL (i : I) (x : Q(a)) : L i (K.mkQ x) = d i.val x := rfl
  have separates (x : E) (hx : ∀ i, L i x=0) : x=0 := by
    obtain ⟨y,rfl⟩ := K.mkQ_surjective x
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,Submodule.mem_iInf]
    exact fun i ↦ hx i
  choose proj hmask hid hcomm hfin Rq _ using
    spectralNuclearity_trace_finite_cluster χ τ hτ a N φ d hd A Aq T hA hAq hT L hL
  choose R hR htrace using Rq
  refine spectralTrace_of_finiteProjections T r hr proj R hid hcomm hfin hR ?_ ?_ _ ?_
  · intro c e hce x hx
    change proj c x = 0
    apply separates
    intro i
    rw [hmask]
    by_cases hi : i.val.1 ∈ c
    · rw [ite_eq_left hi]
      have hm := hmask e i x
      change proj e x = 0 at hx
      simpa only [hx,map_zero,ite_eq_left (hce hi)] using hm.symm
    · rw [ite_eq_right hi]
  · intro x hx
    apply separates
    intro i
    have hm := hmask {i.val.1} i x
    simpa only [hx,map_zero,Finset.mem_singleton_self,ite_true] using hm.symm
  · have hs : Summable term := Summable.of_norm (spectralNuclearity_trace_term_summable χ τ hτ a N φ)
    have e : (fun C : Finset Z ↦ LinearMap.trace ℂ _ (R C)) = (fun C ↦ ∑ z ∈ C,term z) := funext htrace
    rw [e]
    exact hs.hasSum

end SpectralTraceHilbert

section SpectralBoundarySynthesis

open Filter Function Set Topology Bornology MeasureTheory Asymptotics Metric
open scoped NNReal ENNReal

/-- A separating family of observations has strongly dense span in the dual of
a space on which every continuous strong-bidual element is evaluation. -/
private theorem spectralBoundary_dense_observations {S I : Type*}
    [AddCommGroup S] [Module ℂ S] [TopologicalSpace S] [IsTopologicalAddGroup S]
    [ContinuousSMul ℂ S] [PolynormableSpace ℂ S] [T2Space S]
    (obs : I → StrongDual ℂ S) (separate : ∀ x : S, (∀ i, obs i x=0) → x=0)
    (bidual : ∀ φ : StrongDual ℂ (StrongDual ℂ S), ∃ x : S, ∀ L, φ L = L x) :
    Dense ((Submodule.span ℂ (range obs)) : Set (StrongDual ℂ S)) := by
  let : UniformSpace S := IsTopologicalAddGroup.rightUniformSpace S
  let : IsUniformAddGroup S := isUniformAddGroup_of_addCommGroup
  let X := StrongDual ℂ S
  let D := Submodule.span ℂ (range obs)
  let : PolynormableSpace ℂ X :=
    uniformConvergenceCLM_polynormable (F := ℂ)
      {T : Set S | IsVonNBounded ℂ T} (fun _ h ↦ h)
      (by rw [Bornology.sUnion_isVonNBounded_eq_univ,Submodule.span_univ];simp)
  let : Module ℝ X := Module.restrictScalars ℝ ℂ X
  let : IsScalarTower ℝ ℂ X := IsScalarTower.restrictScalars ℝ ℂ X
  let : LocallyConvexSpace ℝ X :=
    (PolynormableSpace.withSeminorms ℂ X).toLocallyConvexSpace
  intro L
  change L ∈ D.topologicalClosure
  by_contra hn
  obtain ⟨φ,hφ,hzero⟩ := exists_dual_eq_zero_on_submodule_of_notMem
    D.topologicalClosure D.isClosed_topologicalClosure hn
  obtain ⟨x,hx⟩ := bidual φ
  have h0 : x=0 := separate x fun i ↦ (hx _).symm.trans
    (hzero _ (D.le_topologicalClosure (Submodule.subset_span (mem_range_self i))))
  exact hφ (by rw [hx,h0,map_zero])

/-- Locally bounded Schwartz-valued kernels can be tested for weak holomorphy on a
separating family. Strong-dual approximation is uniform on the bounded family. -/
private theorem spectralBoundary_weak_holomorphic {S I : Type*}
    [AddCommGroup S] [Module ℂ S] [TopologicalSpace S] [IsTopologicalAddGroup S]
    [ContinuousSMul ℂ S] [PolynormableSpace ℂ S] [T2Space S]
    (obs : I → StrongDual ℂ S) (hd : Dense ((Submodule.span ℂ (range obs)) : Set (StrongDual ℂ S)))
    (region : Set ℂ) (hU : IsOpen region) (f : ℂ → S) (hb : IsVonNBounded ℂ (f '' region))
    (ho : ∀ i, DifferentiableOn ℂ (fun z ↦ obs i (f z)) region) (L : StrongDual ℂ S) :
    DifferentiableOn ℂ (fun z ↦ L (f z)) region := by
  let D := Submodule.span ℂ (range obs)
  let pairing : Submodule ℂ (StrongDual ℂ S) :=
    { carrier := {l | DifferentiableOn ℂ (fun z ↦ l (f z)) region}
      zero_mem' := differentiableOn_const (0:ℂ)
      add_mem' := fun {x y} hx hy ↦ hx.add hy
      smul_mem' := fun c x hx ↦ hx.const_mul c }
  have hs : D ≤ pairing := Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩;exact ho i)
  let F := 𝓝[(D : Set (StrongDual ℂ S))] L
  let : F.NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hd L)
  have hlim : Tendsto (id : StrongDual ℂ S → StrongDual ℂ S) F (𝓝 L) := nhdsWithin_le_nhds
  have hv := (UniformConvergenceCLM.tendsto_iff_tendstoUniformlyOn (RingHom.id ℂ) ℂ
    {s : Set S | IsVonNBounded ℂ s}).mp hlim (f '' region) hb
  have hv' : TendstoUniformlyOn (fun l z ↦ l (f z)) (fun z ↦ L (f z)) F region :=
    (hv.comp f).mono (fun x hx ↦ mem_image_of_mem _ hx)
  have hm : ∀ᶠ l in F, l ∈ D := self_mem_nhdsWithin
  have hP : ∀ᶠ l in F, DifferentiableOn ℂ (fun z ↦ l (f z)) region :=
    hm.mono fun l hl ↦ hs hl
  exact hv'.tendstoLocallyUniformlyOn.differentiableOn hP hU

/-- The evaluation functionals at individual real points are dense in the strong dual
of the complex real-line Schwartz space. -/
private theorem spectralBoundary_schwartz_eval_dense :
    let eval (t : ℝ) := (BoundedContinuousFunction.evalCLM ℂ t).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ)
    Dense ((Submodule.span ℂ (range eval)) : Set (StrongDual ℂ (SchwartzMap ℝ ℂ))) := by
  intro eval
  let S := SchwartzMap ℝ ℂ
  let : PolynormableSpace ℂ S := (schwartz_withSeminorms ℂ ℝ ℂ).toPolynormableSpace
  apply spectralBoundary_dense_observations eval (fun x h ↦ SchwartzMap.ext h)
  let D := EuclideanSpace ℝ (Fin 1)
  let E := SchwartzMap D ℂ
  let e : S ≃L[ℂ] E := schwartzChangeVariable ℂ (PiLp.equivOfUnique 2 ℝ _ : D ≃L[ℝ] ℝ)
  let lift : StrongDual ℂ E →L[ℂ] StrongDual ℂ S :=
    ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ e.toContinuousLinearMap
  obtain ⟨j,hj⟩ := euclideanSchwartz_reflexive 1
  intro Φ
  obtain ⟨u,hu⟩ := j.surjective (Φ.comp lift)
  refine ⟨e.symm u,fun L ↦ ?_⟩
  let l := L.comp e.symm.toContinuousLinearMap
  have eqL : lift l = L := by ext x; change L (e.symm (e x)) = L x; rw [e.symm_apply_apply]
  calc
    Φ L = (Φ.comp lift) l := by change Φ L = Φ (lift l); rw [eqL]
    _ = j u l := by rw [hu]
    _ = l u := hj u l
    _ = _ := rfl

/-- In a locally bounded family of real-line Schwartz functions, holomorphy of
every point value implies holomorphy after application of any tempered functional. -/
private theorem spectralBoundary_schwartz_dual_holomorphic (region : Set ℂ) (hU : IsOpen region)
    (f : ℂ → SchwartzMap ℝ ℂ) (hb : IsVonNBounded ℂ (f '' region))
    (hf : ∀ t : ℝ, DifferentiableOn ℂ (fun z ↦ f z t) region) (L : StrongDual ℂ (SchwartzMap ℝ ℂ)) :
    DifferentiableOn ℂ (fun z ↦ L (f z)) region := by
  let : PolynormableSpace ℂ (SchwartzMap ℝ ℂ) := (schwartz_withSeminorms ℂ ℝ ℂ).toPolynormableSpace
  exact spectralBoundary_weak_holomorphic _ spectralBoundary_schwartz_eval_dense region hU f hb hf L

/-- Every tempered functional applied to a pointwise holomorphic Schwartz-valued
kernel with bounded weighted strip families gives an entire Schwartz–Bergman function. -/
private theorem spectralBoundary_synthesis_schwartzBergman (K : ℂ → SchwartzMap ℝ ℂ)
    (hk : ∀ t : ℝ, Differentiable ℂ (fun z ↦ K z t))
    (hb : ∀ (A : ℝ) (p : ℕ), IsVonNBounded ℂ
      (range (fun z : {z : ℂ // |z.re| ≤ A} ↦ (((1+|z.val.im|)^p:ℝ):ℂ) • K z.val))) :
    ∃ R : StrongDual ℂ (SchwartzMap ℝ ℂ) →ₗ[ℂ] SchwartzBergman (univ : Set ℝ),
      ∀ L z, (R L).val z = L (K z) := by
  let S := SchwartzMap ℝ ℂ
  let sourceSpace := SchwartzBergman (univ : Set ℝ)
  have mem (L : StrongDual ℂ S) : (fun z ↦ L (K z)) ∈ schwartzBergmanSubmodule (univ : Set ℝ) := by
    have hdiff : Differentiable ℂ (fun z ↦ L (K z)) := by
      intro z
      let A := |z.re|+1
      let region := {v : ℂ | |v.re| < A}
      have Uop : IsOpen region := isOpen_lt Complex.continuous_re.abs continuous_const
      have hz : z ∈ region := by dsimp [region,A]; linarith
      have b0 : IsVonNBounded ℂ (K '' region) := (hb A 0).subset (by
        rintro _ ⟨w,hw,rfl⟩
        exact ⟨⟨w,le_of_lt hw⟩,by simp⟩)
      exact (spectralBoundary_schwartz_dual_holomorphic region Uop K b0
        (fun t ↦ (hk t).differentiableOn) L z hz).differentiableAt (Uop.mem_nhds hz)
    refine ⟨fun z h ↦ (h (mem_univ _)).elim,hdiff.differentiableOn,?_⟩
    intro a b _ _ n
    let A := |a|+|b|
    have hA : 0 ≤ A := by dsimp [A]; positivity
    obtain ⟨C,hC⟩ := ((NormedSpace.isVonNBounded_iff ℂ).mp ((hb A n).image L)).exists_norm_le
    refine ⟨(1+A)^n*C,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    have hr : |z.re| ≤ A := abs_le.mpr ⟨by dsimp [A]; linarith [hz.1,neg_abs_le a,abs_nonneg b],
      by dsimp [A]; linarith [hz.2,le_abs_self b,abs_nonneg a]⟩
    have hzn := hC _ (mem_image_of_mem L (mem_range_self (⟨z,hr⟩ : {z : ℂ // |z.re| ≤ A})))
    change ‖L ((((1+|z.im|)^n:ℝ):ℂ) • K z)‖ ≤ C at hzn
    rw [map_smul, norm_smul, Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ (1+|z.im|)^n by positivity)] at hzn
    have hn : ‖z‖ ≤ (1+A)*(1+|z.im|) := (Complex.norm_le_abs_re_add_abs_im z).trans (by nlinarith [mul_nonneg hA (abs_nonneg z.im)])
    change ‖z^n * L (K z)‖ ≤ _
    rw [norm_mul,norm_pow]
    calc
      _ ≤ ((1+A)*(1+|z.im|))^n * ‖L (K z)‖ := by gcongr
      _ = (1+A)^n * ((1+|z.im|)^n*‖L (K z)‖) := by rw [mul_pow,mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left hzn (by positivity)
  exact ⟨{toFun := fun L ↦ ⟨fun z ↦ L (K z),mem L⟩
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl},fun _ _ ↦ rfl⟩

open scoped NNReal ENNReal

private theorem spectralBoundary_rapidBound_eq (a : (Fin 1 → ℤ) → ℂ) (j : ℕ) :
    rapidDecaySequenceBound j a =
      ∑' n, ENNReal.ofReal (latticeWeight n ^ j * ‖a (latticeIndex n)‖) := by
  unfold rapidDecaySequenceBound
  rw [← latticeIndex.tsum_eq]
  apply tsum_congr
  intro n
  have hw : 0 ≤ latticeWeight n := zero_le_one.trans (latticeWeight_bounds n).1
  rw [ENNReal.ofReal_mul (pow_nonneg hw _), ENNReal.ofReal_pow hw, ofReal_norm]
  congr 2
  rw [latticeWeight, ENNReal.ofReal_add zero_le_one (abs_nonneg _), ENNReal.ofReal_one]
  congr 1
  change ‖(WithLp.toLp 2 (fun i ↦ ((latticeIndex n i : ℤ) : ℝ)) : EuclideanSpace ℝ (Fin 1))‖ₑ = _
  rw [← ofReal_norm, EuclideanSpace.norm_eq]
  simp [latticeIndex, Real.norm_eq_abs, Real.sqrt_sq_eq_abs]

private theorem spectralBoundary_rapidSeminorm_eq (a : RapidDecaySequence 1) (j : ℕ) :
    rapidDecaySequenceSeminorm j a = ∑' n, latticeWeight n ^ j * ‖a (latticeIndex n)‖ := by
  change (rapidDecaySequenceBound j a.val).toReal = _
  rw [spectralBoundary_rapidBound_eq, ENNReal.tsum_toReal_eq (fun _ ↦ ENNReal.ofReal_ne_top)]
  apply tsum_congr
  intro n
  exact ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg (zero_le_one.trans (latticeWeight_bounds n).1) _)
    (norm_nonneg _))
/-- Continuous weighted analysis on a closed Hilbert boundary. The family is linear both
in the rapid sequence and in its ℓ² argument, with a single seminorm bound in each weight. -/
private theorem spectralBoundary_weighted_pair (k : ℕ) :
    let H := lp (fun _ : ℕ ↦ ℂ) 2
    let S := RapidDecaySequence 1
    ∃ L : H →ₗ[ℂ] StrongDual ℂ S,
      (∀ s : S, Continuous (fun h : H ↦ L h s)) ∧
      (∀ h s, L h s = ∑' n : ℕ, h n * ((latticeWeight n ^ k:ℝ):ℂ) * s (latticeIndex n)) ∧
      (∀ (n : ℕ) (s : S), L (lp.single (E := fun _ : ℕ ↦ ℂ) 2 n (1:ℂ)) s =
        ((latticeWeight n ^ k:ℝ):ℂ) * s (latticeIndex n)) := by
  intro H S
  let W (n : ℕ) : ℝ := latticeWeight n ^ k
  have hW (n : ℕ) : 0 ≤ W n := pow_nonneg (zero_le_one.trans (latticeWeight_bounds n).1) _
  let t (x : H) (s : S) (n : ℕ) := x n * (W n:ℂ) * s (latticeIndex n)
  have major (x : H) (s : S) (n : ℕ) : ‖t x s n‖ ≤ ‖x‖ * (W n * ‖s (latticeIndex n)‖) := by
    simp only [t,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hW n),mul_assoc]
    exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm (by norm_num) x n)
      (mul_nonneg (hW n) (norm_nonneg _))
  have hsum (s : S) : HasSum (fun n ↦ W n * ‖s (latticeIndex n)‖) (rapidDecaySequenceSeminorm k s) := by
    rw [spectralBoundary_rapidSeminorm_eq]
    exact ((rapidSequence_mem_iff s.val).mp s.property k).hasSum
  have hs (x : H) (s : S) : Summable (t x s) := ((hsum s).summable.mul_left ‖x‖).of_norm_bounded (major x s)
  have bound (x : H) (s : S) : ‖∑' n, t x s n‖ ≤ ‖x‖ * rapidDecaySequenceSeminorm k s := by
    refine (norm_tsum_le_tsum_norm (hs x s).norm).trans ?_
    rw [← ((hsum s).mul_left ‖x‖).tsum_eq]
    exact (hs x s).norm.tsum_le_tsum (major x s) ((hsum s).summable.mul_left ‖x‖)
  let ls (x : H) : S →ₗ[ℂ] ℂ :=
    { toFun := fun s ↦ ∑' n, t x s n
      map_add' := fun a b ↦ by
        rw [← (hs x a).tsum_add (hs x b)]
        exact tsum_congr fun n ↦ mul_add _ _ _
      map_smul' := fun c a ↦ by
        change (∑' n, t x (c • a) n) = c • (∑' n, t x a n)
        rw [← (hs x a).tsum_const_smul c]
        apply tsum_congr; intro n
        change x n * (W n:ℂ) * (c*a (latticeIndex n)) = c * (x n * (W n:ℂ) * a (latticeIndex n))
        ring }
  let L (x : H) : StrongDual ℂ S := ⟨ls x,by
    apply WithSeminorms.continuous_normedSpace_rng _ rapidDecaySequence_withSeminorms
    refine ⟨{k}, ⟨‖x‖,norm_nonneg _⟩,fun s ↦ ?_⟩
    change ‖(ls x) s‖ ≤ _
    exact (bound x s).trans (mul_le_mul_of_nonneg_left ((Finset.le_sup (f := rapidDecaySequenceSeminorm (r := 1)) (Finset.mem_singleton_self k)) s) (norm_nonneg x))⟩
  let l : H →ₗ[ℂ] StrongDual ℂ S :=
    { toFun := L
      map_add' := fun a b ↦ by
        ext s; change (∑' n, t (a+b) s n) = (∑' n, t a s n) + ∑' n, t b s n
        rw [← (hs a s).tsum_add (hs b s)]
        apply tsum_congr; intro n
        change (a n+b n)*(W n:ℂ)*s (latticeIndex n) = _
        simp [t, add_mul]
      map_smul' := fun c a ↦ by
        ext s
        change (∑' n, t (c • a) s n) = c • (∑' n, t a s n)
        rw [← (hs a s).tsum_const_smul c]
        apply tsum_congr; intro n
        change c * a n * (W n:ℂ) * s (latticeIndex n) = c*(a n*(W n:ℂ)*s (latticeIndex n))
        ring }
  refine ⟨l,fun s ↦ ?_,fun _ _ ↦ rfl,fun n s ↦ ?_⟩
  · let q : H →ₗ[ℂ] ℂ := (ContinuousLinearMap.applyₗ (E := S) ℂ (RingHom.id ℂ) s).toLinearMap.comp l
    exact (q.mkContinuous (rapidDecaySequenceSeminorm k s) (fun x ↦ (bound x s).trans_eq (mul_comm _ _))).continuous
  · change (∑' j, t (lp.single 2 n 1) s j) = _
    rw [tsum_eq_single n]
    · simp [t,lp.single_apply,W]
    · intro m hm
      simp [t,lp.single_apply,hm]

private theorem spectralBoundary_continuous_of_closedGraph {E Y : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    [ContinuousSMul ℂ Y]
    (hE : IsFrechetTVS E) (hY : IsFrechetTVS Y)
    (T : E →ₗ[ℂ] Y) (hT : IsClosed (T.graph : Set (E × Y))) : Continuous T := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace E := hE.2.2.2
  have : CompleteSpace Y := hY.2.2.2
  have : TopologicalSpace.MetrizableSpace E := hE.2.2.1
  have : TopologicalSpace.MetrizableSpace Y := hY.2.2.1
  let Γ := T.graph
  have : CompleteSpace Γ := completeSpace_coe_iff_isComplete.mpr hT.isComplete
  have : IsUniformAddGroup Γ := Γ.toAddSubgroup.isUniformAddGroup
  have : TopologicalSpace.MetrizableSpace (E × Y) := inferInstance
  have : TopologicalSpace.MetrizableSpace Γ :=
    inferInstanceAs (TopologicalSpace.MetrizableSpace (Γ : Set (E × Y)))
  have : FirstCountableTopology Γ := inferInstance
  have : FirstCountableTopology E := inferInstance
  have : (uniformity E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : BaireSpace E := BaireSpace.of_completelyPseudoMetrizable
  let Pr : Γ →L[ℂ] E := (ContinuousLinearMap.fst ℂ E Y).comp Γ.subtypeL
  have hmem (x : E) : (x, T x) ∈ Γ := (LinearMap.mem_graph_iff _ _).mpr rfl
  have hval (p : Γ) : p.val.2 = T p.val.1 := (LinearMap.mem_graph_iff _ _).mp p.property
  have hinj : Injective Pr := fun p q h ↦ by
    have h1 : p.val.1 = q.val.1 := h
    exact Subtype.ext (Prod.ext h1 (by rw [hval, hval, h1]))
  have hsurj : Surjective Pr := fun x ↦ ⟨⟨(x, T x), hmem x⟩, rfl⟩
  have ho : IsOpenMap Pr := by
    apply isOpenMap_of_not_isMeagre_range Pr
    rw [hsurj.range_eq]
    exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty
  let h : Γ ≃ₜ E :=
    (Equiv.ofBijective Pr ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen Pr.continuous ho
  refine (continuous_snd.comp (continuous_subtype_val.comp h.symm.continuous)).congr fun x ↦ ?_
  have h1 : (h.symm x).val.1 = x := h.apply_symm_apply x
  change (h.symm x).val.2 = T x
  rw [hval, h1]

/-- Applying the weighted rapid coordinates of the boundary kernels to arbitrary ℓ²
coefficients gives a continuous synthesis into the full Schwartz–Bergman space.
The pointwise continuity on the Hilbert side closes its graph. -/
private theorem spectralBoundary_hilbert_synthesis (K : ℂ → SchwartzMap ℝ ℂ)
    (hk : ∀ t : ℝ, Differentiable ℂ (fun z ↦ K z t))
    (hb : ∀ (A : ℝ) (p : ℕ), IsVonNBounded ℂ
      (range (fun z : {z : ℂ // |z.re| ≤ A} ↦ (((1+|z.val.im|)^p:ℝ):ℂ) • K z.val)))
    (e : SchwartzMap ℝ ℂ ≃L[ℂ] RapidDecaySequence 1) (k : ℕ) :
    let H := lp (fun _ : ℕ ↦ ℂ) 2
    let sourceSpace := SchwartzBergman (univ : Set ℝ)
    ∃ R : H →L[ℂ] sourceSpace,
      (∀ h z, (R h).val z = ∑' n : ℕ, h n * ((latticeWeight n ^ k:ℝ):ℂ) * e (K z) (latticeIndex n)) ∧
      ∀ (n : ℕ) z, (R (lp.single (E := fun _ : ℕ ↦ ℂ) 2 n (1:ℂ))).val z =
        ((latticeWeight n ^ k:ℝ):ℂ) * e (K z) (latticeIndex n) := by
  intro H sourceSpace
  obtain ⟨T,hT⟩ := spectralBoundary_synthesis_schwartzBergman K hk hb
  obtain ⟨L,hLc,hLs,hLn⟩ := spectralBoundary_weighted_pair k
  let pairing : StrongDual ℂ (RapidDecaySequence 1) →L[ℂ] StrongDual ℂ (SchwartzMap ℝ ℂ) :=
    ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ e.toContinuousLinearMap
  let R := (T.comp pairing.toLinearMap).comp L
  have val (x : H) (z : ℂ) : (R x).val z = L x (e (K z)) := hT _ z
  let ev (z : ℂ) := (entireJet z 0).comp schwartzBergmanEntireInclusion
  have he (z : ℂ) (f : sourceSpace) : ev z f = f.val z := by
    change entireJet z 0 (schwartzBergmanEntireInclusion f) = _
    rw [entireJet_apply,iteratedDeriv_zero,schwartzBergmanEntireInclusion_apply]
  have hg : (R.graph : Set (H × sourceSpace)) = ⋂ z : ℂ, {x : H × sourceSpace | L x.1 (e (K z)) = ev z x.2} := by
    ext x
    simp only [mem_iInter,mem_ofPred_eq,SetLike.mem_coe,LinearMap.mem_graph_iff]
    constructor
    · intro h z
      rw [he,h,val]
    · intro h
      apply Subtype.ext
      funext z
      exact ((h z).trans (he z _)).symm.trans (val _ _).symm
  have gc : IsClosed (R.graph : Set (H × sourceSpace)) := hg ▸ isClosed_iInter
    (fun z ↦ isClosed_eq ((hLc _).comp continuous_fst) ((ev z).continuous.comp continuous_snd))
  have hR : Continuous R := spectralBoundary_continuous_of_closedGraph (isFrechetTVS_of_banach H)
    (schwartzBergman_frechet univ isOpen_univ inferInstance univ_nonempty) R gc
  exact ⟨⟨R,hR⟩,fun h z ↦ (val h z).trans (hLs _ _),fun n z ↦ (val _ z).trans (hLn _ _)⟩

/-- A countable family of rapidly decreasing nonnegative rows admits a single positive
rapid majorant up to one constant per row. -/
private theorem spectralBoundary_rapidScale (p : ℕ → ℕ → ℝ)
    (hp : ∀ j k : ℕ, ∃ C : ℝ, ∀ n : ℕ, p j n * ((n:ℝ)+1)^k ≤ C) :
    ∃ c : ℕ → ℝ, (∀ n, 0 < c n) ∧
      (∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, c n * ((n:ℝ)+1)^k ≤ C) ∧
      (∀ j : ℕ, ∃ C : ℝ, ∀ n : ℕ, p j n ≤ C*c n) := by
  classical
  let W (n : ℕ) : ℝ := n+1
  have hW (n) : 1 ≤ W n := by dsimp [W]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have pos (n) : 0 < W n := zero_lt_one.trans_le (hW n)
  have eventual (j k : ℕ) : ∀ᶠ n in atTop, p j n * (W n)^k ≤ 1 := by
    obtain ⟨C,hC⟩ := hp j (k+1)
    obtain ⟨N,hN⟩ := exists_nat_ge C
    filter_upwards [eventually_ge_atTop N] with n hn
    have h1 : C ≤ W n := hN.trans (by dsimp [W]; exact_mod_cast (show N ≤ n + 1 by omega))
    have h2 := hC n
    change p j n * (W n)^(k+1) ≤ C at h2
    rw [pow_succ,←mul_assoc] at h2
    exact (le_of_mul_le_mul_right (by simpa only [one_mul] using h2.trans h1 : (p j n * W n ^ k) * W n ≤ 1 * W n) (pos n))
  let S (n : ℕ) := (Finset.range (n+1)).filter (fun k ↦ ∀ j ≤ k, p j n * (W n)^k ≤ 1)
  let H (n : ℕ) := (insert 0 (S n)).max' (Finset.insert_nonempty _ _)
  have good (k : ℕ) : ∀ᶠ n in atTop, k ∈ S n := by
    have hall : ∀ᶠ n in atTop, ∀ j ∈ Finset.range (k+1), p j n * (W n)^k ≤ 1 :=
      (Finset.eventually_all _).mpr fun j _ ↦ eventual j k
    filter_upwards [eventually_ge_atTop k,hall] with n hn hn'
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),fun j hj ↦ hn' j (Finset.mem_range.mpr (by omega))⟩
  have large (k : ℕ) : ∀ᶠ n in atTop, k ≤ H n := (good k).mono fun n hn ↦
    Finset.le_max' _ _ (Finset.mem_insert_of_mem hn)
  have Hgood : ∀ᶠ n in atTop, H n ∈ S n := by
    filter_upwards [large 1] with n hn
    have hh : H n ∈ insert 0 (S n) := Finset.max'_mem _ _
    exact (Finset.mem_insert.mp hh).resolve_left (by omega)
  let c (n : ℕ) := ((W n)^(H n))⁻¹
  have cp (n) : 0 < c n := inv_pos.mpr (pow_pos (pos n) _)
  have global {f : ℕ → ℝ} (hf : ∀ᶠ n in atTop, f n ≤ 1) : ∃ C : ℝ, ∀ n, f n ≤ C := by
    rw [←Nat.cofinite_eq_atTop] at hf
    obtain ⟨C,hC⟩ := (isBoundedUnder_of_eventually_le hf).bddAbove_range_of_cofinite
    exact ⟨C,fun n ↦ hC (mem_range_self n)⟩
  refine ⟨c,cp,fun k ↦ global ?_,fun j ↦ ?_⟩
  · filter_upwards [large k] with n hn
    change ((W n)^(H n))⁻¹ * (W n)^k ≤ 1
    rw [inv_mul_eq_div, div_le_one (pow_pos (pos n) _)]
    exact pow_le_pow_right₀ (hW n) hn
  · obtain ⟨C,hC⟩ := global (f := fun n ↦ p j n * (W n)^(H n)) (by
      filter_upwards [Hgood,large j] with n hn hnj
      exact (Finset.mem_filter.mp hn).2 j hnj)
    refine ⟨C,fun n ↦ ?_⟩
    change p j n ≤ C * ((W n)^(H n))⁻¹
    rw [← div_eq_mul_inv,le_div_iff₀ (pow_pos (pos n) _)]
    exact hC n

private theorem spectralBoundary_gauge_image {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (φ : M ≃ₗ[ℂ] N) (s : Set M) (x : M) :
    gauge (φ '' s) (φ x) = gauge s x := by
  unfold gauge
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right fun _ ↦ ?_
  simp only [Set.mem_smul_set, Set.exists_mem_image]
  refine exists_congr fun y ↦ and_congr_right fun _ ↦ ?_
  rw [show r • φ y = φ (r • y) from (LinearMap.map_smul_of_tower φ.toLinearMap r y).symm]
  exact φ.injective.eq_iff

/-- The image of a Banach disc under an injective continuous linear map is a Banach disc:
the map restricts to a linear equivalence of the spans that preserves the gauges. -/
private theorem spectralBoundary_disc_image {Y Z : Type*}
    [AddCommGroup Y] [Module ℂ Y] [UniformSpace Y] [IsUniformAddGroup Y]
    [PolynormableSpace ℂ Y] [T2Space Y]
    [AddCommGroup Z] [Module ℂ Z] [UniformSpace Z] [IsUniformAddGroup Z]
    [PolynormableSpace ℂ Z] [T2Space Z]
    {sourceSpace : Set Y} (hB : IsBanachDisc sourceSpace) (T : Y →L[ℂ] Z) (hT : Injective T) :
    IsBanachDisc (T '' sourceSpace) := by
  let S := Submodule.span ℂ sourceSpace
  let S' := Submodule.span ℂ (T '' sourceSpace)
  have hSS : S.map T.toLinearMap = S' := (Submodule.span_image T.toLinearMap).symm
  let φ : S ≃ₗ[ℂ] S' :=
    (Submodule.equivMapOfInjective T.toLinearMap hT S).trans (LinearEquiv.ofEq _ _ hSS)
  have himage : ((↑) ⁻¹' (T '' sourceSpace) : Set S') = φ '' ((↑) ⁻¹' sourceSpace : Set S) := by
    ext z
    constructor
    · rintro ⟨b, hb, hbz⟩
      exact ⟨⟨b, Submodule.subset_span hb⟩, hb, Subtype.ext hbz⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
  have bB : Balanced ℂ ((↑) ⁻¹' (T '' sourceSpace) : Set S') :=
    himage ▸ hB.balanced.image φ.toLinearMap
  have cB : Convex ℝ ((↑) ⁻¹' (T '' sourceSpace) : Set S') :=
    himage ▸ hB.convex.linear_image (φ.toLinearMap.restrictScalars ℝ)
  have aB : Absorbent ℝ ((↑) ⁻¹' (T '' sourceSpace) : Set S') :=
    himage ▸ Absorbent.image_of_surjective (f := φ.toLinearMap.restrictScalars ℝ)
      φ.surjective hB.absorbent
  let p := gaugeSeminorm hB.balanced hB.convex hB.absorbent
  let p' := gaugeSeminorm bB cB aB
  have hnorm (z : S') : p' z = p (φ.symm z) := by
    change gauge _ z = gauge _ (φ.symm z)
    rw [himage, ← spectralBoundary_gauge_image φ, φ.apply_symm_apply]
  let ψ : WithLocalSeminorm p' → WithLocalSeminorm p := fun z ↦ (φ.symm (show S' from z) : S)
  have hψ : Isometry ψ := Isometry.of_dist_eq fun x y ↦ by
    rw [dist_eq_norm, dist_eq_norm]
    change p (φ.symm (show S' from x) - φ.symm (show S' from y)) =
      p' ((show S' from x) - (show S' from y))
    rw [← map_sub]
    exact (hnorm _).symm
  have hinj : Injective ψ := fun a b h ↦ φ.symm.injective h
  have hsurj : Surjective ψ := fun z ↦ ⟨(φ (show S from z) : S'), φ.symm_apply_apply _⟩
  have := hB.separated
  exact ⟨hB.bounded.image T, bB, cB, aB,
    T2Space.of_injective_continuous hinj hψ.continuous,
    (hψ.isUniformInducing.completeSpace_congr hsurj).mpr hB.complete⟩

/-- Every bounded sequence in a complete Hausdorff locally convex space lies in one Banach disc. The ℓ¹ synthesis construction is from the Chapter 7 biorthogonal certificate; factoring out its kernel removes the biorthogonality assumption. -/
private theorem spectralBoundary_bounded_common_disc {I E : Type*} [DecidableEq I]
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [PolynormableSpace ℂ E] [T2Space E] [CompleteSpace E]
    (v : I → E) (bnd : IsVonNBounded ℂ (range v))
    :
    ∃ D : Set E, IsBanachDisc D ∧ ∀ i, v i ∈ D := by
  classical
  let X := lp (fun _ : I ↦ ℂ) 1
  let hp := PolynormableSpace.withSeminorms ℂ E
  have bounded_q (q : {q : Seminorm ℂ E // Continuous q}) :
      ∃ C > (0:ℝ), ∀ i, q.val (v i) ≤ C := by
    obtain ⟨C,hC,h⟩ := hp.isVonNBounded_iff_seminorm_bounded.mp bnd q
    exact ⟨C,hC,fun i ↦ (h _ (mem_range_self i)).le⟩
  have normsum (x : X) : HasSum (fun i ↦ ‖x i‖) ‖x‖ := by
    simpa using (lp.hasSum_norm (p := (1:ℝ≥0∞)) (by simp) x)
  have hterms (x : X) : Summable (fun i ↦ x i • v i) := by
    apply summable_iff_cauchySeq_finset.mpr
    apply cauchySeq_finset_iff_sum_vanishing.mpr
    intro region hU
    obtain ⟨p,hp0,hpU⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ E).mem_iff.mp hU
    obtain ⟨C,hC,hh⟩ := bounded_q ⟨p,hp0⟩
    have hmajor := (normsum x).summable.mul_left C
    obtain ⟨s,hs⟩ := cauchySeq_finset_iff_sum_vanishing.mp
      (summable_iff_cauchySeq_finset.mp hmajor) (Iio 1) (Iio_mem_nhds zero_lt_one)
    refine ⟨s,fun u hu ↦ hpU (p.mem_ball_zero.mpr (lt_of_le_of_lt ?_ (hs u hu)))⟩
    calc
      p (∑ i ∈ u, x i • v i) ≤ ∑ i ∈ u, p (x i • v i) :=
        Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _
      _ ≤ _ := Finset.sum_le_sum fun i _ ↦ by
        rw [map_smul_eq_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hh i) (norm_nonneg _)
  let A : X →ₗ[ℂ] E :=
    { toFun := fun x ↦ ∑' i, x i • v i
      map_add' := fun x y ↦ by
        simpa [add_smul] using (hterms x).tsum_add (hterms y)
      map_smul' := fun c x ↦ by
        change (∑' i, (c * x i) • v i) = c • _
        simpa [smul_smul] using (hterms x).tsum_const_smul c }
  have cont : Continuous A := by
    apply hp.continuous_of_continuous_comp A
    intro q
    obtain ⟨C,hC,h⟩ := bounded_q q
    apply Seminorm.continuous' (r := C+1)
    refine mem_of_superset (Metric.ball_mem_nhds (0:X) one_pos) fun x hx ↦ ?_
    rw [Metric.mem_ball,dist_zero_right] at hx
    have hlimit := q.property.continuousAt.tendsto.comp (hterms x).hasSum
    have hmajor := ((normsum x).mul_left C)
    have hbound : q.val (A x) ≤ C * ‖x‖ :=
      le_of_tendsto_of_tendsto' hlimit hmajor (fun s ↦ by
        change q.val (∑ i ∈ s, x i • v i) ≤ ∑ i ∈ s, C * ‖x i‖
        refine (Finset.le_sum_of_subadditive q.val (map_zero q.val).le (map_add_le_add q.val) _ _).trans ?_
        apply Finset.sum_le_sum
        intro i _
        rw [map_smul_eq_mul,mul_comm]
        exact mul_le_mul_of_nonneg_right (h i) (norm_nonneg _))
    apply (q.val.comp A).mem_closedBall_zero.mpr
    change q.val (A x) ≤ C+1
    nlinarith
  let S : X →L[ℂ] E := ⟨A,cont⟩
  let K := S.ker
  let : IsClosed (K : Set X) := S.isClosed_ker
  let L₀ := K.liftQ S.toLinearMap (le_refl K)
  let L : (X ⧸ K) →L[ℂ] E := ⟨L₀, (Submodule.isQuotientMap_mkQ K).continuous_iff.mpr S.continuous⟩
  have inj : Injective L := LinearMap.ker_eq_bot.mp (K.ker_liftQ_eq_bot S.toLinearMap le_rfl le_rfl)
  refine ⟨L '' Metric.closedBall (0:X ⧸ K) 1, spectralBoundary_disc_image isBanachDisc_closedUnitBall L inj,?_⟩
  intro i
  let e : X := lp.single (E := fun _ : I ↦ ℂ) 1 i (1:ℂ)
  refine ⟨K.mkQ e,?_,?_⟩
  · rw [Metric.mem_closedBall,dist_zero_right]
    apply (Submodule.Quotient.norm_mk_le K e).trans
    dsimp only [e]
    rw [lp.norm_single (by norm_num), norm_one]
  · change (∑' j : I, lp.single (E := fun _ : I ↦ ℂ) 1 i (1:ℂ) j • v j) = v i
    simpa [lp.single_apply] using
      (tsum_eq_single i (f := fun j : I ↦ lp.single (E := fun _ : I ↦ ℂ) 1 i (1:ℂ) j • v j)
        (fun j hj ↦ by simp [lp.single_apply,hj]))

/-- A Hilbert-space boundary extension descends through a quotient by first choosing the
representative perpendicular to the kernel of the synthesis. -/
private theorem spectralBoundary_lift {sourceSpace H E : Type*}
    [AddCommGroup sourceSpace] [Module ℂ sourceSpace] [TopologicalSpace sourceSpace]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [T2Space E]
    (q : sourceSpace →L[ℂ] E) (hq : Topology.IsQuotientMap q)
    (boundary : sourceSpace →L[ℂ] H) (synthesis : H →L[ℂ] E) (T : E →L[ℂ] E)
    (hT : ∀ x, synthesis (boundary x) = T (q x)) :
    ∃ lift : E →L[ℂ] H, synthesis.comp lift = T := by
  let K := synthesis.ker
  let : CompleteSpace K := synthesis.isClosed_ker.completeSpace_coe
  let region := (ContinuousLinearMap.id ℂ H - K.starProjection).comp boundary
  have correction (x : sourceSpace) : synthesis (region x) = T (q x) := by
    change synthesis (boundary x - K.starProjection (boundary x)) = _
    rw [map_sub, show synthesis (K.starProjection (boundary x)) = 0 from K.starProjection_apply_mem _, sub_zero, hT]
  have hker (x : sourceSpace) (hx : q x = 0) : region x = 0 := by
    change boundary x - K.starProjection (boundary x) = 0
    rw [K.starProjection_eq_self_iff.mpr (show boundary x ∈ K by
      change synthesis (boundary x) = 0
      rw [hT,hx,map_zero]), sub_self]
  obtain ⟨s,hs⟩ := q.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hq.surjective)
  have right (y : E) : q (s y) = y := DFunLike.congr_fun hs y
  let L := region.toLinearMap.comp s
  have heq (x : sourceSpace) : L (q x) = region x := by
    have h := hker (s (q x) - x) (by rw [map_sub,right,sub_self])
    simpa only [L,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,map_sub,sub_eq_zero] using h
  have hcont : Continuous L := hq.continuous_iff.mpr (by simpa only [Function.comp_def,heq] using region.continuous)
  refine ⟨⟨L,hcont⟩,ContinuousLinearMap.ext fun y ↦ ?_⟩
  obtain ⟨x,rfl⟩ := hq.surjective y
  change synthesis (L (q x)) = _
  rw [heq,correction]

/-- A single rapid presentation of boundary synthesis gives a single rapid presentation
on the quotient with exactly the same coefficients, vectors, and Banach disc. -/
private theorem spectralBoundary_strong_of_synthesis {sourceSpace H E : Type*}
    [AddCommGroup sourceSpace] [Module ℂ sourceSpace] [TopologicalSpace sourceSpace]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [T2Space E]
    (q : sourceSpace →L[ℂ] E) (hq : Topology.IsQuotientMap q)
    (boundary : sourceSpace →L[ℂ] H) (synthesis : H →L[ℂ] E) (T : E →L[ℂ] E)
    (hT : ∀ x, synthesis (boundary x) = T (q x))
    (r : NuclearPresentation synthesis)
    (rapid : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, ‖r.coeff n‖ * ((n:ℝ)+1)^k ≤ C) :
    IsStronglyNuclearOperator T := by
  obtain ⟨L,rfl⟩ := spectralBoundary_lift q hq boundary synthesis T hT
  let r' : NuclearPresentation (synthesis.comp L) :=
    { coeff := r.coeff, functional := fun n ↦ (r.functional n).comp L
      disc := r.disc, isBanachDisc := r.isBanachDisc, vector := r.vector,
      vector_mem := r.vector_mem, summable_coeff := r.summable_coeff,
      equicontinuous := fun region hU ↦ by
        have h := (L.continuous.tendsto' 0 0 (map_zero L)).eventually (r.equicontinuous region hU)
        simpa only [ContinuousLinearMap.comp_apply, map_zero] using h
      hasSum := fun x ↦ r.hasSum (L x) }
  exact ⟨r',rapid⟩

/-- A smoothing synthesis operator from a separable complex Hilbert space into a
complete countably seminormed space has a single rapid nuclear presentation if its
orthonormal columns decrease rapidly in every generating seminorm. -/
private theorem spectralBoundary_presentation_of_rapid_columns {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [PolynormableSpace ℂ E] [T2Space E] [CompleteSpace E]
    (p : ℕ → Seminorm ℂ E) (hp : WithSeminorms p)
    (b : HilbertBasis ℕ ℂ H) (R : H →L[ℂ] E)
    (h : ∀ j k : ℕ, ∃ C : ℝ, ∀ n : ℕ, p j (R (b n)) * ((n:ℝ)+1)^k ≤ C) :
    ∃ r : NuclearPresentation R, ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
      ‖r.coeff n‖ * ((n:ℝ)+1)^k ≤ C := by
  obtain ⟨c,hc,hr,hd⟩ := spectralBoundary_rapidScale (fun j n ↦ p j (R (b n))) h
  let v (n : ℕ) := ((c n : ℂ)⁻¹) • R (b n)
  have bv : IsVonNBounded ℂ (range v) := by
    apply hp.isVonNBounded_iff_seminorm_bddAbove.mpr
    intro j
    obtain ⟨C,hC⟩ := hd j
    refine ⟨C,?_⟩
    rintro _ ⟨_,⟨n,rfl⟩,rfl⟩
    change p j ((c n : ℂ)⁻¹ • R (b n)) ≤ C
    rw [map_smul_eq_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hc n),inv_mul_eq_div]
    exact (div_le_iff₀ (hc n)).mpr (hC n)
  obtain ⟨D,hD,hv⟩ := spectralBoundary_bounded_common_disc v bv
  let L (n : ℕ) : H →L[ℂ] ℂ := innerSL ℂ (b n)
  have hL : EquicontinuousAt (fun n x ↦ L n x) 0 := by
    apply Metric.equicontinuousAt_of_continuity_modulus (fun x : H ↦ ‖x‖)
      (by simpa using (continuous_norm : Continuous (norm : H → ℝ)).tendsto 0)
    refine Eventually.of_forall fun x n ↦ ?_
    rw [map_zero,dist_zero_left]
    exact (norm_inner_le_norm _ _).trans_eq (by simp [b.orthonormal.norm_eq_one n])
  have hs : Summable c := by
    obtain ⟨C,hC⟩ := hr 2
    have hsum : Summable (fun n : ℕ ↦ 1 / ((n:ℝ)+1)^2) := by
      simpa only [Real.rpow_two,sq_abs] using (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
    refine (hsum.mul_left C).of_norm_bounded fun n ↦ ?_
    rw [Real.norm_eq_abs,abs_of_pos (hc n),mul_one_div]
    exact (le_div_iff₀ (by positivity)).2 (hC n)
  let r : NuclearPresentation R :=
    { coeff := fun n ↦ (c n:ℂ), functional := L, disc := D, isBanachDisc := hD
      vector := fun n ↦ ⟨v n,Submodule.subset_span (hv n)⟩
      vector_mem := hv
      summable_coeff := by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hc _)] using hs
      equicontinuous := hL
      hasSum := fun x ↦ ((b.hasSum_repr x).mapL R).congr_fun fun n ↦ by
        change ((c n:ℂ) * L n x) • v n = (R ((b.repr x n) • b n))
        rw [map_smul,HilbertBasis.repr_apply_apply,show L n x = inner ℂ (b n) x from rfl]
        dsimp only [v]
        rw [smul_smul]
        congr 1
        field_simp [Complex.ofReal_ne_zero.mpr (hc n).ne'] }
  refine ⟨r,fun k ↦ ?_⟩
  obtain ⟨C,hC⟩ := hr k
  exact ⟨C,fun n ↦ by simpa only [r,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hc n)] using hC n⟩

/-- Every polynomially reweighted fixed-line synthesis has a single rapid
presentation after projection to any complete countably-seminormed space. -/
private theorem spectralBoundary_contour_presentation {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [PolynormableSpace ℂ E] [T2Space E] [CompleteSpace E]
    (p : ℕ → Seminorm ℂ E) (hp : WithSeminorms p)
    (K : ℂ → SchwartzMap ℝ ℂ)
    (hk : ∀ t : ℝ, Differentiable ℂ (fun z ↦ K z t))
    (hb : ∀ (A : ℝ) (s : ℕ), IsVonNBounded ℂ
      (range (fun z : {z : ℂ // |z.re| ≤ A} ↦ (((1+|z.val.im|)^s:ℝ):ℂ) • K z.val)))
    (e : SchwartzMap ℝ ℂ ≃L[ℂ] RapidDecaySequence 1) (k : ℕ)
    (q : SchwartzBergman (univ : Set ℝ) →L[ℂ] E) :
    let H := lp (fun _ : ℕ ↦ ℂ) 2
    let sourceSpace := SchwartzBergman (univ : Set ℝ)
    ∃ R : H →L[ℂ] sourceSpace,
      (∀ h z, (R h).val z = ∑' n : ℕ, h n * ((latticeWeight n ^ k:ℝ):ℂ) * e (K z) (latticeIndex n)) ∧
      ∃ r : NuclearPresentation (q.comp R), ∀ j : ℕ, ∃ C : ℝ, ∀ n : ℕ, ‖r.coeff n‖*((n:ℝ)+1)^j ≤ C := by
  intro H sourceSpace
  choose R hR hunit using spectralBoundary_hilbert_synthesis K hk hb e
  refine ⟨R k,hR k,?_⟩
  let basis : HilbertBasis ℕ ℂ H := ⟨LinearIsometryEquiv.refl ℂ H⟩
  let u (n : ℕ) : H := lp.single 2 n 1
  have bval (n : ℕ) : basis n = u n := by rw [← basis.repr_symm_single]; rfl
  have un (n : ℕ) : u n ∈ Metric.closedBall (0:H) 1 := by
    rw [Metric.mem_closedBall,dist_zero_right,← bval, basis.orthonormal.norm_eq_one n]
  apply spectralBoundary_presentation_of_rapid_columns p hp basis (q.comp (R k))
  intro i j
  let T := q.comp (R (k+j))
  have hbd : IsVonNBounded ℂ (T '' Metric.closedBall (0:H) 1) :=
    (NormedSpace.isVonNBounded_closedBall ℂ H 1).image T
  obtain ⟨C,hC⟩ := hp.isVonNBounded_iff_seminorm_bddAbove.mp hbd i
  refine ⟨(2:ℝ)^j*C,fun n ↦ ?_⟩
  have hw : 0 ≤ latticeWeight n := zero_le_one.trans (latticeWeight_bounds n).1
  have hsc : R (k+j) (u n) = ((latticeWeight n ^ j : ℝ):ℂ) • R k (u n) := by
    apply Subtype.ext
    funext z
    change (R (k+j) (u n)).val z = ((latticeWeight n ^ j:ℝ):ℂ) * (R k (u n)).val z
    dsimp only [u]
    rw [hunit,hunit,pow_add,Complex.ofReal_mul]
    ring
  have bound := hC (mem_image_of_mem _ (mem_image_of_mem T (un n)))
  change p i (q ((R (k+j)) (u n))) ≤ C at bound
  rw [hsc,map_smul,map_smul_eq_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hw j)] at bound
  rw [bval]
  change p i (q (R k (u n))) * ((n:ℝ)+1)^j ≤ _
  calc
    _ ≤ p i (q (R k (u n))) * (2*latticeWeight n)^j := by
      gcongr; exact (latticeWeight_bounds n).2.2
    _ = 2^j * ((latticeWeight n)^j * p i (q (R k (u n)))) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left bound (by positivity)

open MeasureTheory Complex

/-- Gaussian regularization of the Cauchy kernel with its moving pole removed. -/
private def spectralBoundaryKernel (G : ℂ → ℂ) (w z : ℂ) : ℂ :=
  Complex.exp ((z-w)^2) * dslope G w z / G w

private theorem spectralBoundaryKernel_entire {G : ℂ → ℂ} (hG : Differentiable ℂ G) (w : ℂ) :
    Differentiable ℂ (spectralBoundaryKernel G w) := by
  apply Differentiable.div_const
  apply Differentiable.mul
  · fun_prop
  · exact fun z ↦ ((hG.analyticAt z).dslope w).differentiableAt

private theorem spectralBoundaryKernel_offPole {G : ℂ → ℂ} {w z : ℂ} (hz : z ≠ w) (hw : G w ≠ 0) :
    spectralBoundaryKernel G w z =
      Complex.exp ((z-w)^2) / (w-z) * (1 - G z / G w) := by
  simp only [spectralBoundaryKernel, dslope_of_ne _ hz,slope,smul_eq_mul,vsub_eq_sub]
  field_simp [sub_ne_zero.mpr hz,sub_ne_zero.mpr hz.symm,hw]
  ring

private theorem spectralBoundary_dslope_norm {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (A C : ℝ) (n : ℕ) (hC : 0 ≤ C)
    (hder : ∀ x : ℂ, |x.re| ≤ A → ‖deriv G x‖ ≤ C * (1+|x.im|)^n)
    (w z : ℂ) (hw : |w.re| ≤ A) (hz : |z.re| ≤ A) :
    ‖dslope G w z‖ ≤ C * (1+|w.im|+|z.im-w.im|)^n := by
  let b := |w.im| + |z.im-w.im|
  have hb : |z.im| ≤ b := by
    calc
      |z.im| = |(z.im-w.im)+w.im| := by congr 1; ring
      _ ≤ |z.im-w.im| + |w.im| := abs_add_le _ _
      _ = b := add_comm _ _
  have hw' : |w.im| ≤ b := le_add_of_nonneg_right (abs_nonneg _)
  let S := {x : ℂ | x.re ∈ Icc (-A) A ∧ x.im ∈ Icc (-b) b}
  have cv : Convex ℝ S := ((convex_halfSpace_re_ge (-A)).inter (convex_halfSpace_re_le A)).inter
    ((convex_halfSpace_im_ge (-b)).inter (convex_halfSpace_im_le b))
  have hbd (x : ℂ) (hx : x ∈ S) : ‖deriv G x‖ ≤ C * (1+b)^n := by
    refine (hder x (abs_le.mpr hx.1)).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (add_le_add_right (abs_le.mpr hx.2) 1) n) hC
  have zm : z ∈ S := ⟨abs_le.mp hz,abs_le.mp hb⟩
  have wm : w ∈ S := ⟨abs_le.mp hw,abs_le.mp hw'⟩
  have goal : ‖dslope G w z‖ ≤ C * (1+b)^n := by
    by_cases e : z = w
    · subst z; simpa only [dslope_same] using hbd w wm
    · rw [dslope_of_ne _ e,slope,smul_eq_mul,norm_mul,norm_inv,inv_mul_eq_div]
      apply (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr e))).mpr
      exact cv.norm_image_sub_le_of_norm_deriv_le (fun x _ ↦ hG x) hbd wm zm
  simpa only [b,add_assoc] using goal

private theorem spectralBoundary_gaussian_abs_pow (m : ℕ) (u : ℝ) :
    (1 + |u|)^m * Real.exp (-(u^2)) ≤ Real.exp ((m:ℝ)^2) := by
  have h := Real.add_one_le_exp |u|
  have hp : (1+|u|)^m ≤ Real.exp ((m:ℝ)*|u|) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  calc
    _ ≤ Real.exp ((m:ℝ)*|u|) * Real.exp (-(u^2)) := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = Real.exp ((m:ℝ)*|u| - u^2) := by rw [←Real.exp_add]; rfl
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ((m:ℝ) - |u|),sq_abs u,sq_nonneg u])

/-- The entire interpolation vector on a vertical contour grows at most polynomially
in the contour height, for each fixed output Schwartz–Bergman seminorm. The same bound
applies uniformly on any narrow complex tube where the reciprocal bound holds. -/
private theorem spectralBoundaryKernel_strip {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (A C D : ℝ) (n b p : ℕ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hder : ∀ x : ℂ, |x.re| ≤ A → ‖deriv G x‖ ≤ C * (1+|x.im|)^n) :
    ∃ K : ℝ, ∀ w z : ℂ, |w.re| ≤ A → |z.re| ≤ A →
      ‖(G w)⁻¹‖ ≤ D*(1+|w.im|)^b →
      (1+|z.im|)^p * ‖spectralBoundaryKernel G w z‖ ≤ K * (1+|w.im|)^(p+n+b) := by
  let m := p+n
  refine ⟨Real.exp ((2*A)^2) * C * D * Real.exp ((m:ℝ)^2), ?_⟩
  intro w z hw hz hi
  let u := z.im-w.im
  let region := 1+|u|
  let targetSet := 1+|w.im|
  have hU : 0 ≤ region := by dsimp [region]; positivity
  have hV : 0 ≤ targetSet := by dsimp [targetSet]; positivity
  have ht : 1+|w.im|+|u| ≤ targetSet*region := by
    dsimp [targetSet,region]; nlinarith [mul_nonneg (abs_nonneg w.im) (abs_nonneg u)]
  have hy : 1+|z.im| ≤ targetSet*region := by
    have h := abs_add_le u w.im
    rw [show u + w.im = z.im by dsimp [u];ring] at h
    linarith
  have hr : |z.re-w.re| ≤ 2*A := (abs_sub _ _).trans (by linarith)
  have hs : (z.re-w.re)^2 ≤ (2*A)^2 := by
    nlinarith [sq_abs (z.re-w.re),abs_nonneg (z.re-w.re),mul_nonneg (sub_nonneg.mpr hr) (add_nonneg (hr.trans' (abs_nonneg _)) (abs_nonneg (z.re-w.re)))]
  have hg : ‖Complex.exp ((z-w)^2)‖ ≤ Real.exp ((2*A)^2) * Real.exp (-(u^2)) := by
    rw [Complex.norm_exp,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [pow_two,Complex.mul_re,Complex.sub_re,Complex.sub_im,u]
    nlinarith
  have hdiff : ‖dslope G w z‖ ≤ C*(targetSet*region)^n := by
    refine (spectralBoundary_dslope_norm hG A C n hC hder w z hw hz).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ht _) hC
  change _ ≤ _ * targetSet^(p+n+b)
  rw [spectralBoundaryKernel,div_eq_mul_inv,norm_mul,norm_mul]
  calc
    _ ≤ (targetSet*region)^p * (Real.exp ((2*A)^2) * Real.exp (-(u^2)) * (C*(targetSet*region)^n) * (D*targetSet^b)) := by
      gcongr
    _ = (Real.exp ((2*A)^2)*C*D*targetSet^(p+n+b)) * (region^m * Real.exp (-(u^2))) := by
      simp only [m,pow_add,mul_pow]; ring
    _ ≤ (Real.exp ((2*A)^2)*C*D*targetSet^(p+n+b)) * Real.exp ((m:ℝ)^2) := by
      apply mul_le_mul_of_nonneg_left (spectralBoundary_gaussian_abs_pow m u)
      positivity
    _ = _ := by ring

/-- The moving, regularized Cauchy vector is holomorphic in its integration parameter
where the generator is nonzero, including at the removable diagonal. -/
private theorem spectralBoundaryKernel_moving {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (z w : ℂ) (hw : G w ≠ 0) :
    DifferentiableAt ℂ (fun t ↦ spectralBoundaryKernel G t z) w := by
  have hswap (t : ℂ) : dslope G t z = dslope G z t := by
    by_cases ht : t=z
    · rw [ht]
    · rw [dslope_of_ne _ (Ne.symm ht),dslope_of_ne _ ht,slope_comm]
  unfold spectralBoundaryKernel
  simp_rw [hswap]
  have he : DifferentiableAt ℂ (fun t : ℂ ↦ Complex.exp ((z-t)^2)) w := by fun_prop
  exact (he.mul ((hG.analyticAt w).dslope z).differentiableAt).div (hG w) hw

/-- The kernel multiplied by a test Mellin transform is uniformly Schwartz in the
boundary parameter, including all its derivatives, in each output strip seminorm. -/
private theorem spectralBoundaryKernel_schwartz {G M : ℂ → ℂ}
    (hG : Differentiable ℂ G) (hM : Differentiable ℂ M) (A C D σ : ℝ) (n b : ℕ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hσ : |σ|+1 ≤ A)
    (hder : ∀ x : ℂ, |x.re| ≤ A → ‖deriv G x‖ ≤ C*(1+|x.im|)^n)
    (hinv : ∀ w : ℂ, |w.re-σ| ≤ 1 → G w ≠ 0 ∧ ‖(G w)⁻¹‖ ≤ D*(1+|w.im|)^b)
    (hrapid : ∀ k : ℕ, ∃ E > (0:ℝ), ∀ w : ℂ, |w.re-σ| ≤ 1 → (1+|w.im|)^k*‖M w‖ ≤ E)
    (p k j : ℕ) : ∃ sourceSpace : ℝ, ∀ w z : ℂ, w.re = σ → |z.re| ≤ A →
      (1+|z.im|)^p * (1+|w.im|)^k *
        ‖iteratedDeriv j (fun v ↦ M v * spectralBoundaryKernel G v z) w‖ ≤ sourceSpace := by
  obtain ⟨K,hK⟩ := spectralBoundaryKernel_strip hG A C D n b p hC hD hder
  let K' := max 0 K
  have Kp : 0 ≤ K' := le_max_left _ _
  let m := p+n+b
  obtain ⟨E,hE,hEM⟩ := hrapid (m+k)
  refine ⟨j.factorial * (2^k * K' * E),?_⟩
  intro w z hw hz
  let Z := (1+|z.im|)^p
  let W := (1+|w.im|)^k
  let H : ℂ := ((Z*W:ℝ):ℂ)
  have hh : ‖H‖ = Z*W := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
    positivity
  have tube (v : ℂ) (hv : v ∈ Metric.closedBall w 1) :
      |v.re - σ| ≤ 1 ∧ |v.re| ≤ A ∧ 1+|w.im| ≤ 2*(1+|v.im|) := by
    have hdist := mem_closedBall_iff_norm.mp hv
    have hre := (Complex.abs_re_le_norm (v-w)).trans hdist
    have him := (Complex.abs_im_le_norm (v-w)).trans hdist
    rw [Complex.sub_re,hw] at hre
    rw [Complex.sub_im] at him
    refine ⟨hre,?_,?_⟩
    · have t := abs_add_le (v.re-σ) σ
      rw [sub_add_cancel] at t
      linarith
    · have t := abs_sub v.im (v.im-w.im)
      rw [sub_sub_cancel] at t
      linarith [abs_nonneg v.im]
  let F (v : ℂ) := M v * spectralBoundaryKernel G v z
  have ha (v : ℂ) (hv : v ∈ Metric.closedBall w 1) : DifferentiableAt ℂ F v :=
    (hM v).mul (spectralBoundaryKernel_moving hG z v (hinv v (tube v hv).1).1)
  have hd : DiffContOnCl ℂ (fun v ↦ H * F v) (Metric.ball w 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball w one_ne_zero]
    exact fun v hv ↦ ((ha v hv).const_mul H).differentiableWithinAt
  have hbound (v : ℂ) (hv : v ∈ Metric.sphere w 1) : ‖H * F v‖ ≤ 2^k*K'*E := by
    obtain ⟨hhv,hva,hvi⟩ := tube v (Metric.sphere_subset_closedBall hv)
    let h := 1+|v.im|
    have hp : 0 ≤ h := by dsimp [h]; positivity
    have hKer : Z * ‖spectralBoundaryKernel G v z‖ ≤ K' * h^m :=
      (hK v z hva hz (hinv v hhv).2).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hp m))
    have hW : W ≤ 2^k * h^k := by simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hvi k
    rw [norm_mul,hh]
    change Z*W*(‖M v * spectralBoundaryKernel G v z‖) ≤ _
    rw [norm_mul]
    calc
      _ = W * (Z * ‖spectralBoundaryKernel G v z‖) * ‖M v‖ := by ring
      _ ≤ (2^k * h^k) * (K'*h^m) * ‖M v‖ := by gcongr
      _ = (2^k*K') * (h^(m+k)*‖M v‖) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hEM v hhv) (by positivity)
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j one_pos hd hbound
  rw [iteratedDeriv_const_mul_field,norm_mul,hh,one_pow,div_one] at h
  exact h

local notation "linePoint" => (fun (x y : ℝ) ↦ (x : ℂ) + y * Complex.I)
private theorem spectralContour_hasDerivAt_vertical_iterate {I : Set ℝ} (hI : IsOpen I) (a : I)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Complex.re ⁻¹' I)) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Complex.I ^ n * iteratedDeriv n f (linePoint a y))
      (Complex.I ^ (n+1) * iteratedDeriv (n+1) f (linePoint a x)) x := by
  have hU := hI.preimage Complex.continuous_re
  have han : ∀ m, AnalyticOnNhd ℂ (iteratedDeriv m f) (Complex.re ⁻¹' I) := by
    intro m
    induction m with
    | zero => simpa using hf.analyticOnNhd hU
    | succ m ih => rw [iteratedDeriv_succ]; exact fun z hz ↦ (ih z hz).deriv
  have hd := (han n _ (show linePoint a x ∈ Complex.re ⁻¹' I by simp)).differentiableAt.hasDerivAt
  have hline : HasDerivAt (fun w : ℂ ↦ (a.val : ℂ) + w * Complex.I) Complex.I (x : ℂ) := by
    simpa using (((hasDerivAt_id (x : ℂ)).mul_const Complex.I).const_add (a.val : ℂ))
  have h := ((hd.comp (x : ℂ) hline).comp_ofReal).const_mul (Complex.I ^ n)
  simpa only [Function.comp_apply, iteratedDeriv_succ, pow_succ, mul_left_comm,
    mul_assoc, mul_comm (deriv _ _)] using h

private theorem spectralContour_iteratedDeriv_vertical {I : Set ℝ} (hI : IsOpen I) (a : I)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Complex.re ⁻¹' I)) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ ↦ f (linePoint a y)) =
      fun y ↦ Complex.I ^ n * iteratedDeriv n f (linePoint a y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (spectralContour_hasDerivAt_vertical_iterate hI a hf n x).deriv

/-- A family holomorphic on a neighborhood of a whole vertical line with uniform
Schwartz bounds for all holomorphic derivatives on that line is a bounded family
of real Schwartz functions after restriction. -/
private theorem spectralBoundary_schwartz_line_family {X : Type*} (F : X → ℂ → ℂ) (σ : ℝ)
    (hol : ∀ i, DifferentiableOn ℂ (F i) (Complex.re ⁻¹' Ioo (σ-1) (σ+1)))
    (bounds : ∀ k j : ℕ, ∃ C : ℝ, ∀ i (t : ℝ),
      (1+|t|)^k * ‖iteratedDeriv j (F i) (linePoint σ t)‖ ≤ C) :
    ∃ f : X → SchwartzMap ℝ ℂ, (∀ i t, f i t = F i (linePoint σ t)) ∧
      Bornology.IsVonNBounded ℂ (range f) := by
  let s : Ioo (σ-1) (σ+1) := ⟨σ,by constructor <;> linarith⟩
  have hdec (k j : ℕ) : ∃ C : ℝ, ∀ i (t : ℝ),
      ‖t‖^k * ‖iteratedFDeriv ℝ j (fun t : ℝ ↦ F i (linePoint σ t)) t‖ ≤ C := by
    obtain ⟨C,hC⟩ := bounds k j
    refine ⟨C,fun i t ↦ ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, show σ = s.val from rfl,
      spectralContour_iteratedDeriv_vertical isOpen_Ioo s (hol i),norm_mul,norm_pow,Complex.norm_I,one_pow,one_mul]
    apply le_trans _ (hC i t)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (by rw [Real.norm_eq_abs]; linarith) _) (norm_nonneg _)
  let f (i : X) : SchwartzMap ℝ ℂ :=
    { toFun := fun t ↦ F i (linePoint σ t)
      smooth' := by
        apply contDiff_of_differentiable_iteratedDeriv
        intro j _ t
        rw [show σ = s.val from rfl,spectralContour_iteratedDeriv_vertical isOpen_Ioo s (hol i)]
        exact (spectralContour_hasDerivAt_vertical_iterate isOpen_Ioo s (hol i) j t).differentiableAt
      decay' := fun k j ↦ ⟨(hdec k j).choose,(hdec k j).choose_spec i⟩ }
  refine ⟨f,fun i t ↦ rfl,?_⟩
  apply (schwartz_withSeminorms ℂ ℝ ℂ).isVonNBounded_iff_seminorm_bddAbove.mpr
  rintro ⟨k,j⟩
  obtain ⟨C,hC⟩ := hdec k j
  refine ⟨max 0 C,?_⟩
  rintro _ ⟨_,⟨i,rfl⟩,rfl⟩
  exact SchwartzMap.seminorm_le_bound ℂ k j (f i) (le_max_left _ _)
    (fun x ↦ (hC i x).trans (le_max_right _ _))

/-- The weighted boundary kernels form a bounded family in the scalar Schwartz space.
The bound covers all their boundary derivatives simultaneously on the same contour. -/
private theorem spectralBoundary_schwartz_vectors {G M : ℂ → ℂ}
    (hG : Differentiable ℂ G) (hM : Differentiable ℂ M) (A C D σ : ℝ) (n b : ℕ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hσ : |σ|+1 ≤ A)
    (hder : ∀ x : ℂ, |x.re| ≤ A → ‖deriv G x‖ ≤ C*(1+|x.im|)^n)
    (hinv : ∀ w : ℂ, |w.re-σ| ≤ 1 → G w ≠ 0 ∧ ‖(G w)⁻¹‖ ≤ D*(1+|w.im|)^b)
    (hrapid : ∀ k : ℕ, ∃ E > (0:ℝ), ∀ w : ℂ, |w.re-σ| ≤ 1 → (1+|w.im|)^k*‖M w‖ ≤ E)
    (p : ℕ) :
    ∃ f : {z : ℂ // |z.re| ≤ A} → SchwartzMap ℝ ℂ,
      (∀ z t, f z t = (((1+|z.val.im|)^p:ℝ):ℂ) * (M (linePoint σ t) * spectralBoundaryKernel G (linePoint σ t) z.val)) ∧
      Bornology.IsVonNBounded ℂ (range f) := by
  apply spectralBoundary_schwartz_line_family
    (fun z : {z : ℂ // |z.re| ≤ A} ↦ fun w ↦ (((1+|z.val.im|)^p:ℝ):ℂ) * (M w * spectralBoundaryKernel G w z.val)) σ
  · intro z w hw
    have h : |w.re-σ| ≤ 1 := abs_le.mpr ⟨by linarith [hw.1],by linarith [hw.2]⟩
    exact (((hM w).mul (spectralBoundaryKernel_moving hG z.val w (hinv w h).1)).const_mul _).differentiableWithinAt
  · intro k j
    obtain ⟨sourceSpace,hB⟩ := spectralBoundaryKernel_schwartz hG hM A C D σ n b hC hD hσ hder hinv hrapid p k j
    refine ⟨sourceSpace,fun z t ↦ ?_⟩
    have h := hB (linePoint σ t) z.val (by simp) z.property
    simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add] at h
    rw [iteratedDeriv_const_mul_field,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ (1+|z.val.im|)^p by positivity)]
    simpa only [mul_assoc,mul_left_comm] using h

/-- The entire comparison generator gives a globally defined Schwartz-valued
kernel. Every polynomially weighted output strip is bounded in the real Schwartz space. -/
private theorem spectralBoundary_global_kernel {G M : ℂ → ℂ}
    (hG : Differentiable ℂ G) (hM : Differentiable ℂ M) (σ : ℝ)
    (hd : ∀ A : ℝ, ∃ n : ℕ, ∃ C > (0:ℝ), ∀ x : ℂ, |x.re| ≤ A →
      ‖deriv G x‖ ≤ C*(1+|x.im|)^n)
    (hinv : ∃ b : ℕ, ∃ D > (0:ℝ), ∀ w : ℂ, |w.re-σ| ≤ 1 → G w ≠ 0 ∧ ‖(G w)⁻¹‖ ≤ D*(1+|w.im|)^b)
    (hm : ∀ k : ℕ, ∃ E > (0:ℝ), ∀ w : ℂ, |w.re-σ| ≤ 1 → (1+|w.im|)^k*‖M w‖ ≤ E) :
    ∃ K : ℂ → SchwartzMap ℝ ℂ,
      (∀ z t, K z t = M (linePoint σ t) * spectralBoundaryKernel G (linePoint σ t) z) ∧
      (∀ t : ℝ, Differentiable ℂ (fun z ↦ K z t)) ∧
      ∀ (A : ℝ) (p : ℕ), Bornology.IsVonNBounded ℂ
        (range (fun z : {z : ℂ // |z.re| ≤ A} ↦ (((1+|z.val.im|)^p:ℝ):ℂ) • K z.val)) := by
  obtain ⟨b,D,hD,hI⟩ := hinv
  have localFamily (A : ℝ) (p : ℕ) :
      ∃ f : {z : ℂ // |z.re| ≤ A} → SchwartzMap ℝ ℂ,
        (∀ z t, f z t = (((1+|z.val.im|)^p:ℝ):ℂ) * (M (linePoint σ t) * spectralBoundaryKernel G (linePoint σ t) z.val)) ∧
        Bornology.IsVonNBounded ℂ (range f) := by
    let A' := max (|σ|+1) A
    obtain ⟨n,C,hC,h⟩ := hd A'
    obtain ⟨f,hf,hb⟩ := spectralBoundary_schwartz_vectors hG hM A' C D σ n b hC.le hD.le (le_max_left _ _) h hI hm p
    let inc (z : {z : ℂ // |z.re| ≤ A}) : {z : ℂ // |z.re| ≤ A'} := ⟨z.val,z.property.trans (le_max_right _ _)⟩
    exact ⟨f ∘ inc,fun z t ↦ hf (inc z) t,hb.subset (range_comp_subset_range _ _)⟩
  choose f hf hb using localFamily
  let K (z : ℂ) : SchwartzMap ℝ ℂ := f |z.re| 0 ⟨z,le_rfl⟩
  have hk (z : ℂ) (t : ℝ) : K z t = M (linePoint σ t) * spectralBoundaryKernel G (linePoint σ t) z := by
    simpa only [K,pow_zero,Complex.ofReal_one,one_mul] using hf |z.re| 0 ⟨z,le_rfl⟩ t
  refine ⟨K,hk,fun t ↦ ?_,fun A p ↦ ?_⟩
  · simp_rw [hk]
    exact (spectralBoundaryKernel_entire hG _).const_mul _
  · apply (hb A p).subset
    rintro _ ⟨z,rfl⟩
    refine ⟨z, SchwartzMap.ext fun t ↦ ?_⟩
    change f A p z t = (((1+|z.val.im|)^p:ℝ):ℂ) * K z.val t
    rw [hf,hk]

set_option backward.isDefEq.respectTransparency false

private def spectralBoundary_delta (n : ℕ) : RapidDecaySequence 1 :=
  ⟨fun a ↦ if a = latticeIndex n then 1 else 0, by
    apply (rapidSequence_mem_iff _).2
    intro k
    apply summable_of_ne_finset_zero (s := {n})
    intro m hm
    have hmn : m ≠ n := by simpa using hm
    rw [ite_eq_right (latticeIndex.injective.ne hmn),norm_zero,mul_zero]⟩

private theorem spectralBoundary_delta_eval (n m : ℕ) :
    spectralBoundary_delta n (latticeIndex m) = if m = n then 1 else 0 := by
  change (if latticeIndex m = latticeIndex n then _ else _) = _
  simp only [latticeIndex.injective.eq_iff]

private theorem spectralBoundary_delta_seminorm (n k : ℕ) :
    rapidDecaySequenceSeminorm k (spectralBoundary_delta n) = latticeWeight n ^ k := by
  rw [spectralBoundary_rapidSeminorm_eq,tsum_eq_single n]
  · simp only [spectralBoundary_delta_eval,ite_true,norm_one,mul_one]
  · intro j hj
    simp only [spectralBoundary_delta_eval,ite_eq_right hj,norm_zero,mul_zero]

private theorem spectralBoundary_delta_hasSum (s : RapidDecaySequence 1) :
    HasSum (fun n ↦ s (latticeIndex n) • spectralBoundary_delta n) s := by
  let S := RapidDecaySequence 1
  let hp := rapidDecaySequence_withSeminorms (r := 1)
  obtain ⟨_, _, _, hcomplete⟩ := (rapidDecaySequence_isFrechet (r := 1))
  let t (n : ℕ) := s (latticeIndex n) • spectralBoundary_delta n
  have hsum : Summable t := by
    apply summable_iff_cauchySeq_finset.mpr
    rw [CauchySeq, cauchy_map_iff', uniformity_eq_comap_nhds_zero, Filter.tendsto_comap_iff,
      hp.tendsto_nhds]
    intro j ε hε
    let p : Seminorm ℂ S := rapidDecaySequenceSeminorm (r := 1) j
    let L : S →ₗ[ℂ] LocalBanach p := UniformSpace.Completion.toComplL.toLinearMap.comp LinearMap.id
    have hL (x : S) : ‖L x‖ = p x := localBanach_norm_coe p x
    have h : Summable (fun n ↦ L (t n)) := by
      apply Summable.of_norm
      apply ((rapidSequence_mem_iff s.val).mp s.property j).congr
      intro n
      rw [hL]
      change _ = rapidDecaySequenceSeminorm j (s (latticeIndex n) • spectralBoundary_delta n)
      rw [map_smul_eq_mul,spectralBoundary_delta_seminorm,mul_comm]
    have hc := cauchy_map_iff'.mp (summable_iff_cauchySeq_finset.mp h)
    rw [tendsto_uniformity_iff_dist_tendsto_zero, Metric.tendsto_nhds] at hc
    filter_upwards [hc ε hε] with z hz
    rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg, dist_eq_norm', ← map_sum, ← map_sum,
      ← map_sub,hL] at hz
    simpa only [sub_zero,Function.comp_apply,p] using hz
  change HasSum t s
  suffices h : (∑' n,t n) = s by exact h ▸ hsum.hasSum
  apply Subtype.ext
  funext a
  obtain ⟨n,rfl⟩ := latticeIndex.surjective a
  let co : S →L[ℂ] ℂ :=
    { toFun := fun x ↦ x (latticeIndex n), map_add' _ _ := rfl, map_smul' _ _ := rfl,
      cont := rapidCoordinate_continuous n }
  change co (∑' j,t j) = s (latticeIndex n)
  rw [← (hsum.hasSum.mapL co).tsum_eq,tsum_eq_single n]
  · change s (latticeIndex n) * spectralBoundary_delta n (latticeIndex n) = _
    simp only [spectralBoundary_delta_eval,ite_true,mul_one]
  · intro m hm
    change s (latticeIndex m) * spectralBoundary_delta m (latticeIndex n) = _
    simp only [spectralBoundary_delta_eval,ite_eq_right (Ne.symm hm),mul_zero]

private theorem spectralBoundary_delta_growth {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (J : RapidDecaySequence 1 →L[ℂ] X) :
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ n, ‖J (spectralBoundary_delta n)‖ ≤ C*latticeWeight n ^m := by
  let q := (normSeminorm ℂ X).comp J.toLinearMap
  obtain ⟨S,K,_,hK⟩ := Seminorm.bound_of_continuous rapidDecaySequence_withSeminorms q
    (show Continuous (fun x ↦ ‖J x‖) from J.continuous.norm)
  refine ⟨S.sup id,K,K.coe_nonneg,fun n ↦ (hK _).trans ?_⟩
  change (K:ℝ)*(S.sup rapidDecaySequenceSeminorm) (spectralBoundary_delta n) ≤ _
  gcongr
  apply Seminorm.finset_sup_apply_le (pow_nonneg (zero_le_one.trans (latticeWeight_bounds n).1) _)
  intro j hj
  rw [spectralBoundary_delta_seminorm]
  exact pow_le_pow_right₀ (latticeWeight_bounds n).1 (Finset.le_sup (f := id) hj)

private theorem spectralBoundary_weight_inv_sq : Summable (fun n ↦ (latticeWeight n ^ 2)⁻¹) := by
  have h := (Real.summable_nat_pow_inv.mpr (by decide : 1 < 2)).comp_injective Nat.succ_injective
  apply (h.mul_left 4).of_nonneg_of_le (fun n ↦ by positivity)
  intro n
  change (latticeWeight n ^ 2)⁻¹ ≤ 4 * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹
  have hn := (latticeWeight_bounds n).2.2
  have hw := (latticeWeight_bounds n).1
  rw [Nat.cast_succ, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (sq_pos_of_pos (by linarith))
    (sq_pos_of_pos (by positivity))]
  nlinarith [sq_nonneg (latticeWeight n), mul_self_le_mul_self (by positivity : 0 ≤ (n : ℝ) + 1) hn]

/-- Polynomial damping of the analysis coordinates realizes an entire Banach family
of tempered functionals in one Hilbert boundary space. -/
private theorem spectralBoundary_incoming {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (J : RapidDecaySequence 1 →L[ℂ] X) (pairing : Y →L[ℂ] X →L[ℂ] ℂ) :
    ∃ (k : ℕ) (T : Y →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2),
      ∀ y s, (∑' n : ℕ, T y n * ((latticeWeight n ^ k:ℝ):ℂ) * s (latticeIndex n)) = pairing y (J s) := by
  let H := lp (fun _ : ℕ ↦ ℂ) 2
  obtain ⟨m,C,hC,hJ⟩ := spectralBoundary_delta_growth J
  let k := m+2
  let u (n : ℕ) : H := lp.single 2 n 1
  let L (n : ℕ) := pairing.flip (J (spectralBoundary_delta n))
  let targetSet (n : ℕ) : Y →L[ℂ] H := (((latticeWeight n ^k : ℝ):ℂ)⁻¹) • (L n).smulRight (u n)
  have hw (n : ℕ) : 0 < latticeWeight n := zero_lt_one.trans_le (latticeWeight_bounds n).1
  have hu (n : ℕ) : ‖u n‖ = 1 := by simp [u,lp.norm_single (by norm_num : 0 < (2 : ℝ≥0∞))]
  have hs : Summable targetSet := by
    apply (spectralBoundary_weight_inv_sq.mul_left (‖pairing.flip‖*C)).of_norm_bounded
    intro n
    rw [show ‖targetSet n‖ = _ from norm_smul ..,ContinuousLinearMap.norm_smulRight_apply,hu,mul_one,
      norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (pow_pos (hw n) _)]
    calc
      _ ≤ (latticeWeight n^k)⁻¹ * (‖pairing.flip‖ * (C*latticeWeight n^m)) :=
        mul_le_mul_of_nonneg_left ((pairing.flip.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (hJ n) (norm_nonneg _))) (inv_nonneg.mpr (pow_nonneg (hw n).le _))
      _ = _ := by dsimp only [k]; rw [pow_add]; field_simp [(hw n).ne']
  let T := ∑' n, targetSet n
  have coord (n : ℕ) (y : Y) : T y n = ((latticeWeight n ^k:ℝ):ℂ)⁻¹ * L n y := by
    let eval := (lp.evalCLM ℂ (fun _ : ℕ ↦ ℂ) 2 n).comp (ContinuousLinearMap.apply ℂ H y)
    change eval (∑' j, targetSet j) = _
    rw [← (hs.hasSum.mapL eval).tsum_eq,tsum_eq_single n]
    · change ((latticeWeight n^k:ℝ):ℂ)⁻¹ * ((L n y) * (lp.single (E := fun _ : ℕ ↦ ℂ) 2 n (1:ℂ)) n) = _
      simp
    · intro j hj
      change ((latticeWeight j^k:ℝ):ℂ)⁻¹ * ((L j y) * (lp.single (E := fun _ : ℕ ↦ ℂ) 2 j (1:ℂ)) n) = _
      simp [lp.single_apply,hj.symm]
  refine ⟨k,T,fun y s ↦ ?_⟩
  have rep := ((spectralBoundary_delta_hasSum s).mapL ((pairing y).comp J)).tsum_eq
  refine Eq.trans (tsum_congr fun n ↦ ?_) rep
  rw [coord,map_smul]
  change (((latticeWeight n^k:ℝ):ℂ)⁻¹ * L n y * ((latticeWeight n^k:ℝ):ℂ)) * s (latticeIndex n) =
    s (latticeIndex n) * L n y
  have hne : ((latticeWeight n ^ k:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (hw n).ne')
  field_simp

private theorem spectralBoundary_line_restriction (σ : ℝ) :
    ∃ L : SchwartzBergman (univ : Set ℝ) →L[ℂ] SchwartzMap ℝ ℂ,
      ∀ x t, L x t = x.val (linePoint σ t) := by
  let a : (univ : Set ℝ) := ⟨σ, mem_univ _⟩
  obtain ⟨T,hT,hE⟩ := schwartzBergman_schwartzLine_topology univ isOpen_univ ordConnected_univ univ_nonempty
  have he (x : SchwartzBergman (univ : Set ℝ)) (t : ℝ) : T x a t = x.val (linePoint σ t) := by
    simpa only [weightedVerticalTrace,pow_zero,one_mul] using hT x a t
  let L : SchwartzBergman (univ : Set ℝ) →L[ℂ] SchwartzMap ℝ ℂ := {
    toFun := fun x ↦ T x a
    map_add' := fun x y ↦ SchwartzMap.ext fun t ↦ by change T (x+y) a t = T x a t + T y a t; rw [he,he,he]; rfl
    map_smul' := fun c x ↦ SchwartzMap.ext fun t ↦ by change T (c • x) a t = c * T x a t; rw [he,he]; rfl
    cont := (continuous_apply a).comp hE.continuous }
  exact ⟨L,he⟩

/-- Restricting to a fixed vertical line gives Hilbert analysis coordinates which
reproduce integration against every Schwartz test function. -/
private theorem spectralBoundary_line_incoming (σ : ℝ) (e : SchwartzMap ℝ ℂ ≃L[ℂ] RapidDecaySequence 1) :
    ∃ (k : ℕ) (b : SchwartzBergman (univ : Set ℝ) →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2),
      ∀ x (g : SchwartzMap ℝ ℂ),
        (∑' n : ℕ, b x n * ((latticeWeight n ^ k:ℝ):ℂ) * e g (latticeIndex n)) =
          ∫ t : ℝ, x.val (linePoint σ t) * g t := by
  let μ := (volume : Measure ℝ)
  let J := (SchwartzMap.toLpCLM ℂ ℂ 2 μ).comp e.symm.toContinuousLinearMap
  let pairing := (ContinuousLinearMap.mul ℂ ℂ).lpPairing μ 2 2
  obtain ⟨line,hline⟩ := spectralBoundary_line_restriction σ
  let b := (SchwartzMap.toLpCLM ℂ ℂ 2 μ).comp line
  obtain ⟨k,T,hT⟩ := spectralBoundary_incoming J pairing
  refine ⟨k,T.comp b,fun x g ↦ (hT (b x) (e g)).trans ?_⟩
  change (ContinuousLinearMap.mul ℂ ℂ).lpPairing μ 2 2 ((line x).toLp 2 μ)
    ((e.symm (e g)).toLp 2 μ) = _
  rw [e.symm_apply_apply,ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [(line x).coeFn_toLp 2 μ, g.coeFn_toLp 2 μ] with t ht hu
  rw [ht,hu]
  change line x t * g t = _
  rw [hline]

/-- The fixed-line Gaussian integral factors through a Hilbert space. Its output
map has rapid nuclear coefficients after composition with the quotient projection. -/
private theorem spectralBoundary_line_factorization {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [PolynormableSpace ℂ E] [T2Space E] [CompleteSpace E]
    (p : ℕ → Seminorm ℂ E) (hp : WithSeminorms p) (q : SchwartzBergman (univ : Set ℝ) →L[ℂ] E)
    {G M : ℂ → ℂ} (hG : Differentiable ℂ G) (hM : Differentiable ℂ M) (σ : ℝ)
    (hd : ∀ A : ℝ, ∃ n : ℕ, ∃ C > (0:ℝ), ∀ x : ℂ, |x.re| ≤ A →
      ‖deriv G x‖ ≤ C*(1+|x.im|)^n)
    (hinv : ∃ D ≥ (1:ℝ), ∀ w : ℂ, |w.re-σ| ≤ 1 → G w ≠ 0 ∧ ‖(G w)⁻¹‖ ≤ D)
    (hm : ∀ k : ℕ, ∃ D > (0:ℝ), ∀ w : ℂ, |w.re-σ| ≤ 1 → (1+|w.im|)^k*‖M w‖ ≤ D) :
    let H := lp (fun _ : ℕ ↦ ℂ) 2
    let sourceSpace := SchwartzBergman (univ : Set ℝ)
    ∃ (b : sourceSpace →L[ℂ] H) (R : H →L[ℂ] sourceSpace),
      (∀ x z, (R (b x)).val z = ∫ t : ℝ,
        (M (linePoint σ t) * x.val (linePoint σ t)) * spectralBoundaryKernel G (linePoint σ t) z) ∧
      ∃ r : NuclearPresentation (q.comp R), ∀ j : ℕ, ∃ D : ℝ, ∀ n : ℕ, ‖r.coeff n‖*((n:ℝ)+1)^j ≤ D := by
  obtain ⟨D,hD,hI⟩ := hinv
  obtain ⟨K,he,hk,hb⟩ := spectralBoundary_global_kernel hG hM σ hd
    ⟨0,D,zero_lt_one.trans_le hD, by simpa only [pow_zero,mul_one] using hI⟩ hm
  obtain ⟨e⟩ := realSchwartz_equiv_rapidDecay
  obtain ⟨k,b,hin⟩ := spectralBoundary_line_incoming σ e
  obtain ⟨R,hout,r,hr⟩ := spectralBoundary_contour_presentation p hp K hk hb e k q
  refine ⟨b,R,fun x z ↦ ?_, r, hr⟩
  rw [hout,hin]
  apply integral_congr_ae
  exact ae_of_all _ fun t ↦ by
    change x.val (linePoint σ t) * K z t = _
    rw [he]; ring

private theorem spectralBoundary_order_of_bound {ρ : ℂ} {F : ℂ → ℂ} (hf : AnalyticAt ℂ F ρ)
    (m : ℕ) (h : F =O[𝓝 ρ] (fun z ↦ (z-ρ)^m)) :
    m ≤ analyticOrderAt F ρ := by
  by_contra! hl
  have hn : analyticOrderAt F ρ ≠ ⊤ := hl.ne_top
  have hlt : analyticOrderNatAt F ρ < m := by
    exact_mod_cast (show (analyticOrderNatAt F ρ : ℕ∞) < (m:ℕ∞) by
      rwa [show (analyticOrderNatAt F ρ : ℕ∞) = analyticOrderAt F ρ from ENat.natCast_toNat hn])
  have hsmall : (fun z : ℂ ↦ (z-ρ)^m) =o[𝓝 ρ] (fun z ↦ (z-ρ)^analyticOrderNatAt F ρ) :=
    (isLittleO_pow_pow (𝕜 := ℂ) hlt).comp_tendsto (by simpa using (continuousAt_id (x := ρ)).sub_const ρ)
  have hnon : ∀ᶠ z : ℂ in 𝓝[≠] ρ, (z-ρ)^analyticOrderNatAt F ρ ≠ 0 :=
    by filter_upwards [self_mem_nhdsWithin] with z hz using pow_ne_zero _ (sub_ne_zero.mpr hz)
  exact isLittleO_irrefl hnon.frequently
    (((hf.isTheta_pow_sub hn).2.trans h).trans_isLittleO hsmall |>.mono nhdsWithin_le_nhds)

private theorem spectralBoundary_bound_of_order {ρ : ℂ} {G : ℂ → ℂ} (hg : AnalyticAt ℂ G ρ)
    (m : ℕ) (hm : m ≤ analyticOrderAt G ρ) :
    G =O[𝓝 ρ] (fun z ↦ (z-ρ)^m) := by
  obtain ⟨g,hg',he⟩ := (natCast_le_analyticOrderAt hg).mp hm
  apply (show G =ᶠ[𝓝 ρ] (fun z ↦ (z-ρ)^m • g z) from he).isBigO.trans
  simpa only [smul_eq_mul,mul_one] using
    (isBigO_refl (fun z : ℂ ↦ (z-ρ)^m) (𝓝 ρ)).mul (hg'.continuousAt.isBigO_one ℂ)

/-- On a neighborhood disjoint from a boundary line, the difference between the
regularized and bare Gaussian integrals is bounded by a constant times the generator. -/
private theorem spectralBoundary_line_error {G : ℂ → ℂ} (hG : Continuous G) (σ : ℝ)
    (C : ℝ) (_hC : 0 ≤ C) (hc : ∀ t : ℝ, G (linePoint σ t) ≠ 0 ∧ ‖(G (linePoint σ t))⁻¹‖ ≤ C)
    (f : ℝ → ℂ) (hf : Continuous f) (hi : Integrable f) (ρ : ℂ) (hρ : ρ.re ≠ σ) :
    (fun z : ℂ ↦ (∫ t : ℝ, f t * spectralBoundaryKernel G (linePoint σ t) z)
        - (∫ t : ℝ, Complex.exp ((z-linePoint σ t)^2) * f t / (linePoint σ t-z))) =O[𝓝 ρ] G := by
  let δ := |ρ.re-σ|/2
  let T := |ρ.re-σ|+1
  let sourceSpace := Real.exp (T^2)/δ
  have hd : 0 < δ := half_pos (abs_pos.mpr (sub_ne_zero.mpr hρ))
  have hT : 0 < T := by dsimp [T]; positivity
  have hB : 0 ≤ sourceSpace := div_nonneg (Real.exp_pos _).le hd.le
  have hnear : ∀ᶠ z : ℂ in 𝓝 ρ, |z.re-σ| ∈ Ioo δ T := by
    apply (show ContinuousAt (fun z : ℂ ↦ |z.re-σ|) ρ by fun_prop).eventually_mem
    exact Ioo_mem_nhds (half_lt_self (abs_pos.mpr (sub_ne_zero.mpr hρ))) (by dsimp [T]; linarith)
  apply IsBigO.of_bound ((sourceSpace*C) * ∫ t : ℝ, ‖f t‖)
  filter_upwards [hnear] with z hz
  let w (t : ℝ) := linePoint σ t
  let a (t : ℝ) := Complex.exp ((z-w t)^2) * f t / (w t-z)
  let b (t : ℝ) := a t / G (w t) * G z
  have hwre (t : ℝ) : (w t).re = σ := by simp [w]
  have hw (t : ℝ) : δ ≤ ‖w t-z‖ := by
    calc δ ≤ |z.re - σ| := hz.1.le
         _ = |(w t-z).re| := by rw [Complex.sub_re,hwre,abs_sub_comm]
         _ ≤ _ := Complex.abs_re_le_norm _
  have hw' (t : ℝ) : w t - z ≠ 0 := norm_pos_iff.mp (hd.trans_le (hw t))
  have ha (t : ℝ) : ‖a t‖ ≤ sourceSpace * ‖f t‖ := by
    have he : ‖Complex.exp ((z-w t)^2)‖ ≤ Real.exp (T^2) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simp only [pow_two,Complex.mul_re,Complex.sub_re,Complex.sub_im,hwre]
      nlinarith [sq_abs (z.re-σ), mul_self_le_mul_self (abs_nonneg _) hz.2.le,sq_nonneg (z.im-(w t).im)]
    change ‖Complex.exp ((z-w t)^2)*f t/(w t-z)‖ ≤ _
    rw [norm_div,norm_mul,div_le_iff₀ (hd.trans_le (hw t))]
    calc
      _ ≤ Real.exp (T^2)*‖f t‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
      _ = (sourceSpace*‖f t‖)*δ := by dsimp [sourceSpace]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hw t) (mul_nonneg hB (norm_nonneg _))
  have hb (t : ℝ) : ‖b t‖ ≤ ((sourceSpace*C)*‖G z‖)*‖f t‖ := by
    change ‖a t / G (w t) * G z‖ ≤ _
    rw [div_eq_mul_inv,norm_mul,norm_mul]
    calc
      _ ≤ (sourceSpace*‖f t‖*C)*‖G z‖ := by gcongr; exacts [ha t,(hc t).2]
      _ = _ := by ring
  have hcw : Continuous w := by fun_prop
  have hca : Continuous a := by dsimp [a]; fun_prop (disch := exact hw' _)
  have hcb : Continuous b := (hca.div (hG.comp hcw) (fun t ↦ (hc t).1)).mul continuous_const
  have hai := (hi.norm.const_mul sourceSpace).mono' hca.aestronglyMeasurable (ae_of_all _ ha)
  have hbi := (hi.norm.const_mul ((sourceSpace*C)*‖G z‖)).mono' hcb.aestronglyMeasurable (ae_of_all _ hb)
  have heq (t : ℝ) : f t * spectralBoundaryKernel G (w t) z = a t - b t := by
    rw [spectralBoundaryKernel_offPole (Ne.symm (sub_ne_zero.mp (hw' t))) (hc t).1]
    dsimp only [a,b]
    ring
  change ‖(∫ t : ℝ, f t * spectralBoundaryKernel G (w t) z) - ∫ t : ℝ, a t‖ ≤ _
  simp_rw [heq]
  rw [integral_sub hai hbi,sub_sub_cancel_left,norm_neg]
  calc
    _ ≤ ∫ t : ℝ, ((sourceSpace*C)*‖G z‖)*‖f t‖ :=
      norm_integral_le_of_norm_le (hi.norm.const_mul _) (ae_of_all _ hb)
    _ = _ := by rw [integral_const_mul]; ring

private theorem spectralGaussian_strip {z : ℂ} {a b : ℝ} (f : SchwartzBergman (univ : Set ℝ)) (hab : a<b) :
    UniformlySchwartzOnStrip (fun w ↦ Complex.exp ((z-w)^2) * f.val w) a b := by
  have hf : Differentiable ℂ f.val := fun w ↦
    (f.property.2.1 w (mem_univ _)).differentiableAt (univ_mem' fun _ ↦ mem_univ _)
  have hdiff : Differentiable ℂ (fun w ↦ Complex.exp ((z-w)^2) * f.val w) := by fun_prop
  refine ⟨hab,hdiff.differentiableOn,?_⟩
  intro δ hδ hwidth N _
  obtain ⟨C,hC⟩ := f.property.2.2 a b hab.le (subset_univ _) N
  let T := |z.re|+|a|+|b|
  have hT : 0 ≤ T := by dsimp [T]; positivity
  refine ⟨Real.exp (T^2) * (|C|+1), by positivity, ?_⟩
  have ht : ∀ᶠ y : ℝ in comap abs atTop, 0 < |y| := tendsto_comap.eventually (eventually_gt_atTop 0)
  filter_upwards [ht] with y hy
  intro σ hσ
  let w := (σ:ℂ) + (y:ℂ)*Complex.I
  have re : w.re = σ := by simp [w]
  have im : w.im = y := by simp [w]
  have hσ' : σ ∈ Icc a b := ⟨by linarith [hσ.1],by linarith [hσ.2]⟩
  have haσ : |σ| ≤ |a|+|b| := abs_le.mpr
    ⟨by linarith [hσ'.1,neg_abs_le a,abs_nonneg b],by linarith [hσ'.2,le_abs_self b,abs_nonneg a]⟩
  have hr : |z.re-w.re| ≤ T := (abs_sub _ _).trans (by dsimp [T];rw [re];linarith)
  have hg : ‖Complex.exp ((z-w)^2)‖ ≤ Real.exp (T^2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [pow_two,Complex.mul_re,Complex.sub_re,Complex.sub_im]
    nlinarith [sq_abs (z.re-w.re),mul_nonneg (sub_nonneg.mpr hr) (add_nonneg hT (abs_nonneg (z.re-w.re))),sq_nonneg (z.im-w.im)]
  have hfc : ‖w‖^N * ‖f.val w‖ ≤ C := by
    simpa only [norm_mul,norm_pow] using hC ⟨w,show w.re ∈ Icc a b from re ▸ hσ',rfl⟩
  have hi : |y| ≤ ‖w‖ := im ▸ Complex.abs_im_le_norm w
  change ‖Complex.exp ((z-w)^2) * f.val w‖ ≤ _
  rw [norm_mul,le_div_iff₀ (pow_pos hy _)]
  calc
    _ = ‖Complex.exp ((z-w)^2)‖ * (|y|^N * ‖f.val w‖) := by ring
    _ ≤ Real.exp (T^2) * (‖w‖^N * ‖f.val w‖) := by gcongr
    _ ≤ Real.exp (T^2) * (|C|+1) := by gcongr; linarith [le_abs_self C]

/-- On two fixed lines a Gaussian-localized Cauchy integral recovers the original
Schwartz–Bergman function at every point strictly between the lines. -/
private theorem spectralBoundary_cauchy (f : SchwartzBergman (univ : Set ℝ))
    (c d : ℝ) (z : ℂ) (hz : z.re ∈ Ioo c d) :
    let Φ := fun w ↦ Complex.exp ((z-w)^2) * f.val w
    (∫ t : ℝ, Φ ((d:ℂ)+t*Complex.I) / ((d:ℂ)+t*Complex.I-z)) -
    (∫ t : ℝ, Φ ((c:ℂ)+t*Complex.I) / ((c:ℂ)+t*Complex.I-z)) =
      2*(Real.pi:ℂ)*f.val z := by
  dsimp only
  let Φ := fun w ↦ Complex.exp ((z-w)^2) * f.val w
  have hΦ : UniformlySchwartzOnStrip Φ (c-1) (d+1) := spectralGaussian_strip f (by linarith [hz.1,hz.2])
  have hc : c-1+1 = c := by ring
  have hd : d+1-1 = d := by ring
  have h := asymptoticCauchy_eq_iteratedDeriv hΦ 1 one_pos (by rw [hc,hd];exact hz.1.trans hz.2) 0 z (by rwa [hc,hd])
  simp only [hc,hd,Nat.factorial_zero,Nat.cast_one,zero_add,pow_one,iteratedDeriv_zero,verticalLineIntegral] at h
  have hΦz : Φ z = f.val z := by simp [Φ]
  rw [hΦz] at h
  change (∫ t : ℝ, Φ ((d:ℂ)+t*Complex.I) / ((d:ℂ)+t*Complex.I-z)) -
    (∫ t : ℝ, Φ ((c:ℂ)+t*Complex.I) / ((c:ℂ)+t*Complex.I-z)) = _
  field_simp [Real.pi_ne_zero, Complex.I_ne_zero] at h
  simpa only [mul_comm Complex.I] using h

/-- The signed pair of regularized Gaussian lines has the same finite jet as the
original test at each common zero of the indicated order. -/
private theorem spectralBoundary_signed_jets (c d : ℝ) (G₀ G₁ : ℂ → ℂ) (F region targetSet : SchwartzBergman (univ : Set ℝ))
    (ρ : ℂ) (hρ : ρ.re ∈ Ioo c d) (m : ℕ)
    (hG₀ : Differentiable ℂ G₀) (hG₁ : Differentiable ℂ G₁)
    (hv₀ : ∃ D ≥ (1:ℝ), ∀ t, G₀ (linePoint d t) ≠ 0 ∧ ‖(G₀ (linePoint d t))⁻¹‖ ≤ D)
    (hv₁ : ∃ D ≥ (1:ℝ), ∀ t, G₁ (linePoint c t) ≠ 0 ∧ ‖(G₁ (linePoint c t))⁻¹‖ ≤ D)
    (ho₀ : m ≤ analyticOrderAt G₀ ρ) (ho₁ : m ≤ analyticOrderAt G₁ ρ)
    (hU : ∀ z, region.val z = ∫ t : ℝ, F.val (linePoint d t) * spectralBoundaryKernel G₀ (linePoint d t) z)
    (hV : ∀ z, targetSet.val z = ∫ t : ℝ, F.val (linePoint c t) * spectralBoundaryKernel G₁ (linePoint c t) z)
    (j : ℕ) (hj : j < m) :
    iteratedDeriv j ((2*(Real.pi:ℂ))⁻¹ • region + (-(2*(Real.pi:ℂ))⁻¹) • targetSet - F).val ρ = 0 := by
  let bare (s : ℝ) (z : ℂ) := ∫ t : ℝ, Complex.exp ((z-linePoint s t)^2) * F.val (linePoint s t)/(linePoint s t-z)
  let p := fun z : ℂ ↦ (z-ρ)^m
  have err (G : ℂ → ℂ) (s : ℝ) (region' : SchwartzBergman (univ : Set ℝ)) (hs : ρ.re ≠ s)
      (hg : Differentiable ℂ G) (ho : m ≤ analyticOrderAt G ρ)
      (hv : ∃ D ≥ (1:ℝ), ∀ t, G (linePoint s t) ≠ 0 ∧ ‖(G (linePoint s t))⁻¹‖ ≤ D)
      (hu : ∀ z, region'.val z = ∫ t : ℝ, F.val (linePoint s t) * spectralBoundaryKernel G (linePoint s t) z) :
      (fun z ↦ region'.val z - bare s z) =O[𝓝 ρ] p := by
    obtain ⟨D,hD,hv⟩ := hv
    obtain ⟨line,hl⟩ := spectralBoundary_line_restriction s
    have hb := spectralBoundary_line_error hg.continuous s D (zero_le_one.trans hD) hv
      (line F) (line F).continuous (line F).integrable ρ hs
    have he : (fun z ↦ region'.val z - bare s z) = (fun z : ℂ ↦ (∫ t : ℝ, line F t * spectralBoundaryKernel G (linePoint s t) z)
        - (∫ t : ℝ, Complex.exp ((z-linePoint s t)^2) * line F t / (linePoint s t-z))) := by
      funext z
      simp only [hu,hl,bare]
    rw [he]
    exact hb.trans (spectralBoundary_bound_of_order (hg.analyticAt ρ) m ho)
  have h₀ := err G₀ d region hρ.2.ne hG₀ ho₀ hv₀ hU
  have h₁ := err G₁ c targetSet hρ.1.ne' hG₁ ho₁ hv₁ hV
  let α : ℂ := (2*(Real.pi:ℂ))⁻¹
  let S := α • region + (-α) • targetSet - F
  have he : S.val =ᶠ[𝓝 ρ] fun z ↦ α * ((region.val z-bare d z) - (targetSet.val z-bare c z)) := by
    filter_upwards [Complex.continuous_re.continuousAt.eventually_mem (Ioo_mem_nhds hρ.1 hρ.2)] with z hz
    have hc : bare d z - bare c z = 2*(Real.pi:ℂ)*F.val z := spectralBoundary_cauchy F c d z hz
    change α * region.val z + (-α) * targetSet.val z - F.val z = _
    have ha : α * (2*(Real.pi:ℂ)) = 1 := inv_mul_cancel₀ (by exact_mod_cast mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) Real.pi_ne_zero)
    linear_combination α * hc + F.val z * ha
  have han : AnalyticAt ℂ S.val ρ :=
    ((show Differentiable ℂ S.val from fun z ↦
      (S.property.2.1 z (mem_univ _)).differentiableAt (univ_mem' fun _ ↦ mem_univ _))).analyticAt ρ
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero han).mp
    (spectralBoundary_order_of_bound han m (he.isBigO.trans ((h₀.sub h₁).const_mul_left α))) j hj

private theorem spectralBoundary_countable_seminorms (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [PolynormableSpace ℂ E] [FirstCountableTopology E] :
    ∃ p : ℕ → Seminorm ℂ E, WithSeminorms p := by
  classical
  obtain ⟨region,hU⟩ := (𝓝 (0:E)).exists_antitone_basis
  choose p hp hsub using fun n ↦ (PolynormableSpace.hasBasis_zero_ball ℂ E).mem_iff.mp (hU.mem n)
  refine ⟨p,SeminormFamily.withSeminorms_of_hasBasis p ((hU.1).to_hasBasis ?_ ?_)⟩
  · intro n _
    exact ⟨(p n).ball 0 1,SeminormFamily.basisSets_singleton_mem p n one_pos,hsub n⟩
  · intro targetSet hV
    obtain ⟨s,r,hr,rfl⟩ := (SeminormFamily.basisSets_iff p).mp hV
    exact hU.1.mem_iff.mp ((s.sup p).ball_mem_nhds (Seminorm.continuous_finsetSup (fun i _ ↦ hp i)) hr)
private theorem spectralBoundary_interleaved_decay (c₀ c₁ : ℕ → ℂ)
    (hr₀ : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, ‖c₀ n‖ * ((n:ℝ)+1)^k ≤ C)
    (hr₁ : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, ‖c₁ n‖ * ((n:ℝ)+1)^k ≤ C)
    (k : ℕ) : ∃ C : ℝ, ∀ n : ℕ,
      ‖Sum.elim c₀ c₁ (Equiv.natSumNatEquivNat.symm n)‖ * ((n:ℝ)+1)^k ≤ C := by
  let e := Equiv.natSumNatEquivNat
  let c := Sum.elim c₀ c₁
  obtain ⟨A,hA⟩ := hr₀ k
  obtain ⟨sourceSpace,hB⟩ := hr₁ k
  refine ⟨2^k*max A sourceSpace,fun n ↦ ?_⟩
  obtain ⟨i,rfl⟩ := e.surjective n
  change ‖c (e.symm (e i))‖ * ((e i:ℕ)+1:ℝ)^k ≤ _
  rw [e.symm_apply_apply]
  have heval : ∀ j : ℕ, (e (Sum.inl j) : ℕ) = 2*j ∧ e (Sum.inr j) = 2*j+1 :=
    fun j ↦ ⟨congrFun Equiv.natSumNatEquivNat_apply (Sum.inl j),congrFun Equiv.natSumNatEquivNat_apply (Sum.inr j)⟩
  cases i with
  | inl j =>
    rw [(heval j).1]
    change ‖c₀ j‖ * _ ≤ _
    push_cast
    have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ)≤2*j+1) (by linarith : (2:ℝ)*j+1 ≤ 2*(j+1)) k
    rw [mul_pow] at hpow
    calc
      _ ≤ ‖c₀ j‖*(2^k*((j:ℝ)+1)^k) := mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = 2^k*(‖c₀ j‖*((j:ℝ)+1)^k) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ((hA j).trans (le_max_left ..)) (by positivity)
  | inr j =>
    rw [(heval j).2]
    change ‖c₁ j‖ * _ ≤ _
    push_cast
    rw [show (2:ℝ)*j+1+1=2*((j:ℝ)+1) by ring,mul_pow,mul_left_comm]
    exact mul_le_mul_of_nonneg_left ((hB j).trans (le_max_right ..)) (by positivity)

private theorem spectralBoundary_interleaved_equicontinuous {X H₀ H₁ : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup H₀] [NormedSpace ℂ H₀] [NormedAddCommGroup H₁] [NormedSpace ℂ H₁]
    (l₀ : ℕ → H₀ →L[ℂ] ℂ) (l₁ : ℕ → H₁ →L[ℂ] ℂ)
    (h₀ : EquicontinuousAt (fun n t ↦ l₀ n t) 0)
    (h₁ : EquicontinuousAt (fun n t ↦ l₁ n t) 0)
    (P₀ : X →L[ℂ] H₀) (P₁ : X →L[ℂ] H₁) :
    let d := Sum.elim (fun n ↦ (l₀ n).comp P₀) (fun n ↦ (l₁ n).comp P₁)
    EquicontinuousAt (fun n t ↦ d (Equiv.natSumNatEquivNat.symm n) t) 0 := by
  intro d targetSet hV
  have hu := (P₀.continuous.tendsto' 0 0 (map_zero P₀)).eventually (h₀ targetSet hV)
  have hv := (P₁.continuous.tendsto' 0 0 (map_zero P₁)).eventually (h₁ targetSet hV)
  filter_upwards [hu,hv] with x hx hy n
  cases e : Equiv.natSumNatEquivNat.symm n with
  | inl j => simpa only [d,Sum.elim_inl,ContinuousLinearMap.comp_apply,map_zero] using hx j
  | inr j => simpa only [d,Sum.elim_inr,ContinuousLinearMap.comp_apply,map_zero] using hy j

set_option backward.isDefEq.respectTransparency false in
/-- Finite interleaving of two rapid presentations over a common source, after
precomposition with arbitrary bounded maps. A jointly bounded family of target vectors
gives one Banach disc, even when the original presentations used different discs. -/
private theorem spectralBoundary_interleave {X H₀ H₁ E : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup H₀] [NormedSpace ℂ H₀]
    [NormedAddCommGroup H₁] [NormedSpace ℂ H₁]
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [PolynormableSpace ℂ E] [T2Space E] [CompleteSpace E]
    {S₀ : H₀ →L[ℂ] E} {S₁ : H₁ →L[ℂ] E}
    (r₀ : NuclearPresentation S₀) (r₁ : NuclearPresentation S₁)
    (hr₀ : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, ‖r₀.coeff n‖ * ((n:ℝ)+1)^k ≤ C)
    (hr₁ : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, ‖r₁.coeff n‖ * ((n:ℝ)+1)^k ≤ C)
    (P₀ : X →L[ℂ] H₀) (P₁ : X →L[ℂ] H₁) :
    ∃ r : NuclearPresentation (S₀.comp P₀ + S₁.comp P₁),
      ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, ‖r.coeff n‖ * ((n:ℝ)+1)^k ≤ C := by
  classical
  let e := Equiv.natSumNatEquivNat
  let c : ℕ⊕ℕ → ℂ := Sum.elim r₀.coeff r₁.coeff
  let d : ℕ⊕ℕ → X →L[ℂ] ℂ := Sum.elim (fun n ↦ (r₀.functional n).comp P₀) (fun n ↦ (r₁.functional n).comp P₁)
  let v : ℕ⊕ℕ → E := Sum.elim (fun n ↦ (r₀.vector n:E)) (fun n ↦ (r₁.vector n:E))
  have hb : IsVonNBounded ℂ (range v) := by
    apply (r₀.isBanachDisc.bounded.union r₁.isBanachDisc.bounded).subset
    rintro _ ⟨i,rfl⟩
    cases i with
    | inl n => exact Or.inl (r₀.vector_mem n)
    | inr n => exact Or.inr (r₁.vector_mem n)
  obtain ⟨D,hD,hmem⟩ := spectralBoundary_bounded_common_disc v hb
  let w (n : ℕ) : Submodule.span ℂ D := ⟨v (e.symm n),Submodule.subset_span (hmem (e.symm n))⟩
  let r : NuclearPresentation (S₀.comp P₀ + S₁.comp P₁) := {
    coeff := c ∘ e.symm
    functional := d ∘ e.symm
    vector := w
    disc := D
    isBanachDisc := hD
    vector_mem := fun n ↦ hmem (e.symm n)
    summable_coeff := by
      have h : Summable (fun i ↦ ‖c i‖) := Summable.sum _ r₀.summable_coeff r₁.summable_coeff
      exact (e.symm.summable_iff (f := fun i ↦ ‖c i‖)).mpr h
    equicontinuous := spectralBoundary_interleaved_equicontinuous r₀.functional r₁.functional r₀.equicontinuous r₁.equicontinuous P₀ P₁
    hasSum := by
      intro x
      let f (i : ℕ⊕ℕ) := (c i * d i x) • v i
      have h : HasSum f (S₀ (P₀ x) + S₁ (P₁ x)) := HasSum.sum (f := f) (r₀.hasSum (P₀ x)) (r₁.hasSum (P₁ x))
      exact (e.symm.hasSum_iff (f := f) (a := S₀ (P₀ x) + S₁ (P₁ x))).mpr h }
  refine ⟨r,?_⟩
  change ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, ‖c (e.symm n)‖ * ((n:ℝ)+1)^k ≤ C
  exact spectralBoundary_interleaved_decay r₀.coeff r₁.coeff hr₀ hr₁

/-- The two boundary actions descend jointly through the spectral quotient. Coefficients
may encode either orientation or the Cauchy normalization. The Hilbert product permits
orthogonal elimination of the full synthesis kernel after taking their signed sum. -/
private theorem spectralBoundary_two_sided_descent {sourceSpace H₀ H₁ E : Type*}
    [AddCommGroup sourceSpace] [Module ℂ sourceSpace] [TopologicalSpace sourceSpace]
    [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [PolynormableSpace ℂ E] [T2Space E] [CompleteSpace E]
    (q : sourceSpace →L[ℂ] E) (hq : Topology.IsQuotientMap q) (T : E →L[ℂ] E)
    (b₀ : sourceSpace →L[ℂ] H₀) (b₁ : sourceSpace →L[ℂ] H₁)
    (S₀ : H₀ →L[ℂ] E) (S₁ : H₁ →L[ℂ] E) (c₀ c₁ : ℂ)
    (r₀ : NuclearPresentation S₀) (r₁ : NuclearPresentation S₁)
    (hr₀ : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, ‖r₀.coeff n‖ * ((n:ℝ)+1)^k ≤ C)
    (hr₁ : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, ‖r₁.coeff n‖ * ((n:ℝ)+1)^k ≤ C)
    (hT : ∀ x, c₀ • S₀ (b₀ x) + c₁ • S₁ (b₁ x) = T (q x)) :
    IsStronglyNuclearOperator T := by
  let H := WithLp 2 (H₀ × H₁)
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ H₀ H₁
  let P₀ : H →L[ℂ] H₀ := (ContinuousLinearMap.fst ℂ H₀ H₁).comp e.toContinuousLinearMap
  let P₁ : H →L[ℂ] H₁ := (ContinuousLinearMap.snd ℂ H₀ H₁).comp e.toContinuousLinearMap
  let S : H →L[ℂ] E := S₀.comp P₀ + S₁.comp P₁
  let b : sourceSpace →L[ℂ] H := e.symm.toContinuousLinearMap.comp ((c₀ • b₀).prod (c₁ • b₁))
  obtain ⟨r,hr⟩ := spectralBoundary_interleave r₀ r₁ hr₀ hr₁ P₀ P₁
  apply spectralBoundary_strong_of_synthesis q hq b S T _ r hr
  intro x
  change S₀ (e (e.symm ((c₀ • b₀) x,(c₁ • b₁) x))).1 + S₁ (e (e.symm ((c₀ • b₀) x,(c₁ • b₁) x))).2 = _
  simpa using hT x

private theorem spectralBoundary_globalStrip {f : ℂ → ℂ} (hc : Continuous f) {a b : ℝ}
    (decay : ∀ k : ℕ, 1 ≤ k → ∃ C > (0:ℝ), ∀ᶠ y : ℝ in comap abs atTop, ∀ t ∈ Icc a b,
      ‖f ((t : ℂ) + y * Complex.I)‖ ≤ C / |y|^k) (k : ℕ) :
    ∃ C > (0:ℝ), ∀ z : ℂ, z.re ∈ Icc a b → ‖f z‖ * (1 + |z.im|)^k ≤ C := by
  obtain ⟨C,hC,h⟩ := decay (k+1) (by omega)
  obtain ⟨R,hR⟩ := eventually_atTop.1 (eventually_comap.mp h)
  let M := |a| + |b| + |R| + 2
  let w (z : ℂ) : ℝ := ‖f z‖ * (1 + |z.im|)^k
  have hw : Continuous w := hc.norm.mul ((continuous_const.add Complex.continuous_im.abs).pow k)
  obtain ⟨D,hD⟩ := (isCompact_closedBall (0 : ℂ) M).bddAbove_image hw.continuousOn
  refine ⟨max D (C*2^k),lt_of_lt_of_le (by positivity : 0 < C*2^k) (le_max_right _ _),?_⟩
  intro z hz
  by_cases hy : max R 1 ≤ |z.im|
  · have hy1 : 1 ≤ |z.im| := (le_max_right _ _).trans hy
    have h0 : 0 < |z.im| := zero_lt_one.trans_le hy1
    have hg := hR |z.im| ((le_max_left _ _).trans hy) z.im rfl z.re hz
    rw [Complex.re_add_im] at hg
    have hh := (le_div_iff₀ (pow_pos h0 _)).mp hg
    have hpow : (1 + |z.im|)^k ≤ 2^k * |z.im|^k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) k
    have hpow' : |z.im|^k ≤ |z.im|^(k+1) := by
      rw [pow_succ]; exact le_mul_of_one_le_right (by positivity) hy1
    apply le_trans _ (le_max_right _ _)
    calc
      _ ≤ ‖f z‖ * (2^k * |z.im|^k) := by gcongr
      _ ≤ ‖f z‖ * (2^k * |z.im|^(k+1)) := by gcongr
      _ = (‖f z‖ * |z.im|^(k+1)) * 2^k := by ring
      _ ≤ _ := by gcongr
  · apply le_trans _ (le_max_left _ _)
    apply hD ⟨z,?_,rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hre : |z.re| ≤ |a| + |b| := abs_le.mpr ⟨by linarith [hz.1, neg_abs_le a, abs_nonneg b],
      by linarith [hz.2,le_abs_self b,abs_nonneg a]⟩
    have hi : |z.im| < max R 1 := lt_of_not_ge hy
    have hh : max R 1 ≤ |R|+1 := max_le (by linarith [le_abs_self R]) (by linarith [abs_nonneg R])
    dsimp [M]
    linarith [Complex.norm_le_abs_re_add_abs_im z]

end SpectralBoundarySynthesis

section SpectralBoundaryArithmetic

open Filter Metric Asymptotics

private theorem spectralBoundary_strip_estimate {L : ℂ → ℂ} (σ : ℝ) (hL : MeromorphicNFOn L univ)
    (hGrowth : ∀ a b : ℝ, a < b → ∃ M : ℝ, 0 < M ∧ (L : ℂ → ℂ) =O[comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)] fun z : ℂ ↦ |Complex.im z| ^ M) (R : ℝ) (hR : 0 < R) :
    ∃ C M T : ℝ, 0 < C ∧ 0 < M ∧ ∀ z : ℂ, |z.re - σ| ≤ R → T < |z.im| →
      AnalyticAt ℂ L z ∧ ‖L z‖ ≤ C * |z.im| ^ M := by
  let a := σ - R - 1
  let b := σ + R + 1
  obtain ⟨M, hM, hg⟩ := hGrowth a b (by dsimp [a, b]; linarith)
  obtain ⟨C, hC, hg⟩ := Asymptotics.isBigO_iff'.mp hg
  rw [eventually_inf_principal, eventually_comap, eventually_atTop] at hg
  obtain ⟨T, hT⟩ := hg
  have hB (z : ℂ) (hz : z.re ∈ Icc a b) (ht : T ≤ |z.im|) :
      ‖L z‖ ≤ C * |z.im| ^ M := by
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using hT _ ht z rfl hz
  refine ⟨C, M, T, hC, hM, fun z hz ht ↦ ⟨?_, hB _ ⟨?_, ?_⟩ ht.le⟩⟩ <;>
    try first | (dsimp [a, b]; linarith [(abs_le.mp hz).1, (abs_le.mp hz).2])
  apply (hL (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  by_contra! hp
  have hr : z.re ∈ Ioo a b := by
    constructor <;> dsimp [a, b] <;> linarith [(abs_le.mp hz).1, (abs_le.mp hz).2]
  have him : Continuous (fun u : ℂ ↦ |u.im|) := Complex.continuous_im.abs
  have hn₁ := (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds hr
  have hn₂ : ∀ᶠ u : ℂ in 𝓝 z, |u.im| ∈ Ioo T (|z.im| + 1) :=
    (isOpen_Ioo.preimage him).mem_nhds ⟨ht, by linarith⟩
  have hbnd : ∀ᶠ u : ℂ in 𝓝 z, ‖L u‖ ≤ C * (|z.im| + 1) ^ M := by
    filter_upwards [hn₁, hn₂] with u hu hv
    exact (hB u ⟨hu.1.le, hu.2.le⟩ hv.1.le).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hv.2.le hM.le) hC.le)
  have hinf := (tendsto_norm_cobounded_atTop.comp
    (tendsto_cobounded_of_meromorphicOrderAt_neg hp)).eventually_gt_atTop (C * (|z.im| + 1) ^ M)
  obtain ⟨u, hu, hv⟩ := ((hbnd.filter_mono nhdsWithin_le_nhds).and hinf).exists
  exact (not_lt_of_ge hu) hv

local notation "Λr" => Λ(χ, τ, hτ)

/-- The gamma-stripped, pole-cleared entire spectral generator of the early spectral section. -/
private def spectralFiniteG (z : ℂ) := (heckeGammaFactor χ z)⁻¹ * (Λr).val z

private theorem spectralFiniteG_diff : Differentiable ℂ (spectralFiniteG χ τ hτ) :=
  (differentiable_inv_heckeGammaFactor χ).mul (Λr).property

private def spectralFiniteP (z : ℂ) : ℂ := open Classical in
  let b := ((existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose : ℂ)*Complex.I
  let δ : ℕ := if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0
  (z+b)^δ * (1-z-b)^δ

private theorem spectralFiniteP_diff : Differentiable ℂ (spectralFiniteP χ τ hτ) := by
  unfold spectralFiniteP; fun_prop

private theorem spectralFiniteP_ne {z : ℂ} (hz : 1 < z.re) : spectralFiniteP χ τ hτ z ≠ 0 := by
  dsimp only [spectralFiniteP]
  apply mul_ne_zero <;> apply pow_ne_zero <;> intro he <;> have h := congrArg Complex.re he <;> simp [Complex.mul_re] at h <;> linarith

private theorem spectralFiniteG_right {z : ℂ} (hz : 1 < z.re) :
    spectralFiniteG χ τ hτ z = spectralFiniteP χ τ hτ z * finiteHeckeL χ ⟨z,hz⟩ := by
  let polarPoly := spectralFiniteP χ τ hτ
  let L := continuedCompletedHeckeL χ
  obtain ⟨hL,hse⟩ := continuedCompletedHeckeL_spec χ
  have hP := spectralFiniteP_diff χ τ hτ
  have hm : MeromorphicOn (polarPoly*L) univ := fun s _ ↦ (hP.analyticAt s).meromorphicAt.mul (hL (mem_univ s)).meromorphicAt
  have hNF := (meromorphicNFAt_mul_iff_right (hP.analyticAt z) (spectralFiniteP_ne χ τ hτ hz)).2 (hL (mem_univ z))
  change (heckeGammaFactor χ z)⁻¹ * toMeromorphicNFOn (polarPoly*L) univ z = _
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ z),toMeromorphicNFAt_eq_self.mpr hNF]
  change (heckeGammaFactor χ z)⁻¹ * (polarPoly z*L z) = polarPoly z*_
  have hγ := heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hz)
  rw [show L z = heckeGammaFactor χ z * finiteHeckeL χ ⟨z,hz⟩ from hse ⟨z,hz⟩]
  field_simp

private theorem spectralFiniteG_eq_finite (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hseries : ∀ s : {s : ℂ // 1<s.re}, L s = finiteHeckeL χ s) :
    spectralFiniteG χ τ hτ = toMeromorphicNFOn (spectralFiniteP χ τ hτ * L) univ := by
  have hn : MeromorphicNFOn (spectralFiniteG χ τ hτ) univ := fun s _ ↦ ((spectralFiniteG_diff χ τ hτ).analyticAt s).meromorphicNFAt
  have hm : MeromorphicOn (spectralFiniteP χ τ hτ * L) univ := fun s _ ↦
    ((spectralFiniteP_diff χ τ hτ).analyticAt s).meromorphicAt.mul (hL (mem_univ s)).meromorphicAt
  rw [←toMeromorphicNFOn_eq_self.mpr hn]
  apply heckeEulerProductOutside_eq_finite_nf_eq _ _ hn.meromorphicOn hm
  intro x hx
  rw [spectralFiniteG_right χ τ hτ hx]
  change _ = _ * L x
  rw [hseries ⟨x,hx⟩]

private theorem spectralFiniteG_order (z : ℂ) :
    meromorphicOrderAt (continuedCompletedHeckeL χ) z ≤ meromorphicOrderAt (spectralFiniteG χ τ hτ) z := by
  obtain ⟨L,hL,hseries,hord⟩ := spectralNuclearity_trace_finite_companion χ
  have hP := (spectralFiniteP_diff χ τ hτ).analyticAt
  have hm : MeromorphicOn (spectralFiniteP χ τ hτ * L) univ := fun s _ ↦
    (hP s).meromorphicAt.mul (hL (mem_univ s)).meromorphicAt
  rw [spectralFiniteG_eq_finite χ τ hτ L hL hseries,meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ _),
    meromorphicOrderAt_mul (hP z).meromorphicAt (hL (mem_univ z)).meromorphicAt]
  exact (hord z).trans (le_add_of_nonneg_left (hP z).meromorphicOrderAt_nonneg)

/-- Each retained multiplicity is dominated by the analytic order of the entire
finite generator at the shifted site used by the actual spectral quotient. -/
private theorem spectralBoundaryFinite_shifted_retained_order (a : ℝ) (z : ℂ)
    (hz : 0 < analyticOrderAt ((Λr).val : ℂ → ℂ) z) :
    ((analyticOrderAt ((Λr).val : ℂ → ℂ) z).toNat : ℕ∞) ≤
      analyticOrderAt (fun s ↦ (spectralFiniteG χ τ hτ) (s + (a:ℂ))) (z - (a:ℂ)) := by
  obtain ⟨k, hk, hreg, hord⟩ := spectralNuclearity_trace_zero_order χ τ hτ ⟨z,hz⟩
  change analyticOrderAt ((Λr).val : ℂ → ℂ) z = (k:ℕ∞) at hreg
  have hZ := (continuedCompletedHeckeL_spec χ).1
  rw [MeromorphicOn.divisor_apply hZ.meromorphicOn (mem_univ _)] at hord
  have hzord : meromorphicOrderAt (continuedCompletedHeckeL χ) z = (k:ℤ) := by
    cases h : meromorphicOrderAt (continuedCompletedHeckeL χ) z with
    | top => rw [h] at hord; simp at hord; omega
    | coe i => rw [h] at hord; simpa using congrArg (fun n : ℤ ↦ (n:WithTop ℤ)) hord
  have hfin := spectralFiniteG_order χ τ hτ z
  rw [hzord,((spectralFiniteG_diff χ τ hτ).analyticAt z).meromorphicOrderAt_eq] at hfin
  have hshift : analyticOrderAt (fun s ↦ (spectralFiniteG χ τ hτ) (s+(a:ℂ))) (z-(a:ℂ)) =
      analyticOrderAt ((spectralFiniteG χ τ hτ):ℂ → ℂ) z := by
    rw [show (fun s ↦ (spectralFiniteG χ τ hτ) (s+(a:ℂ))) =
      ((spectralFiniteG χ τ hτ) : ℂ → ℂ) ∘ (fun s : ℂ ↦ s+(a:ℂ)) by rfl,
      analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp),sub_add_cancel]
  rw [hshift,hreg,ENat.toNat_natCast]
  cases hh : analyticOrderAt ((spectralFiniteG χ τ hτ):ℂ → ℂ) z with
  | top => exact le_top
  | coe n => rw [hh,ENat.map_natCast] at hfin; exact_mod_cast hfin

/-- The entire pole-cleared finite generator has a polynomial bound uniformly up
and down each fixed strip, including its continued values in the finite-height region. -/
private theorem spectralBoundaryFinite_strip_growth (W : ℝ) :
    ∃ n : ℕ, ∃ C > (0:ℝ), ∀ z : ℂ, |z.re| ≤ W →
      ‖(spectralFiniteG χ τ hτ) z‖ ≤ C*(1+|z.im|)^n := by
  classical
  let L := (finiteHeckeL_exists_continuation χ).choose
  obtain ⟨hL,hs⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  let t := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
  let p := spectralFiniteP χ τ hτ
  let G := spectralFiniteG χ τ hτ
  have hp := spectralFiniteP_diff χ τ hτ
  have hm : MeromorphicOn (p*L) univ := fun z _ ↦ (hp.analyticAt z).meromorphicAt.mul (hL (mem_univ z)).meromorphicAt
  have he (z : ℂ) (hz : AnalyticAt ℂ L z) : G z = p z * L z := by
    change spectralFiniteG χ τ hτ z = _
    rw [spectralFiniteG_eq_finite χ τ hτ L hL hs,toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ _),
      toMeromorphicNFAt_eq_self.mpr ((hp.analyticAt z).mul hz).meromorphicNFAt]
    rfl
  let polarPoly := |W|+|t|+3
  have hP : 1 ≤ polarPoly := by dsimp [polarPoly]; linarith [abs_nonneg W,abs_nonneg t]
  have hpb (z : ℂ) (hz : |z.re|≤W) : ‖p z‖ ≤ polarPoly^2*(1+|z.im|)^2 := by
    let b := (t:ℂ)*Complex.I
    have hbn : ‖b‖=|t| := by simp [b]
    have hu : polarPoly + |z.im| ≤ polarPoly*(1+|z.im|) := by nlinarith [mul_le_mul_of_nonneg_right hP (abs_nonneg z.im)]
    have hz1 := Complex.norm_le_abs_re_add_abs_im z
    have h1 : ‖z+b‖ ≤ polarPoly*(1+|z.im|) := (norm_add_le _ _).trans (by rw [hbn]; apply le_trans _ hu; dsimp [polarPoly]; linarith [le_abs_self W])
    have h2 : ‖1-z-b‖ ≤ polarPoly*(1+|z.im|) := calc
      _ ≤ ‖1-z‖+‖b‖ := norm_sub_le _ _
      _ ≤ (‖(1:ℂ)‖+‖z‖)+|t| := by rw [hbn]; exact add_le_add_left (norm_sub_le _ _) _
      _ ≤ _ := by rw [norm_one]; apply le_trans _ hu; dsimp [polarPoly]; linarith [le_abs_self W]
    by_cases hd : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype=1
    · change ‖(z+b)^(if _ then (1:ℕ) else 0)*(1-z-b)^(if _ then (1:ℕ) else 0)‖ ≤ _
      simp only [hd,ite_true,pow_one,norm_mul]
      rw [←mul_pow,pow_two]
      exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    · change ‖(z+b)^(if _ then (1:ℕ) else 0)*(1-z-b)^(if _ then (1:ℕ) else 0)‖ ≤ _
      simp only [ite_eq_right hd,pow_zero,mul_one,norm_one]
      apply one_le_mul_of_one_le_of_one_le <;> apply one_le_pow₀
      · exact hP
      · linarith [abs_nonneg z.im]
  obtain ⟨D,M,T,hD,hM,hgrowth⟩ := spectralBoundary_strip_estimate 0 hL
    (finiteHeckeL_continuation_isBigO_rpow χ L hL hs) (|W|+1) (by positivity)
  have hG : Continuous G := (spectralFiniteG_diff χ τ hτ).continuous
  obtain ⟨A,hA⟩ := (isCompact_closedBall (0:ℂ) (|W|+|T|+1)).exists_bound_of_continuousOn hG.continuousOn
  let n := ⌈M⌉₊
  let C := max 1 (max A (polarPoly^2*D))
  have hC : 1 ≤ C := le_max_left _ _
  refine ⟨n+2,C,zero_lt_one.trans_le hC,?_⟩
  intro z hz
  let H := 1+|z.im|
  have hH : 1 ≤ H := by dsimp [H]; linarith [abs_nonneg z.im]
  by_cases ht : T < |z.im|
  · obtain ⟨ha,hgrow⟩ := hgrowth z (by rw [sub_zero]; linarith [le_abs_self W]) ht
    have hpow : |z.im|^M ≤ H^n := calc
      _ ≤ H^M := Real.rpow_le_rpow (abs_nonneg _) (by dsimp [H]; linarith) hM.le
      _ ≤ H^(n:ℝ) := Real.rpow_le_rpow_of_exponent_le hH (Nat.le_ceil M)
      _ = _ := Real.rpow_natCast ..
    change ‖G z‖ ≤ C*H^(n+2)
    rw [he z ha,norm_mul]
    calc
      _ ≤ (polarPoly^2*H^2)*(D*H^n) := mul_le_mul (hpb z hz) (hgrow.trans (mul_le_mul_of_nonneg_left hpow hD.le)) (norm_nonneg _) (by positivity)
      _ = (polarPoly^2*D)*H^(n+2) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (by positivity)
  · have hmem : z ∈ closedBall (0:ℂ) (|W|+|T|+1) := by
      rw [mem_closedBall,dist_zero_right]
      linarith [Complex.norm_le_abs_re_add_abs_im z,le_abs_self W,le_abs_self T]
    have hb : ‖G z‖ ≤ C := (hA z hmem).trans ((le_max_left _ _).trans (le_max_right _ _))
    exact hb.trans (le_mul_of_one_le_right (zero_le_one.trans hC) (one_le_pow₀ hH))

/-- In every fixed vertical strip and after any real shift, the derivative of the
actual finite generator has at most polynomial growth in absolute height. -/
private theorem spectralBoundaryFinite_shifted_deriv (a W : ℝ) :
    ∃ n : ℕ, ∃ C > (0:ℝ), ∀ z : ℂ, |z.re| ≤ W →
      ‖deriv (fun s ↦ (spectralFiniteG χ τ hτ) (s+(a:ℂ))) z‖ ≤
        C*(1+|z.im|)^n := by
  let G : ℂ → ℂ := (spectralFiniteG χ τ hτ)
  have hd : Differentiable ℂ G := (spectralFiniteG_diff χ τ hτ)
  let g (s : ℂ) := G (s+(a:ℂ))
  have hgd : Differentiable ℂ g := hd.comp (differentiable_id.add_const _)
  obtain ⟨n,C,hC,hb⟩ := spectralBoundaryFinite_strip_growth χ τ hτ (W+|a|+1)
  refine ⟨n,C*2^n,by positivity,?_⟩
  intro z hz
  have hloc (u : ℂ) (hu : u ∈ sphere z 1) : ‖g u‖ ≤ (C*2^n)*(1+|z.im|)^n := by
    have hdist : ‖u-z‖ = 1 := mem_sphere_iff_norm.mp hu
    have hr : |(u+(a:ℂ)).re| ≤ W+|a|+1 := by
      simp only [Complex.add_re,Complex.ofReal_re]
      have hr := (Complex.abs_re_le_norm (u-z)).trans hdist.le
      change |u.re-z.re| ≤ 1 at hr
      have hx := (abs_le.mp ((abs_abs_sub_abs_le_abs_sub u.re z.re).trans hr)).2
      linarith [abs_add_le u.re a]
    have hi : 1+|(u+(a:ℂ)).im| ≤ 2*(1+|z.im|) := by
      simp only [Complex.add_im,Complex.ofReal_im,add_zero]
      have hr := (Complex.abs_im_le_norm (u-z)).trans hdist.le
      change |u.im-z.im| ≤ 1 at hr
      have hx := (abs_le.mp ((abs_abs_sub_abs_le_abs_sub u.im z.im).trans hr)).2
      linarith [abs_nonneg z.im]
    refine (hb _ hr).trans ?_
    rw [mul_assoc,mul_comm (2^n),←mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by simpa [mul_comm] using hi) _) hC.le
  simpa using Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hgd.diffContOnCl hloc

/-- Functional reflection transfers each retained jet to the entire finite generator
of the contragredient. The multiplication here is by a nowhere-zero entire epsilon factor. -/
private theorem spectralBoundaryFinite_reflected_retained_order (a : ℝ) (z : ℂ)
    (hz : 0 < analyticOrderAt ((Λr).val : ℂ → ℂ) z) :
    ((analyticOrderAt ((Λr).val : ℂ → ℂ) z).toNat : ℕ∞) ≤
      analyticOrderAt (fun s ↦ (spectralFiniteG χ⁻¹ τ hτ) (1-(s+(a:ℂ)))) (z - (a:ℂ)) := by
  let L := continuedCompletedHeckeL χ
  let Ld := continuedCompletedHeckeL χ⁻¹
  obtain ⟨hL,heL⟩ := continuedCompletedHeckeL_spec χ
  obtain ⟨hLd,heLd⟩ := continuedCompletedHeckeL_spec χ⁻¹
  obtain ⟨ε,hε,hnε,hfe⟩ := completedHeckeL_continuation_functionalEquation χ _ _ hL heL hLd heLd
  have hcomp : meromorphicOrderAt (fun s ↦ Ld (1-s)) z = meromorphicOrderAt Ld (1-z) := by
    simpa [Function.comp_def] using meromorphicOrderAt_comp_of_deriv_ne_zero (f := Ld)
      (show AnalyticAt ℂ (fun s : ℂ ↦ 1-s) z by fun_prop)
      (show deriv (fun s : ℂ ↦ 1-s) z ≠ 0 by simp)
  rw [show (fun s ↦ Ld (1-s)) = ε*L from funext hfe,meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt _) (hnε _)] at hcomp
  obtain ⟨k, hk, hreg, hord⟩ := spectralNuclearity_trace_zero_order χ τ hτ ⟨z,hz⟩
  change analyticOrderAt ((Λr).val : ℂ → ℂ) z = (k:ℕ∞) at hreg
  rw [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _)] at hord
  have hzord : meromorphicOrderAt L z = (k:ℤ) := by
    change (meromorphicOrderAt L z).untop₀ = (k:ℤ) at hord
    cases h : meromorphicOrderAt L z with
    | top => rw [h] at hord; simp at hord; omega
    | coe i => rw [h] at hord; simpa using congrArg (fun n : ℤ ↦ (n:WithTop ℤ)) hord
  have hfin := spectralFiniteG_order χ⁻¹ τ hτ (1-z)
  change meromorphicOrderAt Ld (1-z) ≤ _ at hfin
  rw [←hcomp,hzord,((spectralFiniteG_diff χ⁻¹ τ hτ).analyticAt _).meromorphicOrderAt_eq] at hfin
  have hshift : analyticOrderAt (fun s ↦ (spectralFiniteG χ⁻¹ τ hτ) (1-(s+(a:ℂ)))) (z-(a:ℂ)) =
      analyticOrderAt ((spectralFiniteG χ⁻¹ τ hτ):ℂ→ℂ) (1-z) := by
    rw [show (fun s ↦ (spectralFiniteG χ⁻¹ τ hτ) (1-(s+(a:ℂ)))) =
      ((spectralFiniteG χ⁻¹ τ hτ) : ℂ → ℂ) ∘ (fun s : ℂ ↦ 1-(s+(a:ℂ))) by rfl,
      analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp),sub_add_cancel]
  rw [hshift,hreg,ENat.toNat_natCast]
  cases hh : analyticOrderAt ((spectralFiniteG χ⁻¹ τ hτ):ℂ → ℂ) (1-z) with
  | top => exact le_top
  | coe n => rw [hh,ENat.map_natCast] at hfin; exact_mod_cast hfin

private theorem spectralBoundaryFinite_reflected_deriv (a W : ℝ) :
    ∃ n : ℕ, ∃ C > (0:ℝ), ∀ z : ℂ, |z.re| ≤ W →
      ‖deriv (fun s ↦ (spectralFiniteG χ⁻¹ τ hτ) (1-(s+(a:ℂ)))) z‖ ≤ C*(1+|z.im|)^n := by
  let g (s : ℂ) := (spectralFiniteG χ⁻¹ τ hτ) (s+((1-a:ℝ):ℂ))
  have hg : Differentiable ℂ g := (spectralFiniteG_diff χ⁻¹ τ hτ).comp (differentiable_id.add_const _)
  obtain ⟨n,C,hC,hb⟩ := spectralBoundaryFinite_shifted_deriv χ⁻¹ τ hτ (1-a) W
  refine ⟨n,C,hC,fun z hz ↦ ?_⟩
  have hn : ∀ s : ℂ, 1-(s+(a:ℂ)) = -s+((1-a:ℝ):ℂ) := by intro s; push_cast; ring
  simp only [hn]
  change ‖deriv (g ∘ fun s : ℂ ↦ -s) z‖ ≤ _
  have hdn : HasDerivAt (fun s : ℂ ↦ -s) (-1) z := (hasDerivAt_id z).neg
  have hdcomp := ((hg (-z)).hasDerivAt).comp z hdn
  rw [hdcomp.deriv]
  have he := hb (-z) (by simpa using hz)
  simpa [g] using he
local notation "domainSet" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "fp(" χ ")" => (ideleClassNormTwist χ 0)

/-- Absolute convergence at two gives a single upper bound on the entire closed
right half-plane. -/
private theorem spectralBoundaryFinite_euler_lower
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z : ℂ, 2 ≤ z.re →
      (ideleClassNormTwist χ 0).LSeries z ≠ 0 ∧ ‖((ideleClassNormTwist χ 0).LSeries z)⁻¹‖ ≤ C := by
  let r (v : HeightOneSpectrum (𝓞 F)) : ℝ := (v.asIdeal.absNorm : ℝ)^(-(2:ℝ))
  have hr : Summable r := (summable_absNorm_rpow F (by norm_num : (1:ℝ)<2)).comp_injective
    (fun _ _ he ↦ HeightOneSpectrum.ext he)
  have hr₀ (v) : 0 ≤ r v := Real.rpow_nonneg (Nat.cast_nonneg _) _
  let C := Real.exp (∑' v,r v)
  have hC : 1 ≤ C := Real.one_le_exp (tsum_nonneg hr₀)
  refine ⟨C,hC,fun z hz ↦ ?_⟩
  have hf (v : HeightOneSpectrum (𝓞 F)) : 1 ≤ Real.exp (r v) * ‖finiteHeckeEulerFactor χ v z‖ := by
    rw [finiteHeckeEulerFactor]
    split_ifs with hu
    · let q := (v.asIdeal.absNorm : ℝ)
      let b := (ideleClassNormTwist χ 0).localValue v * (q : ℂ)^(-z)
      have hq : 1 < q := by dsimp only [q]; exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
      have hw : ‖b‖ ≤ r v := by
        rw [show ‖b‖ = _ from norm_mul ..,norm_ideleClassNormTwist_zero_localValue χ v,
          one_mul,Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq),Complex.neg_re]
        exact Real.rpow_le_rpow_of_exponent_le hq.le (neg_le_neg hz)
      have hlt : r v < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by norm_num)
      have hne : 1-b ≠ 0 := sub_ne_zero.mpr (fun e ↦ by rw [←e,norm_one] at hw; linarith)
      change 1 ≤ Real.exp (r v) * ‖(1-b)⁻¹‖
      rw [norm_inv,←div_eq_mul_inv,one_le_div (norm_pos_iff.mpr hne)]
      exact (norm_sub_le _ _).trans ((by rw [norm_one]; linarith : ‖(1:ℂ)‖+‖b‖ ≤ 1+r v).trans
        (by simpa only [add_comm] using Real.add_one_le_exp (r v)))
    · simpa only [norm_one,mul_one] using Real.one_le_exp (hr₀ v)
  have raw : Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) ↦ ∏ v ∈ S, finiteHeckeEulerFactor χ v z)
      atTop (𝓝 ((ideleClassNormTwist χ 0).LSeries z)) := finiteHeckeL_hasProd χ ⟨z,show 1 < z.re by linarith⟩
  have hs : Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) ↦ ∏ v ∈ S, ‖finiteHeckeEulerFactor χ v z‖)
      atTop (𝓝 ‖(ideleClassNormTwist χ 0).LSeries z‖) := by simpa only [norm_prod] using raw.norm
  have hbound : 1 ≤ C * ‖(ideleClassNormTwist χ 0).LSeries z‖ := by
    apply ge_of_tendsto' (hs.const_mul C)
    intro S
    have hprod := Finset.one_le_prod₀ (s := S) (fun v _ ↦ hf v)
    rw [Finset.prod_mul_distrib,← Real.exp_sum] at hprod
    change 1 ≤ C * ∏ v ∈ S, ‖finiteHeckeEulerFactor χ v z‖
    exact hprod.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (hr.sum_le_tsum S (fun v _ ↦ hr₀ v)))
      (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _))
  have hne : (ideleClassNormTwist χ 0).LSeries z ≠ 0 := by intro e; norm_num [e] at hbound
  exact ⟨hne,by rw [norm_inv,inv_le_iff_one_le_mul₀ (norm_pos_iff.mpr hne)]; simpa only [mul_comm] using hbound⟩

/-- On the absolute-convergence half-plane the pole-clearing polynomial has modulus at least
one. The actual entire finite generator therefore has a uniformly bounded reciprocal there. -/
private theorem spectralBoundaryFinite_right_reciprocal (χ : domainSet) (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F)
    (hτ : RightInverse τ (ideleNorm F)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z : ℂ, 2 ≤ z.re →
      (spectralFiniteG χ τ hτ) z ≠ 0 ∧
        ‖((spectralFiniteG χ τ hτ) z)⁻¹‖ ≤ C := by
  classical
  obtain ⟨C,hC,he⟩ := spectralBoundaryFinite_euler_lower χ
  refine ⟨C,hC,fun z hz ↦ ?_⟩
  let t := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
  let b := (t:ℂ)*Complex.I
  let p := spectralFiniteP χ τ hτ z
  have h1 : 1≤‖z+b‖ := calc
    _ ≤ z.re := by linarith
    _ = (z+b).re := by simp [b,Complex.mul_re]
    _ ≤ _ := Complex.re_le_norm _
  have h2 : 1≤‖1-z-b‖ := calc
    _ ≤ -(1-z-b).re := by simp [b,Complex.mul_re]; linarith
    _ ≤ |(1-z-b).re| := neg_le_abs _
    _ ≤ _ := Complex.abs_re_le_norm _
  have hp : 1≤‖p‖ := by
    change 1≤‖(z+b)^(if _ then (1:ℕ) else 0)*(1-z-b)^(if _ then (1:ℕ) else 0)‖
    rw [norm_mul,norm_pow,norm_pow]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ h1) (one_le_pow₀ h2)
  have hval := spectralFiniteG_right χ τ hτ (show 1<z.re by linarith)
  change spectralFiniteG χ τ hτ z = p*(fp(χ)).LSeries z at hval
  rw [hval]
  obtain ⟨hn,hinv⟩ := he z hz
  refine ⟨mul_ne_zero (norm_pos_iff.mp (zero_lt_one.trans_le hp)) hn,?_⟩
  rw [mul_inv, norm_mul]
  exact (mul_le_of_le_one_left (by positivity) (by simpa using inv_le_one_of_one_le₀ hp)).trans hinv
/-- Both boundary kernels for the genuine quotient admit entire numerators, uniform
reciprocal bounds in unit neighborhoods of their respective integration lines, full
retained orders and polynomial derivative growth on every finite vertical strip. -/
private theorem spectralBoundaryFinite_boundary_arithmetic (a : ℝ) :
    let conditions (G : ℂ → ℂ) (σ : ℝ) :=
      Differentiable ℂ G ∧
      (∀ z : ℂ, 0 < analyticOrderAt ((Λr).val:ℂ → ℂ) z →
        ((analyticOrderAt ((Λr).val:ℂ → ℂ) z).toNat:ℕ∞) ≤ analyticOrderAt G (z-(a:ℂ))) ∧
      (∀ W : ℝ, ∃ n : ℕ, ∃ C > (0:ℝ), ∀ z : ℂ, |z.re| ≤ W → ‖deriv G z‖ ≤ C*(1+|z.im|)^n) ∧
      (∃ C ≥ (1:ℝ), ∀ z : ℂ, |z.re-σ| ≤ 1 → G z ≠ 0 ∧ ‖(G z)⁻¹‖ ≤ C)
    conditions (fun s ↦ (spectralFiniteG χ τ hτ) (s+(a:ℂ))) (3-a) ∧
    conditions (fun s ↦ (spectralFiniteG χ⁻¹ τ hτ) (1-(s+(a:ℂ)))) (-2-a) := by
  intro conditions
  constructor
  · refine ⟨(spectralFiniteG_diff χ τ hτ).comp (differentiable_id.add_const _),
      spectralBoundaryFinite_shifted_retained_order χ τ hτ a,spectralBoundaryFinite_shifted_deriv χ τ hτ a,?_⟩
    obtain ⟨C,hC,hb⟩ := spectralBoundaryFinite_right_reciprocal χ τ hτ
    refine ⟨C,hC,fun z hz ↦ hb _ ?_⟩
    simp only [Complex.add_re,Complex.ofReal_re]
    linarith [(abs_le.mp hz).1]
  · refine ⟨(spectralFiniteG_diff χ⁻¹ τ hτ).comp (show Differentiable ℂ (fun s : ℂ ↦ 1-(s+(a:ℂ))) by fun_prop),
      spectralBoundaryFinite_reflected_retained_order χ τ hτ a,spectralBoundaryFinite_reflected_deriv χ τ hτ a,?_⟩
    obtain ⟨C,hC,hb⟩ := spectralBoundaryFinite_right_reciprocal χ⁻¹ τ hτ
    refine ⟨C,hC,fun z hz ↦ hb _ ?_⟩
    simp only [Complex.sub_re,Complex.one_re,Complex.add_re,Complex.ofReal_re]
    linarith [(abs_le.mp hz).2]

end SpectralBoundaryArithmetic

open Classical in
/-- Paper: Theorem 7.4.1.1(2), p. 367. The remaining operator input is the
existence of a rapidly decreasing nuclear presentation of the retained-jet action. -/
private theorem spectralNuclearity_strong_of_jet_action (a : ℝ) (N : ℕ) (hN : 0 < N) (φ : 𝒟)
    (d : jets(χ, τ, hτ) → StrongDual ℂ (Q(a)))
    (hd : ∀ i f, d i ((D(a)).mkQ f) = iteratedDeriv i.2.val f.val (i.1.val - (a : ℂ))) :
    let K := ⨅ i : {i : jets(χ, τ, hτ) // i.2.val < N}, (d i.val).toLinearMap.ker
    let E := Q(a) ⧸ K
    letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    ∀ (A : B →L[ℂ] B) (Aq : Q(a) →L[ℂ] Q(a)) (T : E →L[ℂ] E),
      (∀ f s, (A f).val s = nuclearityTestMellin χ φ s * f.val s) →
      (∀ f, Aq ((D(a)).mkQ f) = (D(a)).mkQ (A f)) →
      (∀ x, T (K.mkQ x) = K.mkQ (Aq x)) →
      IsStronglyNuclearOperator T := by
  classical
  intro K E A Aq T hA hAq hT
  clear hN
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let D := D(a)
  let I := {i : jets(χ, τ, hτ) // i.2.val < N}
  have hD : IsClosed (D : Set B) := schwartzBergmanDivisible_isClosed _
  have hK : IsClosed (K : Set (Q(a))) := by
    change IsClosed (↑(⨅ i : I, (d i.val).toLinearMap.ker) : Set (Q(a)))
    rw [Submodule.coe_iInf]
    exact isClosed_iInter (fun i ↦ (d i.val).isClosed_ker)
  have hB := schwartzBergman_frechet univ isOpen_univ ordConnected_univ univ_nonempty
  have hQ := isFrechetTVS_quotient hB D hD
  obtain ⟨_, hp, hmet, hcomplete⟩ := isFrechetTVS_quotient hQ K hK
  let : PolynormableSpace ℂ E := hp
  let : TopologicalSpace.MetrizableSpace E := hmet
  let : CompleteSpace E := hcomplete
  let q : B →L[ℂ] E := K.mkQL.comp D.mkQL
  have hq : Topology.IsQuotientMap q := (Submodule.isQuotientMap_mkQ K).comp (Submodule.isQuotientMap_mkQ D)
  obtain ⟨p,hp'⟩ := spectralBoundary_countable_seminorms E
  let M := nuclearityTestMellin χ φ
  have hM : Differentiable ℂ M := differentiable_nuclearityTestMellin χ φ
  have decay (σ : ℝ) (k : ℕ) : ∃ C > (0:ℝ), ∀ w : ℂ, |w.re-σ| ≤ 1 → (1+|w.im|)^k*‖M w‖ ≤ C := by
    obtain ⟨C,hC,h⟩ := spectralBoundary_globalStrip hM.continuous
      (spectralNuclearity_trace_vertical_decay χ φ (σ-1) (σ+1) (by linarith)) k
    exact ⟨C,hC,fun w hw ↦ by rw [mul_comm]; exact h w ⟨by linarith [(abs_le.mp hw).1], by linarith [(abs_le.mp hw).2]⟩⟩
  let G₀ := fun s : ℂ ↦ (spectralFiniteG χ τ hτ) (s+(a:ℂ))
  let G₁ := fun s : ℂ ↦ (spectralFiniteG χ⁻¹ τ hτ) (1-(s+(a:ℂ)))
  obtain ⟨⟨hg₀,ho₀,hd₀,hi₀⟩,hg₁,ho₁,hd₁,hi₁⟩ := spectralBoundaryFinite_boundary_arithmetic χ τ hτ a
  obtain ⟨b₀,R₀,h₀,r₀,hr₀⟩ := spectralBoundary_line_factorization p hp' q (G := G₀) hg₀ hM (3-a) hd₀ hi₀ (decay _)
  obtain ⟨b₁,R₁,h₁,r₁,hr₁⟩ := spectralBoundary_line_factorization p hp' q (G := G₁) hg₁ hM (-2-a) hd₁ hi₁ (decay _)
  let α : ℂ := (2*(Real.pi:ℂ))⁻¹
  apply spectralBoundary_two_sided_descent q hq T b₀ b₁ (q.comp R₀) (q.comp R₁) α (-α) r₀ r₁ hr₀ hr₁
  intro x
  change α • q (R₀ (b₀ x)) + (-α) • q (R₁ (b₁ x)) = T (K.mkQ (D.mkQ x))
  rw [hT,hAq]
  change α • q (R₀ (b₀ x)) + (-α) • q (R₁ (b₁ x)) = q (A x)
  let X := α • R₀ (b₀ x) + (-α) • R₁ (b₁ x) - A x
  suffices hx : q X = 0 by simpa only [X,map_sub,map_add,map_smul,sub_eq_zero] using hx
  change K.mkQ (D.mkQ X) = 0
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,Submodule.mem_iInf]
  intro i
  change d i.val (D.mkQ X) = 0
  rw [hd]
  let z := i.val.1
  obtain ⟨k,hk,_,hdiv⟩ := spectralNuclearity_trace_zero_order χ τ hτ z
  have strip := spectralNuclearity_trace_zero_strip χ (z := z.val) (by rw [hdiv]; exact_mod_cast hk)
  have hs : (z.val-(a:ℂ)).re ∈ Ioo (-2-a) (3-a) := by
    simp only [Complex.sub_re,Complex.ofReal_re,mem_Ioo]
    exact ⟨by linarith [strip.1],by linarith [strip.2]⟩
  have hi (G : ℂ → ℂ) (s : ℝ) (h : ∃ C ≥ (1:ℝ), ∀ w : ℂ, |w.re-s| ≤ 1 → G w ≠ 0 ∧ ‖(G w)⁻¹‖ ≤ C) :
      ∃ C ≥ (1:ℝ), ∀ t : ℝ, G ((s:ℂ)+t*Complex.I) ≠ 0 ∧ ‖(G ((s:ℂ)+t*Complex.I))⁻¹‖ ≤ C := by
    obtain ⟨C,hC,h⟩ := h
    exact ⟨C,hC,fun t ↦ h _ (by simp)⟩
  apply spectralBoundary_signed_jets (-2-a) (3-a) G₀ G₁ (A x) (R₀ (b₀ x)) (R₁ (b₁ x))
    (z.val-(a:ℂ)) hs (multiplicity(χ,τ,hτ,z)) hg₀ hg₁ (hi _ _ hi₀) (hi _ _ hi₁)
    (ho₀ z.val z.property) (ho₁ z.val z.property) _ _ i.val.2.val i.val.2.isLt
  · intro w
    simpa only [hA,M] using h₀ x w
  · intro w
    simpa only [hA,M] using h₁ x w

open Classical in
/-- Paper: Theorem 7.4.1.1(2), pp. 366–367. One rapidly decreasing presentation
of the descended operator whose scalar series sums to the explicit zero formula. -/
private theorem spectralNuclearity_trace_presentation (a : ℝ) (N : ℕ) (hN : 0 < N) (φ : 𝒟)
    (d : jets(χ, τ, hτ) → StrongDual ℂ (Q(a)))
    (hd : ∀ i f, d i ((D(a)).mkQ f) = iteratedDeriv i.2.val f.val (i.1.val - (a : ℂ))) :
    let K := ⨅ i : {i : jets(χ, τ, hτ) // i.2.val < N}, (d i.val).toLinearMap.ker
    let E := Q(a) ⧸ K
    letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    let term := fun z : zeros(χ, τ, hτ) ↦
      ((min N (multiplicity(χ, τ, hτ, z)) : ℕ) : ℂ) * nuclearityTestMellin χ φ (z.val - (a : ℂ))
    ∀ (A : B →L[ℂ] B) (Aq : Q(a) →L[ℂ] Q(a)) (T : E →L[ℂ] E),
      (∀ f s, (A f).val s = nuclearityTestMellin χ φ s * f.val s) →
      (∀ f, Aq ((D(a)).mkQ f) = (D(a)).mkQ (A f)) →
      (∀ x, T (K.mkQ x) = K.mkQ (Aq x)) →
      ∃ r : NuclearPresentation T, (∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
        ‖r.coeff n‖ * ((n : ℝ) + 1)^k ≤ C) ∧
        HasSum (fun n ↦ r.coeff n * r.functional n (r.vector n).val) (∑' z, term z) := by
  intro K E term A Aq T hA hAq hT
  obtain ⟨r, hr⟩ := spectralNuclearity_strong_of_jet_action χ τ hτ a N hN φ d hd A Aq T hA hAq hT
  exact ⟨r, hr, spectralNuclearity_trace_of_rapid_presentation χ τ hτ a N φ d hd A Aq T hA hAq hT r hr⟩

open Classical in
/-- Paper: Theorem 7.4.1.1(2), pp. 366–367. The Mellin action on the quotient
by the first `N` jets is strongly nuclear, and every nuclear presentation has the
trace determined by its jet blocks. -/
theorem spectralNuclearity_trace_of_jet_action (a : ℝ) (N : ℕ) (hN : 0 < N) (φ : 𝒟)
    (d : jets(χ, τ, hτ) → StrongDual ℂ (Q(a)))
    (hd : ∀ i f, d i ((D(a)).mkQ f) = iteratedDeriv i.2.val f.val (i.1.val - (a : ℂ))) :
    let K := ⨅ i : {i : jets(χ, τ, hτ) // i.2.val < N}, (d i.val).toLinearMap.ker
    let E := Q(a) ⧸ K
    letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    let term := fun z : zeros(χ, τ, hτ) ↦
      ((min N (multiplicity(χ, τ, hτ, z)) : ℕ) : ℂ) * nuclearityTestMellin χ φ (z.val - (a : ℂ))
    ∀ (A : B →L[ℂ] B) (Aq : Q(a) →L[ℂ] Q(a)) (T : E →L[ℂ] E),
      (∀ f s, (A f).val s = nuclearityTestMellin χ φ s * f.val s) →
      (∀ f, Aq ((D(a)).mkQ f) = (D(a)).mkQ (A f)) →
      (∀ x, T (K.mkQ x) = K.mkQ (Aq x)) →
      IsStronglyNuclearOperator T ∧ ∀ r : NuclearPresentation T,
        HasSum (fun n ↦ r.coeff n * r.functional n (r.vector n).val) (∑' z, term z) := by
  intro K E term A Aq T hA hAq hT
  obtain ⟨r, hfast, htrace⟩ :=
    spectralNuclearity_trace_presentation χ τ hτ a N hN φ d hd A Aq T hA hAq hT
  refine ⟨⟨r, hfast⟩, ?_⟩
  obtain ⟨v, hv, _⟩ := spectralJet_unique_presentation_sum χ τ hτ a N d T ⟨r⟩
  have he := (hv r).2.unique htrace
  intro t
  exact he ▸ (hv t).2

open Classical in
/-- Paper: Theorem 7.4.1.1(2), pp. 366–367.
Compactly supported tests act on the quotient determined by the first N derivatives
in each block. Every nuclear presentation of the order-zero action has the stated trace.
Deviation: The printed span of the first N primal vectors can fail to be invariant.
Quotient by the common kernel of the retained derivative functionals. The multiplier
is evaluated at z − a for each unshifted zero z. -/
theorem spectralNuclearity_trace (a : ℝ) (N : ℕ) (_hN : 0 < N) (φ : 𝒟)
    (d : jets(χ, τ, hτ) → StrongDual ℂ (Q(a)))
    (_hd : ∀ i f, d i ((D(a)).mkQ f) = iteratedDeriv i.2.val f.val (i.1.val - (a : ℂ))) :
    let K := ⨅ i : {i : jets(χ, τ, hτ) // i.2.val < N}, (d i.val).toLinearMap.ker
    let E := Q(a) ⧸ K
    letI instSpectralUniformSec4 : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    let term := fun z : zeros(χ, τ, hτ) ↦
      ((min N (multiplicity(χ, τ, hτ, z)) : ℕ) : ℂ) * nuclearityTestMellin χ φ (z.val - (a : ℂ))
    ∃ (A : B →L[ℂ] B) (T : E →L[ℂ] E),
      (∀ f s, (A f).val s = nuclearityTestMellin χ φ s * f.val s) ∧
      (∃ Aq : Q(a) →L[ℂ] Q(a),
        (∀ f, Aq ((D(a)).mkQ f) = (D(a)).mkQ (A f)) ∧
        ∀ x : Q(a), T (K.mkQ x) = K.mkQ (Aq x)) ∧
      IsStronglyNuclearOperator T ∧ Summable (fun z ↦ ‖term z‖) ∧
      ∀ r : NuclearPresentation T,
        HasSum (fun n ↦ r.coeff n * r.functional n (r.vector n).val) (∑' z, term z) := by
  intro K E term
  obtain ⟨A, hA, hD⟩ := (spectralNuclearityDenominator_closed_invariant χ τ hτ a φ).2
  obtain ⟨Aq, T, hAq, hT⟩ := spectralNuclearity_trace_descends χ τ hτ a N φ d _hd A hA hD
  obtain ⟨hnuclear, htrace⟩ :=
    spectralNuclearity_trace_of_jet_action χ τ hτ a N _hN φ d _hd A Aq T hA hAq hT
  exact ⟨A, T, hA, ⟨Aq, hAq, hT⟩, hnuclear,
    spectralNuclearity_trace_term_summable χ τ hτ a N φ, htrace⟩

end Spectral

section Orbital

variable (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
  (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))

/-- A quotient map followed by a closed embedding gives the same closed embedding on the kernel quotient. -/
private theorem exists_polarThetaNuclearityAction_closedEmbedding_of_factor
    {X Y Target : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup Target] [Module ℂ Target] [TopologicalSpace Target]
    (N : Submodule ℂ X) (q : X →L[ℂ] Y) (hq : IsQuotientMap q)
    (hqker : q.ker = N) (j : Y →L[ℂ] Target) (hj : IsClosedEmbedding j)
    (Z : (X ⧸ N) →L[ℂ] Target) (hZ : ∀ x, Z (N.mkQ x) = j (q x)) :
    IsClosedEmbedding Z := by
  obtain ⟨e, he⟩ := exists_quotient_equiv_of_kernel q hq N hqker
  have heq : (Z : (X ⧸ N) → Target) = j ∘ e := by
    funext x
    obtain ⟨u, rfl⟩ := N.mkQ_surjective x
    exact (hZ u).trans (congrArg j (he u).symm)
  rw [heq]
  exact hj.comp e.toHomeomorph.isClosedEmbedding

/-- An open map onto a closed linear range identifies its kernel quotient with that range. -/
private theorem exists_polarThetaNuclearityAction_closedEmbedding_of_range
    {X Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (N : Submodule ℂ X) (T : X →L[ℂ] Y)
    (ho : IsOpenMap T.rangeRestrict) (hc : IsClosed (Set.range T))
    (hk : T.ker = N) (Z : (X ⧸ N) →L[ℂ] Y)
    (hZ : ∀ x, Z (N.mkQ x) = T x) : IsClosedEmbedding Z := by
  have hq : IsQuotientMap T.rangeRestrict :=
    ho.isQuotientMap T.rangeRestrict.continuous T.toLinearMap.surjective_rangeRestrict
  have hker : T.rangeRestrict.ker = N := by
    rw [← hk]
    ext x
    change T.rangeRestrict x = 0 ↔ T x = 0
    rw [Subtype.ext_iff]
    rfl
  exact exists_polarThetaNuclearityAction_closedEmbedding_of_factor N T.rangeRestrict hq
    hker T.range.subtypeL hc.isClosedEmbedding_subtypeVal Z hZ

/-- The polar theta Mellin map is a closed embedding on every norm-one component. -/
private theorem exists_polarThetaNuclearityAction_mellin_closedEmbedding
    (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F)) :
    IsClosedEmbedding (exists_globalPolarThetaMellin χ τ hτ).choose := by
  let ω : PontryaginDual (ideleClassNorm F).ker := χ.comp
    (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
      (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F)
  let P₀ := adelePolarSubspace F
  let θ := homogeneousAdelicThetaLinearMap F ω
  let N := (θ.domRestrict P₀).ker
  let Z := (exists_globalPolarThetaMellin χ τ hτ).choose
  have hZ (f : P₀) (s : ℂ) : (Z (N.mkQ f)).val s =
      globalIdelicZFunction f.val (ideleClassNormTwist χ s) :=
    ((exists_globalPolarThetaMellin χ τ hτ).choose_spec f s).2
  by_cases hω : ω = 1
  · obtain ⟨t, ht, _⟩ := globalConverse_existsUnique_normTwist χ hω
    obtain ⟨T, ho, hc, hT, _, hk⟩ := globalConverse_normTwist χ t ht
    have hker : T.ker = N := by
      rw [hk]
      dsimp only [N, θ]
      rw [hω]
      rfl
    apply exists_polarThetaNuclearityAction_closedEmbedding_of_range N T ho hc hker Z
    intro f
    exact Subtype.ext (funext fun s ↦ (hZ f s).trans (hT f s).symm)
  · obtain ⟨j, hj, hje, _⟩ := globalConverse_nontrivial χ hω
    let q : P₀ →L[ℂ] (SchwartzBruhat (Multiplicative 𝔸[F]) ⧸ θ.ker) :=
      θ.ker.mkQL.comp P₀.subtypeL
    have hq : IsQuotientMap q := (globalConverse_nontrivial_exact ω hω).isQuotientMap
    have hqker : q.ker = N := by
      ext f
      change θ.ker.mkQ f.val = 0 ↔ θ f.val = 0
      exact Submodule.Quotient.mk_eq_zero θ.ker
    apply exists_polarThetaNuclearityAction_closedEmbedding_of_factor N q hq hqker j hj Z
    intro f
    exact Subtype.ext (funext fun s ↦ (hZ f s).trans (hje f.val s).symm)

/-- A continuous endomorphism preserving the range of a topological linear
embedding transports to a continuous endomorphism of its source. -/
private theorem exists_polarThetaNuclearityAction_conjugate
    {X Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (Z : X →L[ℂ] Y) (hZ : IsEmbedding Z) (T : Y →L[ℂ] Y)
    (hT : Set.MapsTo T (Set.range Z) (Set.range Z)) :
    ∃ A : X →L[ℂ] X, ∀ x, Z (A x) = T (Z x) := by
  let e₀ := LinearEquiv.ofInjective Z.toLinearMap hZ.injective
  have he₀ (y : Z.range) : Z (e₀.symm y) = y.val :=
    congrArg Subtype.val (e₀.apply_symm_apply y)
  let e : X ≃L[ℂ] Z.range :=
    { e₀ with
      continuous_toFun := Z.rangeRestrict.continuous
      continuous_invFun := hZ.continuous_iff.mpr
        (show Continuous (Z ∘ e₀.symm) from
          continuous_subtype_val.congr fun y ↦ (he₀ y).symm) }
  let R : Z.range →L[ℂ] Z.range :=
    (T.comp Z.range.subtypeL).codRestrict Z.range (fun y ↦ hT y.property)
  let A := e.symm.toContinuousLinearMap.comp (R.comp e.toContinuousLinearMap)
  exact ⟨A, fun x ↦ he₀ (R (e x))⟩


/-- Continuous integrable functions are determined pointwise by their Fourier transforms. -/
private theorem exists_polarThetaNuclearityAction_eq_of_fourier_eq
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (f g : G → ℂ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hfc : Continuous f) (hgc : Continuous g)
    (he : ∀ ψ : PontryaginDual G, lcaFourier μ f ψ = lcaFourier μ g ψ) : f = g := by
  obtain ⟨Φ, hΦ, hinj, -⟩ := lcaFourier_L1 (G := G) μ
  have hcoe (w : G → ℂ) (hw : Integrable w μ) (ψ : PontryaginDual G) :
      Φ (hw.toL1 w) ψ = lcaFourier μ w ψ := by
    rw [hΦ]
    exact integral_congr_ae (hw.coeFn_toL1.mono fun y hy ↦
      congrArg (· * star (ψ y : ℂ)) hy)
  have hL1 : hf.toL1 f = hg.toL1 g :=
    hinj (ZeroAtInftyContinuousMap.ext fun ψ ↦ by rw [hcoe, hcoe, he])
  exact (hfc.ae_eq_iff_eq μ hgc).mp ((Integrable.toL1_eq_toL1_iff f g hf hg).mp hL1)

/-- A Fourier coefficient vanishes when its character does not match the translation isotype. -/
private theorem exists_polarThetaNuclearityAction_fourier_zero_off_isotype
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (K : Subgroup G) (ω : PontryaginDual K) (f : G → ℂ)
    (hh : ∀ h : K, ∀ x, f (h.val⁻¹ * x) = (ω h : ℂ) * f x)
    (ψ : PontryaginDual G) (h : K) (hne : star (ψ h.val : ℂ) ≠ (ω h : ℂ)) :
    lcaFourier μ f ψ = 0 := by
  have htrans : lcaFourier μ (fun x ↦ f (h.val⁻¹ * x)) ψ =
      star (ψ h.val : ℂ) * lcaFourier μ f ψ := by
    unfold lcaFourier
    rw [← integral_mul_left_eq_self (μ := μ)
      (fun x ↦ f (h.val⁻¹ * x) * star (ψ x : ℂ)) h.val, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      simp only [inv_mul_cancel_left, map_mul, Circle.coe_mul, star_mul]
      ring
  have hiso : lcaFourier μ (fun x ↦ f (h.val⁻¹ * x)) ψ =
      (ω h : ℂ) * lcaFourier μ f ψ := by
    unfold lcaFourier
    simp_rw [hh h, mul_assoc]
    exact integral_const_mul _ _
  have he : ((ω h : ℂ) - star (ψ h.val : ℂ)) * lcaFourier μ f ψ = 0 := by
    rw [sub_mul, sub_eq_zero]
    exact hiso.symm.trans htrans
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hne.symm)

/-- For functions of one isotype, it suffices to compare the Fourier transforms on that component. -/
private theorem exists_polarThetaNuclearityAction_eq_convolution_of_component_fourier
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (K : Subgroup G) (ω : PontryaginDual K) (φ f g : G → ℂ)
    (hφ : Integrable φ μ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hgc : Continuous g) (hcc : Continuous (lcaConvolution μ φ f))
    (hfh : ∀ h : K, ∀ x, f (h.val⁻¹ * x) = (ω h : ℂ) * f x)
    (hgh : ∀ h : K, ∀ x, g (h.val⁻¹ * x) = (ω h : ℂ) * g x)
    (hformula : ∀ ψ : PontryaginDual G,
      (∀ h : K, star (ψ h.val : ℂ) = (ω h : ℂ)) →
      lcaFourier μ g ψ = lcaFourier μ φ ψ * lcaFourier μ f ψ) :
    g = lcaConvolution μ φ f := by
  apply exists_polarThetaNuclearityAction_eq_of_fourier_eq μ g (lcaConvolution μ φ f) hg
    (lcaConvolution_integrable μ hφ hf).2.1 hgc hcc
  intro ψ
  rw [lcaFourier_convolution μ hφ hf, Pi.mul_apply]
  by_cases hh : ∀ h : K, star (ψ h.val : ℂ) = (ω h : ℂ)
  · exact hformula ψ hh
  · obtain ⟨h, hne⟩ := not_forall.mp hh
    rw [exists_polarThetaNuclearityAction_fourier_zero_off_isotype μ K ω g hgh ψ h hne,
      exists_polarThetaNuclearityAction_fourier_zero_off_isotype μ K ω f hfh ψ h hne, mul_zero]

/-- Convolving a continuous function with a continuous compactly supported test is continuous. -/
private theorem exists_polarThetaNuclearityAction_convolution_continuous
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (φ f : G → ℂ) (hφ : Continuous φ) (hf : Continuous f)
    (hφc : HasCompactSupport φ) : Continuous (lcaConvolution μ φ f) := by
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (μ := μ) (k := tsupport φ) hφc
  · exact ((hφ.comp continuous_snd).mul
      (hf.comp ((continuous_snd.inv).mul continuous_fst))).continuousOn
  · intro x y _ hy
    simp [image_eq_zero_of_notMem_tsupport hy]


/-- The Fourier characters of a fixed component are norm twists of the chosen unitary character. -/
private theorem exists_polarThetaNuclearityAction_character_component
    {F : Type*} [Field F] [NumberField F]
    (χ ψ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (hψ : ∀ h : (ideleClassNorm F).ker, star (ψ h.val : ℂ) = (χ h.val : ℂ)) :
    ∃ s : ℂ, s.re = 2 ∧ ∀ x : IdeleClassGroup (𝓞 F) F,
      ((((ideleClassNorm F x : ℝ≥0) : ℝ) : ℂ) ^ (2 : ℕ)) * star (ψ x : ℂ) =
        ideleClassNormTwist χ s x := by
  let η : PontryaginDual (IdeleClassGroup (𝓞 F) F) := ψ⁻¹ * χ⁻¹
  have hη : η.comp
      (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
        (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F) = 1 := by
    apply PontryaginDual.ext
    intro h
    change (ψ h.val)⁻¹ * (χ h.val)⁻¹ = 1
    have hh : (ψ h.val)⁻¹ = χ h.val := by
      apply Circle.ext
      rw [Circle.coe_inv_eq_conj, ← Complex.star_def]
      exact hψ h
    rw [hh, mul_inv_cancel]
  obtain ⟨t, ht, -⟩ := globalConverse_existsUnique_normTwist η hη
  have hval (ξ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (z : ℂ)
      (x : IdeleClassGroup (𝓞 F) F) : ideleClassNormTwist ξ z x =
      (ξ x : ℂ) * ((((ideleClassNorm F x : ℝ≥0) : ℝ) : ℂ) ^ z) := rfl
  have hchar (x : IdeleClassGroup (𝓞 F) F) : star (ψ x : ℂ) =
      (χ x : ℂ) * ((((ideleClassNorm F x : ℝ≥0) : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) := by
    have hx := DFunLike.congr_fun ht x
    rw [hval, hval, Complex.cpow_zero, mul_one, PontryaginDual.one_apply,
      Circle.coe_one, one_mul] at hx
    change (((ψ x)⁻¹ * (χ x)⁻¹ : Circle) : ℂ) = _ at hx
    rw [Circle.coe_mul, Circle.coe_inv_eq_conj (ψ x), ← Complex.star_def,
      Circle.coe_inv] at hx
    have hh := congrArg (fun z : ℂ ↦ z * (χ x : ℂ)) hx
    simp only [mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero (χ x)), mul_one] at hh
    exact hh.trans (mul_comm _ _)
  refine ⟨2 + (t : ℂ) * Complex.I, by simp, fun x ↦ ?_⟩
  have hn : ((((ideleClassNorm F x : ℝ≥0) : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (ideleClassNorm F x).ne_zero)
  rw [hval, Complex.cpow_add _ _ hn, Complex.cpow_ofNat, hchar]
  ring


/-- Multiplicative weights commute with convolution. -/
private theorem exists_polarThetaNuclearityAction_weight_convolution
    {G : Type*} [CommGroup G] [MeasurableSpace G] (μ : Measure G)
    (c : G →* ℂ) (φ f : G → ℂ) (x : G) :
    lcaConvolution μ (fun y ↦ c y * φ y) (fun y ↦ c y * f y) x =
      c x * lcaConvolution μ φ f x := by
  unfold lcaConvolution
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  have hc : c y * c (y⁻¹ * x) = c x := by
    rw [← map_mul, mul_inv_cancel_left]
  calc
    (c y * φ y) * (c (y⁻¹ * x) * f (y⁻¹ * x)) =
        (c y * c (y⁻¹ * x)) * (φ y * f (y⁻¹ * x)) := by ring
    _ = c x * (φ y * f (y⁻¹ * x)) := by rw [hc]

/-- The squared norm weight makes a homogeneous theta function integrable on the full class group. -/
private theorem exists_polarThetaNuclearityAction_weighted_integrable
    (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (f : SchwartzBruhat (Multiplicative 𝔸[F])) :
    let ω : PontryaginDual (ideleClassNorm F).ker := χ.comp
      (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
        (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F)
    Integrable (fun x ↦ ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 2 x *
      homogeneousAdelicTheta ω f x) (ideleClassTamagawaMeasure F) := by
  intro ω
  let : BorelSpace (IdeleClassGroup (𝓞 F) F) := ⟨rfl⟩
  let c := ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (2 : ℂ)
  have h := (homogeneousTheta_classMellin_eq_mass_mul χ f ⟨2, by norm_num⟩).1
  have he (x : IdeleClassGroup (𝓞 F) F) :
      homogeneousAdelicTheta ω f x * ideleClassNormTwist χ 2 x =
        (χ x : ℂ) * (c x * homogeneousAdelicTheta ω f x) := by
    change homogeneousAdelicTheta ω f x * ((χ x : ℂ) *
        ((((ideleClassNorm F x).val : ℝ) : ℂ) ^ (2 : ℂ))) =
      (χ x : ℂ) * ((1 * ((((ideleClassNorm F x).val : ℝ) : ℂ) ^ (2 : ℂ))) *
        homogeneousAdelicTheta ω f x)
    ring
  apply h.mono ((c.continuous.mul (homogeneousAdelicTheta_continuous ω f)).aestronglyMeasurable)
  filter_upwards with x
  change ‖c x * homogeneousAdelicTheta ω f x‖ ≤
    ‖homogeneousAdelicTheta ω f x * ideleClassNormTwist χ 2 x‖
  simp only [he, norm_mul, Circle.norm_coe, one_mul, le_refl]


/-- A compactly supported Bruhat test is continuous, by its zero twist in the decay space. -/
private theorem exists_polarThetaNuclearityAction_test_continuous
    (F : Type*) [Field F] [NumberField F]
    (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F)) : Continuous φ.val := by
  let m : IdeleClassGroup (𝓞 F) F →ₜ* ℝ≥0ˣ :=
    ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
  have hm : IsModulation m := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hms : Surjective m := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
  let d := bruhatCompactSupportToModulatedExponentialDecay m univ hm hms φ
  let f := modulatedExponentialDecayTwist m univ ⟨0, mem_univ (0 : ℝ)⟩ d
  have he : (f : IdeleClassGroup (𝓞 F) F → ℂ) = φ.val := modulationWeight_zero m φ.val
  exact (schwartzBruhat_continuous f).congr (congrFun he)

/-- Mellin multiplication identifies the theta representative of the transported operator with Haar convolution. -/
private theorem exists_polarThetaNuclearityAction_convolution_graph
    (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F))
    (f g : adelePolarSubspace F)
    (hM : ∀ s : ℂ,
      globalIdelicZFunction g.val (ideleClassNormTwist χ s) =
        nuclearityTestMellin χ φ s * globalIdelicZFunction f.val (ideleClassNormTwist χ s)) :
    (homogeneousAdelicTheta
      (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
        (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F)) g.val :
      IdeleClassGroup (𝓞 F) F → ℂ) =
    lcaConvolution (ideleClassTamagawaMeasure F) φ.val (homogeneousAdelicTheta
      (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
        (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F)) f.val) := by
  let G := IdeleClassGroup (𝓞 F) F
  let μ := ideleClassTamagawaMeasure F
  let K := (ideleClassNorm F).ker
  let ω : PontryaginDual (ideleClassNorm F).ker := χ.comp (⟨K.subtype, continuous_subtype_val⟩ : K →ₜ* G)
  let c := ideleClassNormTwist (1 : PontryaginDual G) (2 : ℂ)
  let Hf : G → ℂ := homogeneousAdelicTheta ω f.val
  let Hg : G → ℂ := homogeneousAdelicTheta ω g.val
  let weightedF : G → ℂ := fun x ↦ c x * Hf x
  let weightedG : G → ℂ := fun x ↦ c x * Hg x
  let Pφ : G → ℂ := fun x ↦ c x * φ.val x
  let mass : ℂ := ((normOneIdeleClassTamagawaMeasure F univ).toReal : ℂ)
  let : BorelSpace G := ⟨rfl⟩
  let : μ.IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  let : μ.Regular := (ideleClassTamagawaMeasure_isWeil F).2.1
  have hφc : Continuous φ.val := exists_polarThetaNuclearityAction_test_continuous F φ
  have hPc : Continuous Pφ := c.continuous.mul hφc
  have hPs : HasCompactSupport Pφ :=
    (show HasCompactSupport φ.val from φ.property.2).mul_left
  have hPi : Integrable Pφ μ := hPc.integrable_of_hasCompactSupport hPs
  have hUi : Integrable weightedF μ := exists_polarThetaNuclearityAction_weighted_integrable F χ f.val
  have hVi : Integrable weightedG μ := exists_polarThetaNuclearityAction_weighted_integrable F χ g.val
  have hUc : Continuous weightedF := c.continuous.mul (homogeneousAdelicTheta_continuous ω f.val)
  have hVc : Continuous weightedG := c.continuous.mul (homogeneousAdelicTheta_continuous ω g.val)
  have hcK (h : K) : c h.val = 1 := by
    change (1 : ℂ) * (((ideleClassNorm F h.val).val : ℂ) ^ (2 : ℂ)) = 1
    rw [MonoidHom.mem_ker.mp h.property]
    simp
  have hiso (u : SchwartzBruhat (Multiplicative 𝔸[F])) (h : K) (x : G) :
      c (h.val⁻¹ * x) * homogeneousAdelicTheta ω u (h.val⁻¹ * x) =
        (ω h : ℂ) * (c x * homogeneousAdelicTheta ω u x) := by
    rw [map_mul, map_inv, hcK, inv_one, one_mul]
    exact (congrArg (c x * ·) (homogeneousAdelicTheta_homogeneous ω u h x)).trans
      (mul_left_comm _ _ _)
  have hEq : weightedG = lcaConvolution μ Pφ weightedF := by
    apply exists_polarThetaNuclearityAction_eq_convolution_of_component_fourier μ K ω Pφ weightedF weightedG hPi hUi hVi hVc
      (exists_polarThetaNuclearityAction_convolution_continuous μ Pφ weightedF hPc hUc hPs)
      (hiso f.val) (hiso g.val)
    intro ψ hψ
    obtain ⟨s, hs, hcs₀⟩ := exists_polarThetaNuclearityAction_character_component χ ψ hψ
    have hcs (x : G) : c x * star (ψ x : ℂ) = ideleClassNormTwist χ s x := by
      change (1 * (((((ideleClassNorm F x).val : ℝ) : ℂ)) ^ (2 : ℂ))) *
        star (ψ x : ℂ) = _
      rw [one_mul, Complex.cpow_ofNat]
      exact hcs₀ x
    have hF (u : SchwartzBruhat (Multiplicative 𝔸[F])) :
        lcaFourier μ (fun x ↦ c x * homogeneousAdelicTheta ω u x) ψ =
          mass * globalIdelicZFunction u (ideleClassNormTwist χ s) := by
      apply (integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)).trans
        (homogeneousTheta_classMellin_eq_mass_mul χ u ⟨s, by change 1 < s.re; rw [hs]; norm_num⟩).2
      change (c x * homogeneousAdelicTheta ω u x) * star (ψ x : ℂ) =
        homogeneousAdelicTheta ω u x * ideleClassNormTwist χ s x
      rw [← hcs]
      ring
    have hP : lcaFourier μ Pφ ψ = nuclearityTestMellin χ φ s := by
      apply integral_congr_ae
      filter_upwards with x
      change (c x * φ.val x) * star (ψ x : ℂ) = φ.val x * ideleClassNormTwist χ s x
      rw [← hcs]
      ring
    rw [hF, hF, hP, hM]
    ring
  funext x
  have hh := congrFun hEq x
  have hh' : c x * Hg x = c x * lcaConvolution μ φ.val Hf x :=
    hh.trans (exists_polarThetaNuclearityAction_weight_convolution μ c.toMonoidHom φ.val Hf x)
  have hcne : c x ≠ 0 := by
    intro hz
    have hp : c x * c x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [hz, zero_mul] at hp
    exact zero_ne_one hp
  exact mul_left_cancel₀ hcne hh'


/-- A map on a quotient has the prescribed graph once it has that graph on representatives. -/
private theorem exists_polarThetaNuclearityAction_graph_iff
    {Test Q Y : Type*} (q : Test → Q) (H : Test → Y) (C : Y → Y) (A : Q → Q)
    (hq : Function.Surjective q) (hker : ∀ f g, q f = q g ↔ H f = H g)
    (hforward : ∀ f g, A (q f) = q g → H g = C (H f)) :
    ∀ f g, A (q f) = q g ↔ H g = C (H f) := by
  intro f g
  constructor
  · exact hforward f g
  · intro h
    obtain ⟨u, hu⟩ := hq (A (q f))
    have huH := hforward f u hu.symm
    exact hu.symm.trans ((hker u g).mpr (huH.trans h.symm))

/-- Classes modulo a linear kernel agree exactly when the linear images agree. -/
private theorem exists_polarThetaNuclearityAction_quotient_eq_iff
    {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (T : X →ₗ[ℂ] Y) (f g : X) :
    T.ker.mkQ f = T.ker.mkQ g ↔ T f = T g := by
  change (Submodule.Quotient.mk f : X ⧸ T.ker) = Submodule.Quotient.mk g ↔ _
  rw [Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, sub_eq_zero]

/-- The convolution identity on representatives gives the graph of the quotient action. -/
private theorem exists_polarThetaNuclearityAction_graph_of_mellin
    (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : Function.RightInverse τ (ideleNorm F))
    (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F)) :
    let ω : PontryaginDual (ideleClassNorm F).ker := χ.comp
      (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
        (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F)
    let P₀ := adelePolarSubspace F
    let T := (homogeneousAdelicThetaLinearMap F ω).domRestrict P₀
    let N := T.ker
    let Z := (exists_globalPolarThetaMellin χ τ hτ).choose
    ∀ A : (P₀ ⧸ N) →L[ℂ] (P₀ ⧸ N),
      (∀ x s, (Z (A x)).val s = nuclearityTestMellin χ φ s * (Z x).val s) →
      ∀ f g : P₀, A (N.mkQ f) = N.mkQ g ↔
        (homogeneousAdelicTheta ω g.val : IdeleClassGroup (𝓞 F) F → ℂ) =
          lcaConvolution (ideleClassTamagawaMeasure F) φ.val (homogeneousAdelicTheta ω f.val) := by
  intro ω P₀ T N Z A hA
  let H (f : P₀) : IdeleClassGroup (𝓞 F) F → ℂ := homogeneousAdelicTheta ω f.val
  have hZ (f : P₀) (s : ℂ) : (Z (N.mkQ f)).val s =
      globalIdelicZFunction f.val (ideleClassNormTwist χ s) :=
    ((exists_globalPolarThetaMellin χ τ hτ).choose_spec f s).2
  have hquot (f g : P₀) : N.mkQ f = N.mkQ g ↔ H f = H g := by
    rw [exists_polarThetaNuclearityAction_quotient_eq_iff T f g]
    constructor
    · intro h
      exact congrArg (fun k : C(IdeleClassGroup (𝓞 F) F, ℂ) ↦
        (k : IdeleClassGroup (𝓞 F) F → ℂ)) h
    · intro h
      exact ContinuousMap.ext (congrFun h)
  apply exists_polarThetaNuclearityAction_graph_iff N.mkQ H
    (fun h ↦ lcaConvolution (ideleClassTamagawaMeasure F) φ.val h) A N.mkQ_surjective hquot
  intro f g hfg
  apply exists_polarThetaNuclearityAction_convolution_graph F χ φ f g
  intro s
  calc
    globalIdelicZFunction g.val (ideleClassNormTwist χ s) = (Z (N.mkQ g)).val s :=
      (hZ g s).symm
    _ = (Z (A (N.mkQ f))).val s :=
      congrArg (fun x ↦ (Z x).val s) hfg.symm
    _ = nuclearityTestMellin χ φ s * (Z (N.mkQ f)).val s := hA (N.mkQ f) s
    _ = nuclearityTestMellin χ φ s *
        globalIdelicZFunction f.val (ideleClassNormTwist χ s) := by rw [hZ]

/-- Paper: Theorem 7.4.2.1(1)–(2), p. 367, and Theorem 7.4.3.2, pp. 372–373.
In global Mellin coordinates the regularized theta action is multiplication by
the transform of the test. The induced map on theta functions is Haar convolution. -/
theorem exists_polarThetaNuclearityAction (φ : 𝒟) :
    ∃ A : Θ₀(χ) →L[ℂ] Θ₀(χ),
      (∀ f s, ((Z(χ, τ, hτ)) (A f)).val s =
        nuclearityTestMellin χ φ s * ((Z(χ, τ, hτ)) f).val s) ∧
      ∀ f g : P, A mkΘ(χ, f) = mkΘ(χ, g) ↔
        (homogeneousAdelicTheta (ω(χ)) g.val : C𝔽 → ℂ) =
          lcaConvolution μ𝔽 φ.val (homogeneousAdelicTheta (ω(χ)) f.val) := by
  let Z := (exists_globalPolarThetaMellin χ τ hτ).choose
  obtain ⟨_, T, hT, hPres⟩ := spectralNuclearityDenominator_closed_invariant χ τ hτ 0 φ
  have hz := exists_polarThetaNuclearityAction_mellin_closedEmbedding F χ τ hτ
  have hPres' : Set.MapsTo T (Set.range Z) (Set.range Z) := by
    change Set.MapsTo T (Z.toLinearMap.range : Set (SchwartzBergman univ))
      (Z.toLinearMap.range : Set (SchwartzBergman univ))
    rw [← spectralNuclearityDenominator_zero χ τ hτ]
    exact hPres
  obtain ⟨A, hA⟩ := exists_polarThetaNuclearityAction_conjugate Z hz.isEmbedding T hPres'
  have hM : ∀ f s, (Z (A f)).val s = nuclearityTestMellin χ φ s * (Z f).val s :=
    fun f s ↦ (congrArg (fun b ↦ b.val s) (hA f)).trans (hT (Z f) s)
  exact ⟨A, hM, exists_polarThetaNuclearityAction_graph_of_mellin F χ τ hτ φ A hM⟩

local notation "Aθ(" φ ")" => (exists_polarThetaNuclearityAction χ τ hτ φ).choose

/-- Paper: Equation (7.4.0.2), p. 366.
The finite places of a number field lying above one rational prime form a finite set. -/
theorem finite_nuclearityPlacesAbove (p : HeightOneSpectrum (𝓞 ℚ)) :
    {v : V | v.under (𝓞 ℚ) = p}.Finite := by
  apply Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal)
    (hi := HeightOneSpectrum.asIdeal_injective.injOn)
  apply (IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 F)).subset
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal (show w.under (𝓞 ℚ) = p from hw).symm⟩⟩

local notation "Sₚ(" p ")" => (finite_nuclearityPlacesAbove (F := F) p).toFinset

/-- Paper: Equation (7.4.0.2), p. 366.
Principal value preserves the common kernel of the two global polar evaluations. -/
theorem nuclearityPrincipalValue_mem_polar (p : HeightOneSpectrum (𝓞 ℚ)) (f : P) :
    adelePrincipalValue F (Sₚ(p)) f.val ∈ P := by
  classical
  have hn : (Sₚ(p)).Nonempty := by
    have := p.isMaximal
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F) p.asIdeal
    let v : V := ⟨q, hq.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot q⟩
    exact ⟨v, (finite_nuclearityPlacesAbove p).mem_toFinset.mpr (HeightOneSpectrum.ext hqp.over.symm)⟩
  let E := SchwartzBruhat (Multiplicative 𝔸[F])
  let pv : E →L[ℂ] E :=
    ⟨adelePrincipalValue F (Sₚ(p)), (adelePrincipalValue_isClosedEmbedding (Sₚ(p))).continuous⟩
  let vals : E →L[ℂ] ℂ × ℂ := ⟨adelePolarValues, adelePolarValues_continuous⟩
  obtain ⟨y, hy⟩ := adelePolarValues_surjective (F := F) ((1, 1) : ℂ × ℂ)
  change vals y = (1, 1) at hy
  have hx : vals f.val = 0 := f.property
  -- Pullback by principal value preserves the eigenspace of each polar functional.
  have coord (L : ℂ × ℂ →L[ℂ] ℂ) (c : QuasiCharacter C𝔽)
      (hL : L.comp vals ∈ adelicEigendistributions c) (h1 : L (1, 1) = 1) :
      L (vals (pv f.val)) = 0 := by
    let l := L.comp vals
    have hk : l.comp pv ∈ adelicEigendistributions c := by
      intro u t
      have he := congrArg (fun q : GlobalAdelicThetaSpace F ↦ L (globalThetaPolarValues q))
        (globalThetaPrincipalValue_equivariant hn u t)
      exact he.trans (hL u (pv t))
    have hl : l ≠ 0 := by
      intro hz
      have hy' : l y = 1 := (congrArg L hy).trans h1
      rw [hz] at hy'
      exact zero_ne_one hy'
    have hdim := Module.rank_eq_one_iff_finrank_eq_one.mp (adelicEigendistributions_rank c)
    rw [eq_span_singleton_of_mem_of_finrank_eq_one hdim hL hl, Submodule.mem_span_singleton] at hk
    obtain ⟨a, ha⟩ := hk
    have he := congrArg (fun k : E →L[ℂ] ℂ ↦ k f.val) ha.symm
    change L (vals (pv f.val)) = a * L (vals f.val) at he
    simpa only [hx, map_zero, mul_zero] using he
  apply (mem_adelePolarSubspace _).2
  constructor
  · apply coord (ContinuousLinearMap.fst ℂ ℂ ℂ) 1 _ rfl
    intro u t
    change t (Multiplicative.ofAdd ((↑u⁻¹ : 𝔸[F]) * 0)) = 1 * t (Multiplicative.ofAdd 0)
    rw [mul_zero, one_mul]
  · apply coord (ContinuousLinearMap.snd ℂ ℂ ℂ) (ideleClassNormTwist (1 : U) 1) _ rfl
    intro u t
    have h := globalThetaPolarValues_snd_translate (QuotientGroup.mk u) (Submodule.Quotient.mk t)
    rw [(existsUnique_globalThetaAction (F := F)).exists.choose_spec.2 u t] at h
    change (adelePolarValues (schwartzBruhatUnitTranslate u t)).2 =
      ((1 : ℂ) * (((ideleNorm F u).val : ℝ) : ℂ) ^ (1 : ℂ)) * (adelePolarValues t).2
    rw [Complex.cpow_one, one_mul]
    exact h

/-- Paper: Equation (7.4.0.2), p. 366.
The finite-place denominator is the theta image of principal values of zero-moment
tests, with the principal value taken at all places above the rational prime. -/
def finiteNuclearityDenominator (p : HeightOneSpectrum (𝓞 ℚ)) : Submodule ℂ (Θ₀(χ)) :=
  Submodule.span ℂ (Set.range (fun f : P ↦
    (Submodule.Quotient.mk ⟨adelePrincipalValue F (Sₚ(p)) f.val,
      nuclearityPrincipalValue_mem_polar (F := F) p f⟩ : Θ₀(χ))))

/-- Paper: Equation (7.4.0.2), p. 366.
The finite orbital quotient is taken by the principal-value image.

This is a `def` with its own instances, not an `abbrev`, so that instance terms over it do
not spell out its definition (#5398). -/
def FiniteNuclearityQuotient (p : HeightOneSpectrum (𝓞 ℚ)) :=
  Θ₀(χ) ⧸ finiteNuclearityDenominator χ p

namespace FiniteNuclearityQuotient

instance instAddCommGroup (p : HeightOneSpectrum (𝓞 ℚ)) :
    AddCommGroup (FiniteNuclearityQuotient χ p) :=
  inferInstanceAs (AddCommGroup (Θ₀(χ) ⧸ finiteNuclearityDenominator χ p))

instance instModule (p : HeightOneSpectrum (𝓞 ℚ)) : Module ℂ (FiniteNuclearityQuotient χ p) :=
  inferInstanceAs (Module ℂ (Θ₀(χ) ⧸ finiteNuclearityDenominator χ p))

instance instTopologicalSpace (p : HeightOneSpectrum (𝓞 ℚ)) :
    TopologicalSpace (FiniteNuclearityQuotient χ p) :=
  inferInstanceAs (TopologicalSpace (Θ₀(χ) ⧸ finiteNuclearityDenominator χ p))

instance instIsTopologicalAddGroup (p : HeightOneSpectrum (𝓞 ℚ)) :
    IsTopologicalAddGroup (FiniteNuclearityQuotient χ p) :=
  inferInstanceAs (IsTopologicalAddGroup (Θ₀(χ) ⧸ finiteNuclearityDenominator χ p))

instance instContinuousSMul (p : HeightOneSpectrum (𝓞 ℚ)) :
    ContinuousSMul ℂ (FiniteNuclearityQuotient χ p) :=
  inferInstanceAs (ContinuousSMul ℂ (Θ₀(χ) ⧸ finiteNuclearityDenominator χ p))

end FiniteNuclearityQuotient

private theorem mkQ_span_range_eq_zero {E M : Type*} [AddCommGroup E] [AddCommGroup M]
    [Module ℂ E] [Module ℂ M] (L : E →ₗ[ℂ] M) (x : M) :
    (Submodule.span ℂ (Set.range L)).mkQ x = 0 ↔ ∃ y, x = L y := by
  have hle : Submodule.span ℂ (Set.range L) ≤ LinearMap.range L :=
    Submodule.span_le.mpr Set.Subset.rfl
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hle hx
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, hy⟩
    exact Submodule.subset_span ⟨y, hy.symm⟩

private theorem mkQ_principal_range_eq_zero {E : Type*} [AddCommGroup E] [Module ℂ E]
    (S : Submodule ℂ E) (Q : Submodule ℂ S) (A : E →ₗ[ℂ] E)
    (h : ∀ g : S, A g.val ∈ S) (f : S) :
    (Submodule.span ℂ (Set.range (fun g : S ↦
      (Submodule.Quotient.mk ⟨A g.val, h g⟩ : S ⧸ Q)))).mkQ
        (Submodule.Quotient.mk f) = 0 ↔
      ∃ g : S, (Submodule.Quotient.mk f : S ⧸ Q) = Submodule.Quotient.mk ⟨A g.val, h g⟩ :=
  mkQ_span_range_eq_zero (Q.mkQ.comp ((A.domRestrict S).codRestrict S h)) (Q.mkQ f)

/-- Paper: Equation (7.4.0.2), p. 366.
The class of a test is zero in the finite quotient exactly when its theta class
is represented by a principal value. -/
theorem finiteNuclearityQuotient_mk_eq_zero (p : HeightOneSpectrum (𝓞 ℚ)) (f : P) :
    (finiteNuclearityDenominator χ p).mkQ mkΘ(χ, f) = 0 ↔
      ∃ g : P, mkΘ(χ, f) =
        mkΘ(χ, ⟨adelePrincipalValue F (Sₚ(p)) g.val, nuclearityPrincipalValue_mem_polar (F := F) p g⟩) :=
  by
    unfold finiteNuclearityDenominator
    have hz := mkQ_principal_range_eq_zero P (Π(χ)) (adelePrincipalValue F (Sₚ(p)))
      (nuclearityPrincipalValue_mem_polar (F := F) p) f
    with_reducible exact hz

/-- The polar Mellin transform separates homogeneous theta classes by the two
global converse theorems, using their respective kernels. -/
private theorem finiteNuclearity_mellin_injective : Injective (Z(χ, τ, hτ)) := by
  apply LinearMap.ker_eq_bot.mp
  refine (Submodule.eq_bot_iff _).mpr fun x hx ↦ ?_
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (Π(χ)) x
  have hZ : (Z(χ, τ, hτ)) (mkΘ(χ, f)) = 0 := hx
  have hf (s : ℂ) : globalIdelicZFunction f.val (ideleClassNormTwist χ s) = 0 := by
    rw [← ((exists_globalPolarThetaMellin χ τ hτ).choose_spec f s).2, hZ]
    rfl
  apply (Submodule.Quotient.mk_eq_zero (Π(χ))).mpr
  by_cases hω : ω(χ) = 1
  · obtain ⟨t, ht⟩ := (globalConverse_existsUnique_normTwist χ hω).exists
    obtain ⟨M, _, _, hM, _, hker⟩ := globalConverse_normTwist χ t ht
    have hm : f ∈ M.ker := specDenom_B_ext (M f) 0 (fun s ↦ (hM f s).trans (hf s))
    have hK := congrArg (fun ψ ↦ (homogeneousAdelicThetaLinearMap F ψ).ker.comap (P).subtype) hω
    exact (hK.trans hker.symm).ge hm
  · obtain ⟨M, hM, hval, _⟩ := globalConverse_nontrivial χ hω
    let K := (homogeneousAdelicThetaLinearMap F (ω(χ))).ker
    have hfM : M (K.mkQ f.val) = 0 :=
      specDenom_B_ext _ 0 (fun s ↦ (hval f.val s).trans (hf s))
    change f.val ∈ K
    exact (Submodule.Quotient.mk_eq_zero K).mp (hM.injective (hfM.trans M.map_zero.symm))

local notation "orbitalGenerator(" S ")" => orbitalHeckeGenerator χ τ hτ
  (continuedCompletedHeckeL χ) (continuedCompletedHeckeL_spec χ).1
  (continuedCompletedHeckeL_spec χ).2 S

/-- A surjective choice of representatives carries a Mellin range equality
to a pointwise description on those representatives. -/
private theorem finiteNuclearity_values_of_range {X Y C : Type*} (q : X → Y)
    (hq : Surjective q) (M : Y → C) (ev : C → ℂ → ℂ) (g : ℂ → ℂ)
    (hM : Set.range M = {b | ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, ev b s = g s * u s})
    (hev : Injective ev) (val : X → ℂ → ℂ) (hval : ∀ x s, ev (M (q x)) s = val x s) (b : C) :
    (∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, ev b s = g s * u s) ↔
      ∃ x, ∀ s, ev b s = val x s := by
  have hr : b ∈ Set.range M ↔ ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, ev b s = g s * u s :=
    Set.ext_iff.mp hM b
  refine hr.symm.trans ?_
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := hq y
    exact ⟨x, hval x⟩
  · rintro ⟨x, hx⟩
    exact ⟨q x, hev (funext fun s ↦ (hval x s).trans (hx s).symm)⟩

open Classical in
private theorem finiteNuclearity_mellin_values_normTwist (S : Finset V) (b : B)
    (hω : ω(χ) = 1) :
    (∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, b.val s = (orbitalGenerator(S)).val s * u s) ↔
      ∃ f : P, ∀ s : ℂ, b.val s =
        globalIdelicZFunction (adelePrincipalValue F S f.val) (ideleClassNormTwist χ s) := by
  let L := fun s : ℂ ↦ (orbitalGenerator(S)).val s
  let ev := fun b : B ↦ b.val
  let val (f : P) (s : ℂ) :=
    globalIdelicZFunction (adelePrincipalValue F S f.val) (ideleClassNormTwist χ s)
  have hev : Injective ev := Subtype.val_injective
  change (∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, b.val s = L s * u s) ↔ ∃ f, ∀ s, ev b s = val f s
  obtain ⟨t, ht⟩ := (globalConverse_existsUnique_normTwist χ hω).exists
  obtain ⟨M, _, _, hM, hRange, _⟩ := globalPrincipalValueConverse_normTwist S χ t ht
  let W := (P).map (adelePrincipalValue F S)
  let q : P → W := fun f ↦ ⟨adelePrincipalValue F S f.val, Submodule.mem_map_of_mem f.property⟩
  have hq : Surjective q := by
    intro y
    obtain ⟨f, hf, hfy⟩ := y.property
    exact ⟨⟨f, hf⟩, Subtype.ext hfy⟩
  have hL : L = fun s ↦ reciprocalPartialHeckeEulerProduct χ S s *
      toMeromorphicNFOn (fun s ↦ ((s + (t : ℂ) * Complex.I) *
        (1 - s - (t : ℂ) * Complex.I)) * continuedCompletedHeckeL χ s) univ s := by
    funext s
    change reciprocalPartialHeckeEulerProduct χ S s *
      (regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
        (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2).val s = _
    rw [congrFun (specDenom_L1 χ τ hτ t hω ht) s]
  rw [hL]
  have heq (f : P) (s : ℂ) : (M (q f)).val s =
      globalIdelicZFunction (adelePrincipalValue F S f.val) (ideleClassNormTwist χ s) :=
    hM (q f) s
  with_reducible exact finiteNuclearity_values_of_range q hq M ev _ hRange hev val heq b

open Classical in
private theorem finiteNuclearity_mellin_values_nontrivial (S : Finset V) (b : B)
    (hω : ω(χ) ≠ 1) :
    (∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, b.val s = (orbitalGenerator(S)).val s * u s) ↔
      ∃ f : P, ∀ s : ℂ, b.val s =
        globalIdelicZFunction (adelePrincipalValue F S f.val) (ideleClassNormTwist χ s) := by
  let L := fun s : ℂ ↦ (orbitalGenerator(S)).val s
  let ev := fun b : B ↦ b.val
  let val (f : P) (s : ℂ) :=
    globalIdelicZFunction (adelePrincipalValue F S f.val) (ideleClassNormTwist χ s)
  have hev : Injective ev := Subtype.val_injective
  change (∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, b.val s = L s * u s) ↔ ∃ f, ∀ s, ev b s = val f s
  let K := (homogeneousAdelicThetaLinearMap F (ω(χ))).ker
  let A := K.mkQ.comp (adelePrincipalValue F S)
  let q : P → A.range := fun f ↦ A.rangeRestrict f.val
  obtain ⟨M, _, hM, hRange⟩ := globalPrincipalValueConverse_nontrivial S χ hω
  have hq : Surjective q := (globalPrincipalValueConverse_nontrivial_exact S (ω(χ)) hω).surjective
  have hL : L = fun s ↦ reciprocalPartialHeckeEulerProduct χ S s *
      continuedCompletedHeckeL χ s := by
    funext s
    change reciprocalPartialHeckeEulerProduct χ S s *
      (regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
        (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2).val s = _
    rw [congrFun (specDenom_L0 χ τ hτ (normOneRestrict_ne_one χ hω)) s]
  rw [hL]
  have heq (f : P) (s : ℂ) : (M (q f)).val s =
      globalIdelicZFunction (adelePrincipalValue F S f.val) (ideleClassNormTwist χ s) :=
    hM f.val s
  with_reducible exact finiteNuclearity_values_of_range q hq M ev _ hRange hev val heq b

open Classical in
/-- The polar principal-value image has precisely the Mellin transforms
divisible by the regularized completed function with the Euler factors removed. -/
private theorem finiteNuclearity_mellin_values (p : HeightOneSpectrum (𝓞 ℚ)) (b : B) :
    b ∈ schwartzBergmanDivisible (orbitalGenerator(Sₚ(p))) ↔
      ∃ f : P, ∀ s : ℂ, b.val s =
        globalIdelicZFunction (adelePrincipalValue F (Sₚ(p)) f.val) (ideleClassNormTwist χ s) := by
  refine (mem_schwartzBergmanDivisible_iff (orbitalGenerator(Sₚ(p))) b).trans ?_
  by_cases hω : ω(χ) = 1
  · exact finiteNuclearity_mellin_values_normTwist χ τ hτ (Sₚ(p)) b hω
  · exact finiteNuclearity_mellin_values_nontrivial χ τ hτ (Sₚ(p)) b hω

private theorem finiteNuclearity_mellin_mem (p : HeightOneSpectrum (𝓞 ℚ)) (x : Θ₀(χ)) :
    x ∈ finiteNuclearityDenominator χ p ↔
      (Z(χ, τ, hτ)) x ∈ schwartzBergmanDivisible (orbitalGenerator(Sₚ(p))) := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective (Π(χ)) x
  rw [← Submodule.Quotient.mk_eq_zero (finiteNuclearityDenominator χ p),
    ← Submodule.mkQ_apply, finiteNuclearityQuotient_mk_eq_zero,
    finiteNuclearity_mellin_values χ τ hτ p]
  refine exists_congr fun f ↦ ?_
  let fv : P := ⟨adelePrincipalValue F (Sₚ(p)) f.val, nuclearityPrincipalValue_mem_polar p f⟩
  have hv (s : ℂ) := ((exists_globalPolarThetaMellin χ τ hτ).choose_spec fv s).2
  exact ⟨fun h s ↦ (congrArg (fun y : Θ₀(χ) ↦ ((Z(χ, τ, hτ)) y).val s) h).trans (hv s),
    fun h ↦ finiteNuclearity_mellin_injective χ τ hτ
      (specDenom_B_ext _ _ fun s ↦ (h s).trans (hv s).symm)⟩

/-- Paper: Theorem 7.4.2.1(1), p. 367.
The finite-place denominator is closed and is stable under each regularized action. -/
theorem finiteNuclearityDenominator_closed_invariant (p : HeightOneSpectrum (𝓞 ℚ)) (φ : 𝒟) :
    let D := finiteNuclearityDenominator χ p
    IsClosed (D : Set (Θ₀(χ))) ∧ Set.MapsTo (Aθ(φ)) (D : Set (Θ₀(χ))) D := by
  let G := orbitalGenerator(Sₚ(p))
  constructor
  · rw [show (finiteNuclearityDenominator χ p : Set (Θ₀(χ))) =
      (Z(χ, τ, hτ)) ⁻¹' (schwartzBergmanDivisible G : Set B) from
        Set.ext (finiteNuclearity_mellin_mem χ τ hτ p)]
    exact (schwartzBergmanDivisible_isClosed G).preimage (Z(χ, τ, hτ)).continuous
  · intro x hx
    have hmem (y : Θ₀(χ)) := (finiteNuclearity_mellin_mem χ τ hτ p y).trans
      (mem_schwartzBergmanDivisible_iff G ((Z(χ, τ, hτ)) y))
    obtain ⟨u, hu, hv⟩ := (hmem x).mp hx
    refine (hmem _).mpr ⟨fun s ↦ nuclearityTestMellin χ φ s * u s, ?_, fun s ↦ ?_⟩
    · exact (differentiable_nuclearityTestMellin χ φ).mul hu
    · rw [(exists_polarThetaNuclearityAction χ τ hτ φ).choose_spec.1 x s, hv s]
      ring

-- TODO(paper-gap): The cited §7.1.4.3 concerns the entire comparison space.
-- To apply the rapid-decay argument on this quotient, one needs bounds in its
-- own topology for the functionals and the biorthogonal vectors.

/-- Paper: Theorem 7.4.2.1(2), p. 367.
The operator induced on the finite orbital quotient is of order zero. Its trace sums
the test Mellin transform over the zeros of the reciprocal partial Euler product,
counting collisions with their full order. -/
theorem finiteNuclearity_trace (p : HeightOneSpectrum (𝓞 ℚ)) (φ : 𝒟) :
    let D := finiteNuclearityDenominator χ p
    let Q := Θ₀(χ) ⧸ D
    letI instFiniteUniformSec4 : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
    let R := reciprocalPartialHeckeEulerProduct χ (Sₚ(p))
    let zeros := {z : ℂ // 0 < analyticOrderAt R z}
    let term := fun z : zeros ↦
      ((analyticOrderAt R z.val).toNat : ℂ) * nuclearityTestMellin χ φ z.val
    ∃ T : Q →L[ℂ] Q,
      (∀ f : Θ₀(χ), T (D.mkQ f) = D.mkQ (Aθ(φ) f)) ∧
      IsStronglyNuclearOperator T ∧ Summable (fun z ↦ ‖term z‖) ∧
      ∀ r : NuclearPresentation T,
        HasSum (fun n ↦ r.coeff n * r.functional n (r.vector n).val) (∑' z, term z) := by sorry

end Orbital

end RiemannMasullo
