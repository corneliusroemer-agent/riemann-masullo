module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec4_SpectralOrbital

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
import all RiemannMasullo.AppD_SchwartzBruhat.Sec2b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3b

import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import all RiemannMasullo.Ch06_LocalGlobal.Sec3
import all RiemannMasullo.AppA_AlgebraicNT.Sec3
import all RiemannMasullo.Ch03_IdelicZeta.Sec3b
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec3b

import RiemannMasullo.ForMathlib.Analysis.Meromorphic.VerticalStripZeros

/-! # §7.4 Nuclearity

The spectral quotient is in Schwartz–Bergman coordinates. The orbital quotients
use the quotient topology of the zero-moment homogeneous theta space.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NNReal NumberField.AdeleRing TensorProduct
set_option quotPrecheck false
set_option maxHeartbeats 150000
variable {F : Type*} [Field F] [NumberField F]
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "ω(" χ ")" => (χ : U).comp
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : (ideleClassNorm F).ker →ₜ* C𝔽)
local notation "P" => adelePolarSubspace F
local notation "B" => SchwartzBergman (univ : Set ℝ)
local notation "Entire" => entireContinuousMapSubalgebra
local notation "𝒟" => BruhatCompactSupport (IdeleClassGroup (𝓞 F) F)
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "Π(" χ ")" => LinearMap.ker ((homogeneousAdelicThetaLinearMap F (ω(χ))).domRestrict P)
local notation "Θ₀(" χ ")" => ↥P ⧸ Π(χ)
local notation "mkΘ(" χ ", " f ")" => (Submodule.Quotient.mk f : Θ₀(χ))
local notation "Z(" χ ", " τ ", " hτ ")" => (exists_globalPolarThetaMellin χ τ hτ).choose
local notation "testIntegrand(" χ ", " φ ", " s ")" =>
  (fun g : C𝔽 ↦ (φ : 𝒟).val g * (ideleClassNormTwist χ s) g)
attribute [local instance] instIdeleClassT2Sec4 instIdeleClassLocallyCompactSec4 instIdeleClassMeasurableSec4 instNuclearitySecondCountable


section Archimedean

open Classical

local notation "RealPlaces" => {v : InfinitePlace F // v.IsReal}
local notation "ComplexPlaces" => {v : InfinitePlace F // v.IsComplex}
local notation "Coordinates" => (RealPlaces → ℝ) × (ComplexPlaces → ℂ)
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)

variable (F) in
/-- Paper: Equation (7.4.3.1), p. 368.
Finite sums of adelic tensors have flat archimedean factors and arbitrary finite
factors. When required, each archimedean factor has additive integral zero.
Deviation: Uses the adelic tensor realization of §2.1.3 and the flat jet
conditions from §5.3.3. The tensor image carries the subspace topology from the
adelic Schwartz space. The display on p. 368 writes the projective tensor topology. -/
def globalArchimedeanFlatTests (requireArchMoment : Prop := False) : Submodule ℂ ℬ(𝔸[F]) :=
  let coordinates (x : InfiniteAdeleRing F) : Coordinates :=
    (fun v ↦ InfinitePlace.Completion.ringEquivRealOfIsReal v.property (x v.val),
      fun v ↦ InfinitePlace.Completion.ringEquivComplexOfIsComplex v.property (x v.val))
  let tensor := (adeleSchwartz_inductiveTensor_equiv F).choose
  Submodule.span ℂ {test | ∃ (f : ℬ(InfiniteAdeleRing F))
    (g : ℬ(FiniteAdeleRing (𝓞 F) F))
    (h : archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces)),
    (∀ x : InfiniteAdeleRing F, f (Multiplicative.ofAdd x) = h.val (coordinates x)) ∧
      (requireArchMoment → (∫ u : Coordinates, h.val u) = 0) ∧
      tensor (f ⊗ₜ[ℂ] g) = test}

variable (F) in
/-- Paper: Equation (7.4.3.1), p. 368.
The archimedean-flat tensor image is closed in the adelic Schwartz topology,
including when the archimedean integral of each tensor factor must vanish. -/
theorem globalArchimedeanFlatTests_isClosed (requireArchMoment : Prop) :
    IsClosed (globalArchimedeanFlatTests F requireArchMoment : Set ℬ(𝔸[F])) := by
  classical
  let E := ℬ(InfiniteAdeleRing F)
  let Ef := ℬ(FiniteAdeleRing (𝓞 F) F)
  let flat := archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces)
  let I : SchwartzMap Coordinates ℂ →L[ℂ] ℂ := SchwartzMap.integralCLM ℂ volume
  let flatWithMoment := flat ⊓ ⨅ _ : requireArchMoment, I.ker
  have hP : IsClosed (flatWithMoment : Set (SchwartzMap Coordinates ℂ)) := by
    simpa only [flatWithMoment, Submodule.coe_inf, Submodule.coe_iInf] using
      (archimedeanFlatSchwartz_isClosed (ι := RealPlaces) (κ := ComplexPlaces)).inter
        (isClosed_iInter fun _ : requireArchMoment ↦ I.isClosed_ker)
  obtain ⟨J, hJ⟩ := archimedeanSchwartzBruhat_equiv (F := F)
  let K := flatWithMoment.comap J.symm.toLinearMap
  have hK : IsClosed (K : Set E) := hP.preimage J.symm.continuous
  let : T2Space E := J.symm.toHomeomorph.isEmbedding.t2Space
  let : T2Space Ef := schwartzBruhat_t2_of_stages
  let : T2Space (E ⧸ K) := inferInstance
  let : PolynormableSpace ℂ (E ⧸ K) := polynormableSpace_quotient K
  let q : InductiveTensor E Ef →L[ℂ] InductiveTensor (E ⧸ K) Ef :=
    ⟨inductiveTensorMap K.mkQ LinearMap.id, inductiveTensorMap_continuous K.mkQL (ContinuousLinearMap.id ℂ Ef)⟩
  let e := (adeleSchwartz_inductiveTensor_equiv F).choose
  let D := globalArchimedeanFlatTests F requireArchMoment
  have hr : q.ker = (K.subtype.rTensor Ef).range := rTensor_mkQ Ef K
  have hmem (f : E) : f ∈ K ↔ ∃ h : flat,
      (∀ x : InfiniteAdeleRing F, f (Multiplicative.ofAdd x) =
        h.val (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) ∧
      (requireArchMoment → (∫ u : Coordinates, h.val u) = 0) := by
    change J.symm f ∈ flat ⊓ ⨅ _ : requireArchMoment, I.ker ↔ _
    simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
    constructor
    · rintro ⟨hf, hi⟩
      exact ⟨⟨J.symm f, hf⟩, fun x ↦ ((congrArg (fun g : E ↦ g (Multiplicative.ofAdd x))
        (J.apply_symm_apply f)).symm.trans (hJ _ _)), hi⟩
    · rintro ⟨h, hf, hi⟩
      have he : f = J h.val := Subtype.ext (funext fun x ↦ (hf x.toAdd).trans (hJ _ _).symm)
      rw [he, J.symm_apply_apply]
      exact ⟨h.property, hi⟩
  let insertFlat : (K ⊗[ℂ] Ef) →ₗ[ℂ] ℬ(𝔸[F]) := e.toLinearMap.comp (K.subtype.rTensor Ef)
  have hB (z : K ⊗[ℂ] Ef) : insertFlat z ∈ D := by
    induction z using TensorProduct.inductionOn with
    | tmul f g =>
      obtain ⟨h, hf, hi⟩ := (hmem f.val).mp f.property
      exact Submodule.subset_span ⟨f.val, g, h, hf, hi, rfl⟩
    | add u v hu hv => exact (map_add insertFlat u v).symm ▸ D.add_mem hu hv
  have hD : D = (q.comp e.symm.toContinuousLinearMap).ker := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨f, g, h, hf, hi, rfl⟩
      have hfK := (hmem f).mpr ⟨h, hf, hi⟩
      let z : InductiveTensor E Ef := f ⊗ₜ[ℂ] g
      refine (congrArg q (e.symm_apply_apply z)).trans ?_
      change K.mkQ f ⊗ₜ[ℂ] g = 0
      have hf0 : K.mkQ f = 0 := (Submodule.Quotient.mk_eq_zero K).mpr hfK
      rw [hf0, TensorProduct.zero_tmul]
    · intro x hx
      have hh : e.symm x ∈ q.ker := hx
      rw [hr] at hh
      obtain ⟨z, hz⟩ := hh
      have he : insertFlat z = x := (congrArg (fun v : InductiveTensor E Ef ↦ e v) hz).trans (e.apply_symm_apply x)
      exact he ▸ hB z
  change IsClosed (D : Set ℬ(𝔸[F]))
  rw [hD]
  exact (q.comp e.symm.toContinuousLinearMap).isClosed_ker

/-- A flat archimedean Schwartz function vanishes at the origin, which meets a wall. -/
private theorem globalArchimedeanFlatTests_zero_moments_flat
    (h : archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces)) :
    h.val (0 : Coordinates) = 0 := by
  have hw : (∃ i, (0 : Coordinates).1 i = 0) ∨ (∃ j, (0 : Coordinates).2 j = 0) := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    rcases w.isReal_or_isComplex with hr | hc
    · exact Or.inl ⟨⟨w, hr⟩, rfl⟩
    · exact Or.inr ⟨⟨w, hc⟩, rfl⟩
  have hk := Submodule.mem_iInf _ |>.mp h.property ⟨0, hw⟩
  have hk := Submodule.mem_iInf _ |>.mp hk 0
  have hk := Submodule.mem_iInf _ |>.mp hk (fun i => Fin.elim0 i)
  have := LinearMap.mem_ker.mp hk
  simpa using this

/-- Paper: Equation (7.4.3.1), p. 368.
Archimedean flatness kills evaluation at the adelic origin. Within the flat space,
the other zero-moment condition is the vanishing of the Fourier value at the origin. -/
theorem globalArchimedeanFlatTests_zero_moments (f : ℬ(𝔸[F]))
    (_hf : f ∈ globalArchimedeanFlatTests F) :
    f (Multiplicative.ofAdd 0) = 0 ∧
      (f ∈ adelePolarSubspace F ↔ adeleSchwartzFourier (F := F) f (Multiplicative.ofAdd 0) = 0) := by
  have h0 : f (Multiplicative.ofAdd 0) = 0 := by
    let ev : ℬ(𝔸[F]) →ₗ[ℂ] ℂ :=
      { toFun := fun f ↦ f (Multiplicative.ofAdd 0)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    change ev f = 0
    have hf : f ∈ LinearMap.ker ev := by
      refine (Submodule.span_le.mpr ?_) _hf
      rintro _ ⟨g₁, g₂, h, hx, -, rfl⟩
      change (adeleSchwartz_inductiveTensor_equiv F).choose (g₁ ⊗ₜ[ℂ] g₂) (Multiplicative.ofAdd 0) = 0
      rw [(adeleSchwartz_inductiveTensor_equiv F).choose_spec g₁ g₂ 0]
      have : g₁ (Multiplicative.ofAdd (0 : InfiniteAdeleRing F)) = 0 := by
        rw [hx 0]
        convert globalArchimedeanFlatTests_zero_moments_flat h using 2
        refine Prod.ext (funext fun v ↦ ?_) (funext fun v ↦ ?_)
        · exact map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal v.property)
        · exact map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex v.property)
      exact mul_eq_zero_of_left this _
    exact LinearMap.mem_ker.mp hf
  refine ⟨h0, ?_⟩
  rw [mem_adelePolarSubspace]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h0, h⟩⟩

variable (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
  (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))

/-- Paper: Equation (7.4.3.1), p. 368.
The denominator uses archimedean-flat factors. On the trivial norm-one component
each factor has zero additive integral, equivalently zero local Fourier value at zero.
Deviation: Implements the prose Fourier-moment condition. On a nontrivial norm-one
isotype the moment restriction can be imposed on representatives, since the two
polar functionals are trivial-isotypic. -/
def archNuclearityDenominator : Submodule ℂ (Θ₀(χ)) :=
  Submodule.span ℂ {x : Θ₀(χ) | ∃ f : P,
    f.val ∈ globalArchimedeanFlatTests F (ω(χ) = 1) ∧ x = Submodule.Quotient.mk f}

section FlatPolarImage

local notation "Coord" =>
  ({v : InfinitePlace F // v.IsReal} → ℝ) × ({v : InfinitePlace F // v.IsComplex} → ℂ)
local notation "Flat" =>
  archimedeanFlatSchwartz (ι := {v : InfinitePlace F // v.IsReal}) (κ := {v : InfinitePlace F // v.IsComplex})
local notation "coord" => InfiniteAdeleRing.ringEquiv_mixedSpace F

/-- The archimedean Schwartz functions with flat coordinate realizations. -/
private def archNuclearity_flatFactors : Submodule ℂ ℬ(InfiniteAdeleRing F) where
  carrier := {a | ∃ h : Flat, ∀ x : InfiniteAdeleRing F, a (Multiplicative.ofAdd x) = h.val (coord x)}
  zero_mem' := ⟨0, fun _ ↦ rfl⟩
  add_mem' := by
    rintro a b ⟨h, hh⟩ ⟨k, hk⟩
    refine ⟨h + k, fun x ↦ ?_⟩
    exact congrArg₂ (· + ·) (hh x) (hk x)
  smul_mem' := by
    rintro r a ⟨h, hh⟩
    exact ⟨r • h, fun x ↦ congrArg (r • ·) (hh x)⟩

/-- Coordinatewise multiplication by units preserves every archimedean wall
and hence also the vanishing of every jet along those walls. -/
private theorem archNuclearity_flatFactors_translate (u : (InfiniteAdeleRing F)ˣ)
    (a : ℬ(InfiniteAdeleRing F)) (ha : a ∈ archNuclearity_flatFactors) :
    schwartzBruhatUnitTranslate u a ∈ archNuclearity_flatFactors := by
  obtain ⟨h, hh⟩ := ha
  let d := Units.map (coord).toMonoidHom u⁻¹
  let L₀ : Coord ≃ₗ[ℝ] Coord :=
    { LinearMap.mulLeft ℝ (d : Coord) with
      invFun := fun x ↦ (↑d⁻¹ : Coord) * x
      left_inv := fun x ↦ by
        change (↑d⁻¹ : Coord) * ((d : Coord) * x) = x
        rw [← mul_assoc, Units.inv_mul, one_mul]
      right_inv := fun x ↦ by
        change (d : Coord) * ((↑d⁻¹ : Coord) * x) = x
        rw [← mul_assoc, Units.mul_inv, one_mul] }
  let L := L₀.toContinuousLinearEquiv
  let k := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L h.val
  have hk : k ∈ Flat := by
    have hf := h.property
    simp only [archimedeanFlatSchwartz, Submodule.mem_iInf, LinearMap.mem_ker, IsLinearMap.mk'_apply] at hf ⊢
    rintro ⟨x, hx⟩ n v
    have hx' : (∃ i, (L x).1 i = 0) ∨ ∃ j, (L x).2 j = 0 := by
      rcases hx with ⟨i, hi⟩ | ⟨j, hj⟩
      · exact Or.inl ⟨i, by change (d : Coord).1 i * x.1 i = 0; rw [hi, mul_zero]⟩
      · exact Or.inr ⟨j, by change (d : Coord).2 j * x.2 j = 0; rw [hj, mul_zero]⟩
    change iteratedFDeriv ℝ n ((h.val : Coord → ℂ) ∘ L) x v = 0
    erw [L.toContinuousLinearMap.iteratedFDeriv_comp_right (h.val.smooth ⊤) x (i := n)
      (mod_cast le_top)]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    exact hf ⟨L x, hx'⟩ n (fun i ↦ L (v i))
  refine ⟨⟨k, hk⟩, fun x ↦ ?_⟩
  rw [schwartzBruhatUnitTranslate_apply, hh]
  change h.val (coord ((↑u⁻¹ : InfiniteAdeleRing F) * x)) = h.val ((d : Coord) * coord x)
  rw [map_mul]
  rfl


/-- Once finite mass-zero factors may be discarded modulo a submodule, the total
moment of a flat tensor sum can be imposed on one archimedean representative. -/
private theorem tensor_mem_flat_moment_sup
    {E W X : Type*} [AddCommGroup E] [AddCommGroup W] [AddCommGroup X]
    [Module ℂ E] [Module ℂ W] [Module ℂ X]
    (e : E ⊗[ℂ] W →ₗ[ℂ] X) (Uflat : Submodule ℂ E) (A K : Submodule ℂ X)
    (i : E →ₗ[ℂ] ℂ) (j : W →ₗ[ℂ] ℂ) (L : X →ₗ[ℂ] ℂ)
    (b₀ : W) (hb₀ : j b₀ = 1)
    (hL : ∀ a b, L (e (a ⊗ₜ[ℂ] b)) = i a * j b)
    (hA : ∀ a ∈ Uflat, i a = 0 → ∀ b, e (a ⊗ₜ[ℂ] b) ∈ A)
    (hK : ∀ a ∈ Uflat, ∀ b, j b = 0 → e (a ⊗ₜ[ℂ] b) ∈ A ⊔ K)
    {x : X} (hx : x ∈ Submodule.span ℂ {v | ∃ a ∈ Uflat, ∃ b, e (a ⊗ₜ[ℂ] b) = v})
    (hx₀ : L x = 0) : x ∈ A ⊔ K := by
  let u : E →ₗ[ℂ] X := e.comp ((TensorProduct.mk ℂ E W).flip b₀)
  have hu (a : E) : u a = e (a ⊗ₜ[ℂ] b₀) := rfl
  have H (x : X) (hx : x ∈ Submodule.span ℂ {v | ∃ a ∈ Uflat, ∃ b, e (a ⊗ₜ[ℂ] b) = v}) :
      ∃ a ∈ Uflat, i a = L x ∧ x - u a ∈ A ⊔ K := by
    refine Submodule.span_induction (p := fun x _ ↦ ∃ a ∈ Uflat, i a = L x ∧ x - u a ∈ A ⊔ K)
      ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, ha, b, rfl⟩
      refine ⟨j b • a, Uflat.smul_mem _ ha, ?_, ?_⟩
      · rw [map_smul, smul_eq_mul, hL, mul_comm]
      · have hj : j (b - j b • b₀) = 0 := by
          rw [map_sub, map_smul, hb₀, smul_eq_mul, mul_one, sub_self]
        have h := hK a ha (b - j b • b₀) hj
        simpa only [TensorProduct.tmul_sub, TensorProduct.tmul_smul, TensorProduct.smul_tmul', map_sub, hu] using h
    · exact ⟨0, Uflat.zero_mem, by rw [map_zero, map_zero], by simp⟩
    · rintro x y _ _ ⟨a, ha, hia, hxa⟩ ⟨b, hb, hib, hyb⟩
      refine ⟨a + b, Uflat.add_mem ha hb, by rw [map_add, map_add, hia, hib], ?_⟩
      rw [map_add, add_sub_add_comm]
      exact Submodule.add_mem _ hxa hyb
    · rintro c x _ ⟨a, ha, hia, hxa⟩
      refine ⟨c • a, Uflat.smul_mem c ha, by rw [map_smul, map_smul, hia], ?_⟩
      rw [map_smul, ← smul_sub]
      exact Submodule.smul_mem _ c hxa
  obtain ⟨a, ha, hi, he⟩ := H x hx
  have haux : u a ∈ A ⊔ K := (show A ≤ A ⊔ K from le_sup_left) (hA a ha (hi.trans hx₀) b₀)
  have hsum := Submodule.add_mem _ he haux
  rwa [sub_add_cancel] at hsum


local notation "Aflat" => archNuclearity_flatFactors (F := F)
local notation "A₀(" χ ")" => globalArchimedeanFlatTests F (ω(χ) = 1)
local notation "A" => globalArchimedeanFlatTests F
local notation "K(" χ ")" => (homogeneousAdelicThetaLinearMap F (ω(χ))).ker
local notation "ArchTests" => ℬ(InfiniteAdeleRing F)
local notation "FiniteTests" => ℬ(FiniteAdeleRing (𝓞 F) F)
local notation "tensor" => (adeleSchwartz_inductiveTensor_equiv F).choose
local notation "hatL" => (ContinuousLinearMap.snd ℂ ℂ ℂ).toLinearMap.comp
  ((adelePolarValues_isLinear (F := F)).mk' adelePolarValues)

private theorem archNuclearityDenominator_mem_restricted
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (x : Θ₀(χ)) :
    x ∈ archNuclearityDenominator χ ↔
      ∃ f : P, f.val ∈ A₀(χ) ∧ x = mkΘ(χ, f) := by
  let D : Submodule ℂ P := (A₀(χ)).comap (P).subtype
  let q : P →ₗ[ℂ] Θ₀(χ) := (Π(χ)).mkQ
  have hEq : archNuclearityDenominator χ = D.map q := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨f, hf, rfl⟩
    · rintro _ ⟨f, hf, rfl⟩
      exact Submodule.subset_span ⟨f, hf, rfl⟩
  rw [hEq]
  exact exists_congr fun f ↦ and_congr_right fun _ ↦ eq_comm

private theorem archNuclearity_flatTests_mono {Q R : Prop} (h : Q → R) :
    globalArchimedeanFlatTests F R ≤ globalArchimedeanFlatTests F Q := by
  apply Submodule.span_mono
  rintro _ ⟨a, b, f, hf, hR, rfl⟩
  exact ⟨a, b, f, hf, hR ∘ h, rfl⟩

/-- Reduction to additive moment factorization and the vanishing of weighted finite
coinvariants modulo the restricted flat space and the theta kernel. -/
private theorem archNuclearity_of_finiteMassReduction
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (x : Θ₀(χ))
    (H : ω(χ) = 1 → ∃ (i : ArchTests →ₗ[ℂ] ℂ) (j : FiniteTests →ₗ[ℂ] ℂ) (b₀ : FiniteTests),
      j b₀ = 1 ∧
      (∀ a b, hatL (tensor (a ⊗ₜ[ℂ] b)) = i a * j b) ∧
      (∀ (a : ArchTests) (h : Flat), (∀ z, a (Multiplicative.ofAdd z) = h.val (coord z)) →
        (i a = 0 ↔ (∫ y : Coord, h.val y) = 0)) ∧
      (∀ a ∈ Aflat, ∀ b, j b = 0 → tensor (a ⊗ₜ[ℂ] b) ∈ A₀(χ) ⊔ K(χ))) :
    x ∈ archNuclearityDenominator χ ↔
      ∃ f : P, f.val ∈ A ∧ x = mkΘ(χ, f) := by
  rw [archNuclearityDenominator_mem_restricted]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, archNuclearity_flatTests_mono (False.elim : False → ω(χ) = 1) hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    by_cases hω : ω(χ) = 1
    swap
    · exact ⟨f, archNuclearity_flatTests_mono hω hf, rfl⟩
    obtain ⟨i, j, b₀, hb, hL, hi, hK⟩ := H hω
    have hA (a : ArchTests) (ha : a ∈ Aflat) (h0 : i a = 0) (b : FiniteTests) :
        tensor (a ⊗ₜ[ℂ] b) ∈ A₀(χ) := by
      obtain ⟨h, hh⟩ := ha
      exact Submodule.subset_span ⟨a, b, h, hh, fun _ ↦ (hi a h hh).mp h0, rfl⟩
    have hspan : A ≤ Submodule.span ℂ {v | ∃ a ∈ Aflat, ∃ b, tensor (a ⊗ₜ[ℂ] b) = v} := by
      apply Submodule.span_mono
      rintro _ ⟨a, b, h, hh, _, rfl⟩
      exact ⟨a, ⟨h, hh⟩, b, rfl⟩
    have hsum := tensor_mem_flat_moment_sup (tensor).toLinearMap Aflat (A₀(χ)) (K(χ)) i j hatL b₀
      hb hL hA hK (hspan hf) ((mem_adelePolarSubspace f.val).mp f.property).2
    obtain ⟨g, hg, k, hk, hgf⟩ := Submodule.mem_sup.mp hsum
    have hg0 : g ∈ P := by
      have hgflat : g ∈ A := archNuclearity_flatTests_mono (False.elim : False → ω(χ) = 1) hg
      apply (globalArchimedeanFlatTests_zero_moments g hgflat).2.mpr
      suffices hatL g = 0 from this
      refine Submodule.span_induction (p := fun y _ ↦ hatL y = 0) ?_ ?_ ?_ ?_ hg
      · rintro _ ⟨a, b, h, hh, hM, rfl⟩
        exact (hL a b).trans (mul_eq_zero_of_left ((hi a h hh).mpr (hM hω)) _)
      · exact map_zero _
      · intro a b _ _ ha hb'
        rw [map_add, ha, hb', add_zero]
      · intro c y _ hy
        rw [map_smul, hy, smul_zero]
    refine ⟨⟨g, hg0⟩, hg, (Submodule.Quotient.eq (Π(χ))).mpr ?_⟩
    change f.val - g ∈ K(χ)
    have he : f.val - g = k := by rw [← hgf, add_comm g k, add_sub_cancel_right]
    rwa [he]

open scoped RestrictedProduct
local notation "AF" => FiniteAdeleRing (𝓞 F) F
/-- In mixed archimedean coordinates the global Fourier value at zero factors
as ordinary archimedean volume integration against a fixed finite functional. -/
private theorem archNuclearity_productMoment :
    ∃ J : FiniteTests → ℂ, ∀ (a : ℬ(InfiniteAdeleRing F)) (b : FiniteTests),
      adeleSchwartzFourier (F := F) (tensor (a ⊗ₜ[ℂ] b)) (Multiplicative.ofAdd 0) =
        (∫ y : Coord, a (Multiplicative.ofAdd ((coord).symm y))) * J b := by
  let (v : V) : CompactSpace (v.adicCompletionIntegers F) := compactSpace_adicCompletionIntegers v
  let (v : V) : LocallyCompactSpace (v.adicCompletion F) := locallyCompactSpace_adicCompletion v
  let : Fact (∀ v : V, IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
  let : LocallyCompactSpace AF := inferInstanceAs
    (LocallyCompactSpace (Πʳ v : V, [v.adicCompletion F, v.adicCompletionIntegers F]))
  let : LocallyCompactSpace 𝔸[F] := inferInstanceAs
    (LocallyCompactSpace (InfiniteAdeleRing F × AF))
  let := ratAdele_secondCountable
  obtain ⟨e, _, _⟩ := exists_adeleTrace_dualCoordinates F
  let : SecondCountableTopology 𝔸[F] := e.symm.toHomeomorph.isEmbedding.secondCountableTopology
  let : SecondCountableTopology (InfiniteAdeleRing F × AF) := inferInstanceAs (SecondCountableTopology 𝔸[F])
  let : SecondCountableTopology AF :=
    (isEmbedding_prodMkRight (X := InfiniteAdeleRing F) (Y := AF) 0).secondCountableTopology
  let : IsTopologicalAddGroup AF := inferInstanceAs
    (IsTopologicalAddGroup (Πʳ v : V, [v.adicCompletion F, v.adicCompletionIntegers F]))
  let : IsTopologicalAddGroup 𝔸[F] := inferInstanceAs
    (IsTopologicalAddGroup (InfiniteAdeleRing F × AF))
  let : MeasurableSpace AF := borel _
  let : BorelSpace AF := ⟨rfl⟩
  let : MeasurableSpace 𝔸[F] := borel _
  let : BorelSpace 𝔸[F] := ⟨rfl⟩
  let d : (Coord × AF) ≃ₜ+ 𝔸[F] :=
    { toAddEquiv := (coord).symm.toAddEquiv.prodCongr (AddEquiv.refl _)
      continuous_toFun := ((continuous_infiniteAdeleRingEquivMixedSpace_symm F).comp continuous_fst).prodMk
        continuous_snd
      continuous_invFun := ((continuous_infiniteAdeleRingEquivMixedSpace F).comp continuous_fst).prodMk
        continuous_snd }
  let μf := Measure.addHaar (G := AF)
  let μ : Measure (Coord × AF) := (volume : Measure Coord).prod μf
  let : μ.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  let ν : Measure 𝔸[F] := μ.map d
  let : ν.IsAddHaarMeasure := d.isAddHaarMeasure_map μ
  let m := additiveTamagawaMeasure F
  let : m.IsAddHaarMeasure := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec.1
  let c := m.addHaarScalarFactor ν
  have hc : m = c • ν := Measure.isAddLeftInvariant_eq_smul m ν
  refine ⟨fun b ↦ (c : ℂ) * ∫ x, b (Multiplicative.ofAdd x) ∂μf, fun a b ↦ ?_⟩
  rw [(adeleSchwartzFourier_apply_zero _).2]
  change (∫ x : 𝔸[F], tensor (a ⊗ₜ[ℂ] b) (Multiplicative.ofAdd x) ∂m) = _
  rw [hc, integral_smul_nnreal_measure]
  change (c : ℂ) * ∫ x : 𝔸[F], tensor (a ⊗ₜ[ℂ] b) (Multiplicative.ofAdd x) ∂ν = _
  rw [show ν = μ.map d.toHomeomorph.toMeasurableEquiv from rfl, integral_map_equiv]
  have h (x : Coord × AF) :
      tensor (a ⊗ₜ[ℂ] b) (Multiplicative.ofAdd (d.toHomeomorph.toMeasurableEquiv x)) =
        a (Multiplicative.ofAdd ((coord).symm x.1)) * b (Multiplicative.ofAdd x.2) :=
    (adeleSchwartz_inductiveTensor_equiv F).choose_spec a b (d x)
  simp_rw [h]
  exact (congrArg ((c : ℂ) * ·) (integral_prod_mul (μ := (volume : Measure Coord)) (ν := μf)
    (fun y ↦ a (Multiplicative.ofAdd ((coord).symm y))) (fun y ↦ b (Multiplicative.ofAdd y)))).trans
      (mul_left_comm _ _ _)

local notation "hatC" => (ContinuousLinearMap.snd ℂ ℂ ℂ).comp
  (⟨(adelePolarValues_isLinear (F := F)).mk' adelePolarValues,
    adelePolarValues_continuous⟩ : ℬ(𝔸[F]) →L[ℂ] ℂ × ℂ)

private theorem archNuclearity_nonzero_pure_moment :
    ∃ (a : ArchTests) (b : FiniteTests), hatC (tensor (a ⊗ₜ[ℂ] b)) ≠ 0 := by
  by_contra! h
  have hz : (hatC).toLinearMap.comp (tensor).toLinearMap = 0 :=
    TensorProduct.ext' fun a b ↦ h a b
  obtain ⟨f, hf⟩ := adelePolarValues_surjective (F := F) ((0, 1) : ℂ × ℂ)
  have hf' : hatC f = 1 := congrArg Prod.snd hf
  have ht := LinearMap.congr_fun hz ((tensor).symm f)
  change hatC (tensor ((tensor).symm f)) = 0 at ht
  rw [(tensor).apply_symm_apply, hf'] at ht
  exact one_ne_zero ht

private theorem archNuclearity_normalized_moment :
    ∃ (i : ArchTests →L[ℂ] ℂ) (j : FiniteTests →ₗ[ℂ] ℂ) (a₀ : ArchTests) (b₀ : FiniteTests),
      i a₀ ≠ 0 ∧ j b₀ = 1 ∧
      (∀ a b, hatC (tensor (a ⊗ₜ[ℂ] b)) = i a * j b) ∧
      (∀ (a : ArchTests) (h : Flat), (∀ z, a (Multiplicative.ofAdd z) = h.val (coord z)) →
        (i a = 0 ↔ (∫ y : Coord, h.val y) = 0)) := by
  obtain ⟨a₀, b₀, hab₀⟩ := archNuclearity_nonzero_pure_moment (F := F)
  obtain ⟨rawJ, hraw⟩ := archNuclearity_productMoment (F := F)
  let rawI (a : ArchTests) := ∫ y : Coord, a (Multiplicative.ofAdd ((coord).symm y))
  have hL (a : ArchTests) (b : FiniteTests) : hatC (tensor (a ⊗ₜ[ℂ] b)) = rawI a * rawJ b := hraw a b
  have hj₀ : rawJ b₀ ≠ 0 := right_ne_zero_of_mul (fun hz ↦ hab₀ ((hL a₀ b₀).trans hz))
  have hi₀ : rawI a₀ ≠ 0 := left_ne_zero_of_mul (fun hz ↦ hab₀ ((hL a₀ b₀).trans hz))
  let T := InductiveTensor ArchTests FiniteTests
  let eb : ArchTests →ₗ[ℂ] T := (TensorProduct.mk ℂ ArchTests FiniteTests).flip b₀
  have heb : Continuous eb := by
    let h := withGeneratingSeminorms_spec (ArchTests ⊗[ℂ] FiniteTests)
      (fun p : {p : Seminorm ℂ (ArchTests ⊗[ℂ] FiniteTests) //
        (∀ a : ArchTests, Continuous (fun b : FiniteTests ↦ p (a ⊗ₜ[ℂ] b))) ∧
        (∀ b : FiniteTests, Continuous (fun a : ArchTests ↦ p (a ⊗ₜ[ℂ] b)))} ↦ p.val)
    exact h.continuous_of_continuous_comp eb fun p ↦ p.property.2 b₀
  let i : ArchTests →L[ℂ] ℂ := (hatC).comp ((tensor).toContinuousLinearMap.comp ⟨eb, heb⟩)
  let j : FiniteTests →ₗ[ℂ] ℂ := (hatC (tensor (a₀ ⊗ₜ[ℂ] b₀)))⁻¹ •
    ((hatC).toLinearMap.comp ((tensor).toLinearMap.comp (TensorProduct.mk ℂ ArchTests FiniteTests a₀)))
  have hi (a : ArchTests) : i a = rawI a * rawJ b₀ := hL a b₀
  have hj (b : FiniteTests) : j b = (rawI a₀ * rawJ b₀)⁻¹ * (rawI a₀ * rawJ b) := by
    change (hatC (tensor (a₀ ⊗ₜ[ℂ] b₀)))⁻¹ * hatC (tensor (a₀ ⊗ₜ[ℂ] b)) = _
    rw [hL, hL]
  refine ⟨i, j, a₀, b₀, hab₀, ?_, ?_, ?_⟩
  · rw [hj, inv_mul_cancel₀ (mul_ne_zero hi₀ hj₀)]
  · intro a b
    rw [hL, hi, hj]
    field_simp
  · intro a h hh
    rw [hi, mul_eq_zero, or_iff_left hj₀]
    have hh' (y : Coord) : a (Multiplicative.ofAdd ((coord).symm y)) = h.val y := by
      rw [hh, RingEquiv.apply_symm_apply]
    have hI : rawI a = ∫ y : Coord, h.val y :=
      congrArg (fun f : Coord → ℂ ↦ ∫ y, f y) (funext hh')
    rw [hI]

local notation "A∞" => InfiniteAdeleRing F
local notation "𝕀" => IdeleGroup (𝓞 F) F

private def archNuclearity_archUnit (u : A∞ˣ) : 𝕀 where
  val := (u.val, 1)
  inv := (u.inv, 1)
  val_inv := Prod.ext u.val_inv (one_mul 1)
  inv_val := Prod.ext u.inv_val (one_mul 1)

private def archNuclearity_finiteUnit (u : AFˣ) : 𝕀 where
  val := (1, u.val)
  inv := (1, u.inv)
  val_inv := Prod.ext (one_mul 1) u.val_inv
  inv_val := Prod.ext (one_mul 1) u.inv_val

private def archNuclearity_translateLinear {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (u : Rˣ) : ℬ(R) →ₗ[ℂ] ℬ(R) where
  toFun := schwartzBruhatUnitTranslate u
  map_add' := fun _ _ ↦ Subtype.ext rfl
  map_smul' := fun _ _ ↦ Subtype.ext rfl

private theorem archNuclearity_translate_pure (u : A∞ˣ) (v : AFˣ) (a : ArchTests) (b : FiniteTests) :
    schwartzBruhatUnitTranslate (archNuclearity_archUnit u * archNuclearity_finiteUnit v)
      (tensor (a ⊗ₜ[ℂ] b)) =
    tensor (schwartzBruhatUnitTranslate u a ⊗ₜ[ℂ] schwartzBruhatUnitTranslate v b) := by
  apply Subtype.ext
  funext x
  change schwartzBruhatUnitTranslate (archNuclearity_archUnit u * archNuclearity_finiteUnit v)
      (tensor (a ⊗ₜ[ℂ] b)) (Multiplicative.ofAdd x.toAdd) =
    tensor (schwartzBruhatUnitTranslate u a ⊗ₜ[ℂ] schwartzBruhatUnitTranslate v b)
      (Multiplicative.ofAdd x.toAdd)
  rw [schwartzBruhatUnitTranslate_apply,
    (adeleSchwartz_inductiveTensor_equiv F).choose_spec,
    (adeleSchwartz_inductiveTensor_equiv F).choose_spec,
    schwartzBruhatUnitTranslate_apply, schwartzBruhatUnitTranslate_apply]
  change a (Multiplicative.ofAdd ((1 * (↑u⁻¹ : A∞)) * x.toAdd.1)) *
    b (Multiplicative.ofAdd (((↑v⁻¹ : AF) * 1) * x.toAdd.2)) = _
  rw [mul_one, one_mul]

private theorem archNuclearity_translate_one {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (a : ℬ(R)) : schwartzBruhatUnitTranslate 1 a = a := by
  apply Subtype.ext
  funext x
  change schwartzBruhatUnitTranslate 1 a (Multiplicative.ofAdd x.toAdd) = _
  rw [schwartzBruhatUnitTranslate_apply, inv_one, Units.val_one, one_mul]
  rfl

private theorem archNuclearity_unit_arch_finite (w : 𝕀) :
    ∃ u : A∞ˣ, ∃ v : AFˣ, w = archNuclearity_archUnit u * archNuclearity_finiteUnit v := by
  refine ⟨Units.map (RingHom.fst A∞ AF).toMonoidHom w,
    Units.map (RingHom.snd A∞ AF).toMonoidHom w, ?_⟩
  apply Units.ext
  exact Prod.ext (mul_one _).symm (one_mul _).symm

local notation "absValue(" u ")" => ((((ideleNorm F u).val : ℝ) : ℂ))

private theorem archNuclearity_hatC_translate (u : 𝕀) (f : ℬ(𝔸[F])) :
    hatC (schwartzBruhatUnitTranslate u f) = absValue(u) * hatC f := by
  have h := globalThetaPolarValues_snd_translate (QuotientGroup.mk u) (Submodule.Quotient.mk f)
  rw [(existsUnique_globalThetaAction (F := F)).exists.choose_spec.2 u f] at h
  exact h

private theorem archNuclearity_moment_arch_translate (i : ArchTests →L[ℂ] ℂ) (j : FiniteTests →ₗ[ℂ] ℂ)
    (b₀ : FiniteTests) (hb : j b₀ = 1) (hL : ∀ a b, hatC (tensor (a ⊗ₜ[ℂ] b)) = i a * j b)
    (u : A∞ˣ) (a : ArchTests) :
    i (schwartzBruhatUnitTranslate u a) = absValue(archNuclearity_archUnit u) * i a := by
  have h := archNuclearity_hatC_translate
    (archNuclearity_archUnit u * archNuclearity_finiteUnit (F := F) 1) (tensor (a ⊗ₜ[ℂ] b₀))
  rw [archNuclearity_translate_pure, archNuclearity_translate_one, hL, hL, hb, mul_one, mul_one,
    show archNuclearity_finiteUnit (F := F) 1 = 1 from Units.ext rfl, mul_one] at h
  exact h

private theorem archNuclearity_moment_finite_translate (i : ArchTests →L[ℂ] ℂ) (j : FiniteTests →ₗ[ℂ] ℂ)
    (a₀ : ArchTests) (ha : i a₀ ≠ 0) (hL : ∀ a b, hatC (tensor (a ⊗ₜ[ℂ] b)) = i a * j b)
    (v : AFˣ) (b : FiniteTests) :
    j (schwartzBruhatUnitTranslate v b) = absValue(archNuclearity_finiteUnit v) * j b := by
  have h := archNuclearity_hatC_translate
    (archNuclearity_archUnit (F := F) 1 * archNuclearity_finiteUnit v) (tensor (a₀ ⊗ₜ[ℂ] b))
  rw [archNuclearity_translate_pure, archNuclearity_translate_one, hL, hL,
    show archNuclearity_archUnit (F := F) 1 = 1 from Units.ext rfl, one_mul,
    mul_left_comm] at h
  exact mul_left_cancel₀ ha h

private theorem archNuclearity_translate_mul (u v : 𝕀) (f : ℬ(𝔸[F])) :
    schwartzBruhatUnitTranslate u (schwartzBruhatUnitTranslate v f) =
    schwartzBruhatUnitTranslate (u * v) f := by
  apply Subtype.ext
  funext x
  change f (Multiplicative.ofAdd (v.inv * (u.inv * x.toAdd))) =
    f (Multiplicative.ofAdd ((u * v).inv * x.toAdd))
  exact congrArg (fun y ↦ f (Multiplicative.ofAdd y)) (mul_assoc v.inv u.inv x.toAdd).symm

private theorem archNuclearity_archLift (v : AFˣ) :
    ∃ u : A∞ˣ, ideleNorm F (archNuclearity_archUnit u) = ideleNorm F (archNuclearity_finiteUnit v) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  let t := ideleNorm F (archNuclearity_finiteUnit v)
  let g := singlePlaceIdeleNormSection F w t
  let u := Units.map (RingHom.fst A∞ AF).toMonoidHom g
  have hu : archNuclearity_archUnit u = g := Units.ext (Prod.ext rfl rfl)
  exact ⟨u, hu ▸ singlePlaceIdeleNormSection_rightInverse F w t⟩

private theorem archNuclearity_theta_translate_sameNorm
    (χ : PontryaginDual C𝔽) (hω : ω(χ) = 1) (u v : 𝕀) (h : ideleNorm F u = ideleNorm F v)
    (f : ℬ(𝔸[F])) :
    homogeneousAdelicThetaLinearMap F (ω(χ)) (schwartzBruhatUnitTranslate u f) =
    homogeneousAdelicThetaLinearMap F (ω(χ)) (schwartzBruhatUnitTranslate v f) := by
  let g := u * v⁻¹
  have hg : ideleNorm F g = 1 := by
    change ideleNorm F (u * v⁻¹) = _
    rw [map_mul, map_inv, h, mul_inv_cancel]
  let k : (ideleClassNorm F).ker :=
    ⟨QuotientGroup.mk g, MonoidHom.mem_ker.mpr (show ideleNorm F g = 1 from hg)⟩
  have he := globalConverse_nontrivial_exact_theta_translate (ω(χ)) k g rfl
    (schwartzBruhatUnitTranslate v f)
  have hw : (ω(χ) k : ℂ) = 1 :=
    (congrArg (fun χ' : PontryaginDual (ideleClassNorm F).ker ↦ (χ' k : ℂ)) hω).trans rfl
  let M := homogeneousAdelicThetaLinearMap F (ω(χ))
  have htrans : schwartzBruhatUnitTranslate g (schwartzBruhatUnitTranslate v f) =
      schwartzBruhatUnitTranslate u f :=
    (archNuclearity_translate_mul g v f).trans
      (congrArg (fun s : 𝕀 ↦ schwartzBruhatUnitTranslate s f) (inv_mul_cancel_right u v))
  exact ((congrArg M htrans).symm.trans he).trans
    ((congrArg (fun c : ℂ ↦ c • M (schwartzBruhatUnitTranslate v f)) hw).trans (one_smul _ _))

/-- A finite eigendistribution of additive weight extends by tensoring with the
archimedean moment. Global rank one then determines it uniquely. -/
private theorem archNuclearity_finiteEigen_unique
    (hcont : ∀ L : FiniteTests →ₗ[ℂ] ℂ, Continuous L)
    (i : ArchTests →L[ℂ] ℂ) (j : FiniteTests →ₗ[ℂ] ℂ) (a₀ : ArchTests) (b₀ : FiniteTests)
    (ha : i a₀ ≠ 0) (hb : j b₀ = 1) (hL : ∀ a b, hatC (tensor (a ⊗ₜ[ℂ] b)) = i a * j b)
    (L : FiniteTests →ₗ[ℂ] ℂ)
    (hLcov : ∀ (u : AFˣ) b, L (schwartzBruhatUnitTranslate u b) = absValue(archNuclearity_finiteUnit u) * L b) :
    ∃ c : ℂ, L = c • j := by
  let T := InductiveTensor ArchTests FiniteTests
  let Q : T →ₗ[ℂ] ℂ := (LinearMap.mul' ℂ ℂ).comp (TensorProduct.map i.toLinearMap L)
  have hQ (a : ArchTests) (b : FiniteTests) : Q (a ⊗ₜ[ℂ] b) = i a * L b := by
    change (LinearMap.mul' ℂ ℂ) (TensorProduct.map i.toLinearMap L (a ⊗ₜ[ℂ] b)) = _
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply]
    rfl
  have hcQ : Continuous Q := by
    let hS := withGeneratingSeminorms_spec (ArchTests ⊗[ℂ] FiniteTests)
      (fun p : {p : Seminorm ℂ (ArchTests ⊗[ℂ] FiniteTests) //
        (∀ a : ArchTests, Continuous (fun b : FiniteTests ↦ p (a ⊗ₜ[ℂ] b))) ∧
        (∀ b : FiniteTests, Continuous (fun a : ArchTests ↦ p (a ⊗ₜ[ℂ] b)))} ↦ p.val)
    refine (PolynormableSpace.withSeminorms ℂ ℂ).continuous_of_continuous_comp Q fun q ↦ ?_
    refine hS.continuous_seminorm ⟨q.val.comp Q, fun a ↦ q.property.comp ?_, fun b ↦ q.property.comp ?_⟩
    · exact (continuous_const.mul (hcont L)).congr fun b ↦ (hQ a b).symm
    · exact (i.continuous.mul continuous_const).congr fun a ↦ (hQ a b).symm
  let D : StrongDual ℂ ℬ(𝔸[F]) := (⟨Q, hcQ⟩ : T →L[ℂ] ℂ).comp (tensor).symm.toContinuousLinearMap
  have hD (a : ArchTests) (b : FiniteTests) : D (tensor (a ⊗ₜ[ℂ] b)) = i a * L b :=
    (congrArg Q ((tensor).symm_apply_apply (a ⊗ₜ[ℂ] b))).trans (hQ a b)
  let c := ideleClassNormTwist (1 : U) 1
  have hDcov (w : 𝕀) (f : ℬ(𝔸[F])) :
      D (schwartzBruhatUnitTranslate w f) = absValue(w) * D f := by
    obtain ⟨u, v, rfl⟩ := archNuclearity_unit_arch_finite w
    let w := archNuclearity_archUnit u * archNuclearity_finiteUnit v
    let L₁ := (D.toLinearMap.comp (archNuclearity_translateLinear w)).comp (tensor).toLinearMap
    let L₂ := absValue(w) • D.toLinearMap.comp (tensor).toLinearMap
    have he : L₁ = L₂ := by
      refine TensorProduct.ext' fun a b ↦ ?_
      change D (schwartzBruhatUnitTranslate (archNuclearity_archUnit u * archNuclearity_finiteUnit v)
        (tensor (a ⊗ₜ[ℂ] b))) = absValue(archNuclearity_archUnit u * archNuclearity_finiteUnit v) *
          D (tensor (a ⊗ₜ[ℂ] b))
      rw [archNuclearity_translate_pure, hD, hD, archNuclearity_moment_arch_translate i j b₀ hb hL,
        hLcov, map_mul, Units.val_mul, NNReal.coe_mul, Complex.ofReal_mul, mul_mul_mul_comm]
    obtain ⟨x, rfl⟩ := (tensor).surjective f
    exact LinearMap.congr_fun he x
  have hmem : D ∈ adelicEigendistributions c := by
    intro w f
    change _ = ((1 : ℂ) * absValue(w) ^ (1 : ℂ)) * D f
    rw [Complex.cpow_one, one_mul]
    exact hDcov w f
  let H : StrongDual ℂ ℬ(𝔸[F]) := hatC
  have hH : H ∈ adelicEigendistributions c := by
    intro w f
    change _ = ((1 : ℂ) * absValue(w) ^ (1 : ℂ)) * H f
    rw [Complex.cpow_one, one_mul]
    exact archNuclearity_hatC_translate w f
  have hnH : H ≠ 0 := by
    intro he
    have hh := hL a₀ b₀
    change H (tensor (a₀ ⊗ₜ[ℂ] b₀)) = _ at hh
    rw [he, zero_apply, hb, mul_one] at hh
    exact ha hh.symm
  have hr := Module.rank_eq_one_iff_finrank_eq_one.mp (adelicEigendistributions_rank c)
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hr hH hnH, Submodule.mem_span_singleton] at hmem
  obtain ⟨z, hz⟩ := hmem
  refine ⟨z, LinearMap.ext fun b ↦ ?_⟩
  have he := congrArg (fun d : StrongDual ℂ ℬ(𝔸[F]) ↦ d (tensor (a₀ ⊗ₜ[ℂ] b))) hz
  change z * hatC (tensor (a₀ ⊗ₜ[ℂ] b)) = D (tensor (a₀ ⊗ₜ[ℂ] b)) at he
  rw [hL, hD, mul_left_comm] at he
  exact (mul_left_cancel₀ ha he).symm

/-- If the additive-mass functional spans the algebraic eigenfunctionals,
the weighted translation differences generate its kernel. -/
private theorem span_weightedDifferences_eq_ker
    {W G : Type*} [AddCommGroup W] [Module ℂ W] (T : G → W → W) (c : G → ℂ)
    (J : W →ₗ[ℂ] ℂ) (hJ : ∀ u w, J (T u w) = c u * J w)
    (huniq : ∀ L : W →ₗ[ℂ] ℂ, (∀ u w, L (T u w) = c u * L w) → ∃ z : ℂ, L = z • J) :
    Submodule.span ℂ {x | ∃ u w, x = T u w - c u • w} = J.ker := by
  let D := Submodule.span ℂ {x | ∃ u w, x = T u w - c u • w}
  have hD : D ≤ J.ker := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨u, w, rfl⟩
    change J (T u w - c u • w) = 0
    rw [map_sub, map_smul, smul_eq_mul, hJ, sub_self]
  apply Subspace.dualAnnihilator_inj.mp
  apply le_antisymm
  · intro l hl
    have hL (u : G) (w : W) : l (T u w) = c u * l w := by
      have hm : T u w - c u • w ∈ D := Submodule.subset_span ⟨u, w, rfl⟩
      have hz := (D.mem_dualAnnihilator l).mp hl _ hm
      rw [map_sub, map_smul, smul_eq_mul] at hz
      exact sub_eq_zero.mp hz
    obtain ⟨z, rfl⟩ := huniq l hL
    exact (J.ker.mem_dualAnnihilator _).mpr fun w hw ↦ by
      change z * J w = 0
      rw [LinearMap.mem_ker.mp hw, mul_zero]
  · intro l hl
    exact (D.mem_dualAnnihilator _).mpr fun w hw ↦ (J.ker.mem_dualAnnihilator _).mp hl _ (hD hw)


private theorem archNuclearity_weightedDifference
    (χ : PontryaginDual C𝔽) (hω : ω(χ) = 1)
    (i : ArchTests →L[ℂ] ℂ) (j : FiniteTests →ₗ[ℂ] ℂ) (b₀ : FiniteTests)
    (hb₀ : j b₀ = 1) (hL : ∀ a b, hatC (tensor (a ⊗ₜ[ℂ] b)) = i a * j b)
    (hi : ∀ (a : ArchTests) (h : Flat), (∀ z, a (Multiplicative.ofAdd z) = h.val (coord z)) →
      (i a = 0 ↔ (∫ y : Coord, h.val y) = 0))
    (a : ArchTests) (ha : a ∈ Aflat) (b : FiniteTests) (v : AFˣ) :
    tensor (a ⊗ₜ[ℂ] (schwartzBruhatUnitTranslate v b - absValue(archNuclearity_finiteUnit v) • b)) ∈
      A₀(χ) ⊔ K(χ) := by
  obtain ⟨u, hu⟩ := archNuclearity_archLift v
  let c := absValue(archNuclearity_finiteUnit v)
  let a' := schwartzBruhatUnitTranslate u a - c • a
  have ha' : a' ∈ Aflat :=
    Submodule.sub_mem _ (archNuclearity_flatFactors_translate u a ha) (Submodule.smul_mem _ _ ha)
  have hia : i a' = 0 := by
    change i (schwartzBruhatUnitTranslate u a - c • a) = 0
    rw [map_sub, map_smul, archNuclearity_moment_arch_translate i j b₀ hb₀ hL, hu, smul_eq_mul, sub_self]
  let p := tensor (a' ⊗ₜ[ℂ] b)
  have hp : p ∈ A₀(χ) := by
    obtain ⟨h, hh⟩ := ha'
    exact Submodule.subset_span ⟨a', b, h, hh, fun _ ↦ (hi a' h hh).mp hia, rfl⟩
  let q := tensor (a ⊗ₜ[ℂ] (schwartzBruhatUnitTranslate v b - c • b))
  have hq : q - p ∈ K(χ) := by
    let M := homogeneousAdelicThetaLinearMap F (ω(χ))
    have htheta := archNuclearity_theta_translate_sameNorm χ hω
      (archNuclearity_finiteUnit v) (archNuclearity_archUnit u) hu.symm
      (tensor (a ⊗ₜ[ℂ] b))
    have htF := archNuclearity_translate_pure (1 : A∞ˣ) v a b
    have htA := archNuclearity_translate_pure u (1 : AFˣ) a b
    rw [archNuclearity_translate_one, show archNuclearity_archUnit (F := F) 1 = 1 from Units.ext rfl,
      one_mul] at htF
    rw [archNuclearity_translate_one, show archNuclearity_finiteUnit (F := F) 1 = 1 from Units.ext rfl,
      mul_one] at htA
    let H := M.comp (tensor).toLinearMap
    have he : H (a ⊗ₜ[ℂ] schwartzBruhatUnitTranslate v b) =
        H (schwartzBruhatUnitTranslate u a ⊗ₜ[ℂ] b) :=
      ((congrArg M htF).symm.trans htheta).trans (congrArg M htA)
    have heq : M q = M p := by
      change H (a ⊗ₜ[ℂ] (schwartzBruhatUnitTranslate v b - c • b)) =
        H ((schwartzBruhatUnitTranslate u a - c • a) ⊗ₜ[ℂ] b)
      rw [TensorProduct.tmul_sub, TensorProduct.sub_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      exact (map_sub H _ _).trans ((congrArg (· - H ((c • a) ⊗ₜ[ℂ] b)) he).trans
        (map_sub H _ _).symm)
    exact (map_sub M q p).trans (sub_eq_zero.mpr heq)
  refine Submodule.mem_sup.mpr ⟨p, hp, q - p, hq, ?_⟩
  change p + (q - p) = q
  rw [add_comm, sub_add_cancel]

private theorem archNuclearity_discard_massZero
    (χ : PontryaginDual C𝔽) (hω : ω(χ) = 1)
    (hcont : ∀ L : FiniteTests →ₗ[ℂ] ℂ, Continuous L)
    (i : ArchTests →L[ℂ] ℂ) (j : FiniteTests →ₗ[ℂ] ℂ) (a₀ : ArchTests) (b₀ : FiniteTests)
    (ha₀ : i a₀ ≠ 0) (hb₀ : j b₀ = 1) (hL : ∀ a b, hatC (tensor (a ⊗ₜ[ℂ] b)) = i a * j b)
    (hi : ∀ (a : ArchTests) (h : Flat), (∀ z, a (Multiplicative.ofAdd z) = h.val (coord z)) →
      (i a = 0 ↔ (∫ y : Coord, h.val y) = 0))
    (a : ArchTests) (ha : a ∈ Aflat) (b : FiniteTests) (hb : j b = 0) :
    tensor (a ⊗ₜ[ℂ] b) ∈ A₀(χ) ⊔ K(χ) := by
  let wt := fun v : AFˣ ↦ absValue(archNuclearity_finiteUnit v)
  have heq := span_weightedDifferences_eq_ker (schwartzBruhatUnitTranslate (R := AF)) wt j
    (archNuclearity_moment_finite_translate i j a₀ ha₀ hL)
    (archNuclearity_finiteEigen_unique hcont i j a₀ b₀ ha₀ hb₀ hL)
  let M : FiniteTests →ₗ[ℂ] ℬ(𝔸[F]) := (tensor).toLinearMap.comp (TensorProduct.mk ℂ ArchTests FiniteTests a)
  have H : Submodule.span ℂ {x | ∃ u w, x = schwartzBruhatUnitTranslate u w - wt u • w} ≤
      (A₀(χ) ⊔ K(χ)).comap M := by
    apply Submodule.span_le.mpr
    rintro _ ⟨u, w, rfl⟩
    exact archNuclearity_weightedDifference χ hω i j b₀ hb₀ hL hi a ha w u
  exact (heq ▸ H) hb

/-- Transport the finest topology of the empty tail without changing the
representation of the finite adelic test functions. -/
private theorem archNuclearity_finiteFunctionals_continuous (L : FiniteTests →ₗ[ℂ] ℂ) :
    Continuous L := by
  obtain ⟨e, he, _⟩ := finiteAdeleTail_empty F
  let : Fact (∀ w : {w : V // w ∉ (∅ : Finset V)},
      IsOpen (w.val.adicCompletionIntegers F : Set (w.val.adicCompletion F))) :=
    ⟨fun w ↦ Valued.isOpen_valuationSubring (w.val.adicCompletion F)⟩
  let : IsTopologicalRing (FiniteAdeleTail F ∅) := RestrictedProduct.isTopologicalRing _
  let : IsTopologicalGroup (Multiplicative (FiniteAdeleTail F ∅)) := inferInstance
  let d : Multiplicative (FiniteAdeleTail F ∅) ≃ₜ* Multiplicative AF :=
    ⟨e.toAddEquiv.toMultiplicative, he.continuous, he.homeomorph.symm.continuous.congr
      fun x ↦ e.injective (he.homeomorph.apply_symm_apply x |>.trans (e.apply_symm_apply x).symm)⟩
  let (v : V) : CompactSpace (v.adicCompletionIntegers F) := compactSpace_adicCompletionIntegers v
  let (v : V) : LocallyCompactSpace (v.adicCompletion F) := locallyCompactSpace_adicCompletion v
  let : Fact (∀ v : V, IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
  let : T2Space (Multiplicative AF) := inferInstanceAs
    (T2Space (Πʳ w : V, [w.adicCompletion F, w.adicCompletionIntegers F]))
  let : LocallyCompactSpace (Multiplicative AF) := inferInstanceAs
    (LocallyCompactSpace (Πʳ w : V, [w.adicCompletion F, w.adicCompletionIntegers F]))
  let : T2Space (Multiplicative (FiniteAdeleTail F ∅)) := d.toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace (Multiplicative (FiniteAdeleTail F ∅)) :=
    d.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  obtain ⟨T, hT⟩ := schwartzBruhat_transport d
  obtain ⟨S, hS⟩ := schwartzBruhat_transport d.symm
  let W := ℬ(FiniteAdeleTail F ∅)
  let Q : W →ₗ[ℂ] ℂ := L.comp T.toLinearMap
  have ht := (finiteProduct_tailSchwartz_finestTopology F ∅ ∅).2
  have hQ : Continuous Q :=
    Eq.mpr (congrArg (fun t : TopologicalSpace W ↦ @Continuous W ℂ t _ Q) ht)
      (continuous_of_finestLocallyConvex W Q)
  have hinv (f : FiniteTests) : T (S f) = f := by
    apply Subtype.ext
    funext x
    change T (S f) x = f x
    rw [hT, hS, ContinuousMulEquiv.symm_symm, d.apply_symm_apply]
  exact (hQ.comp S.continuous).congr fun f ↦ congrArg L (hinv f)

/-- Paper: Equations (7.4.3.1) and (7.4.3.12), pp. 368 and 371.
In the homogeneous theta image the factorwise moment condition agrees with
imposing the two global polar conditions on the unrestricted flat tensors. -/
theorem mem_archNuclearityDenominator_iff_flatPolarImage (x : Θ₀(χ)) :
    x ∈ archNuclearityDenominator χ ↔
      ∃ f : P, f.val ∈ globalArchimedeanFlatTests F ∧ x = mkΘ(χ, f) := by
  refine archNuclearity_of_finiteMassReduction χ x fun hω ↦ ?_
  obtain ⟨i, j, a₀, b₀, ha₀, hb₀, hL, hi⟩ := archNuclearity_normalized_moment (F := F)
  exact ⟨i.toLinearMap, j, b₀, hb₀, hL, hi,
    archNuclearity_discard_massZero χ hω archNuclearity_finiteFunctionals_continuous
      i j a₀ b₀ ha₀ hb₀ hL hi⟩

end FlatPolarImage

/-- Paper: Equation (7.4.3.13), p. 372.
The archimedean orbital quotient divides the zero-moment theta space by its flat image.

This is a `def` with its own instances, not an `abbrev`, so that instance terms over it do
not spell out its definition (#5398). -/
def ArchNuclearityQuotient := Θ₀(χ) ⧸ archNuclearityDenominator χ

namespace ArchNuclearityQuotient

instance instAddCommGroup : AddCommGroup (ArchNuclearityQuotient χ) :=
  inferInstanceAs (AddCommGroup (Θ₀(χ) ⧸ archNuclearityDenominator χ))

instance instModule : Module ℂ (ArchNuclearityQuotient χ) :=
  inferInstanceAs (Module ℂ (Θ₀(χ) ⧸ archNuclearityDenominator χ))

instance instTopologicalSpace : TopologicalSpace (ArchNuclearityQuotient χ) :=
  inferInstanceAs (TopologicalSpace (Θ₀(χ) ⧸ archNuclearityDenominator χ))

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (ArchNuclearityQuotient χ) :=
  inferInstanceAs (IsTopologicalAddGroup (Θ₀(χ) ⧸ archNuclearityDenominator χ))

instance instContinuousSMul : ContinuousSMul ℂ (ArchNuclearityQuotient χ) :=
  inferInstanceAs (ContinuousSMul ℂ (Θ₀(χ) ⧸ archNuclearityDenominator χ))

end ArchNuclearityQuotient

/-- Paper: Equation (7.4.3.13), p. 372.
A test represents zero in the archimedean quotient exactly when its theta class
has an archimedean-flat zero-moment representative. -/
theorem archNuclearityQuotient_mk_eq_zero (f : P) :
    (archNuclearityDenominator χ).mkQ mkΘ(χ, f) = 0 ↔
      ∃ g : P, g.val ∈ globalArchimedeanFlatTests F (ω(χ) = 1) ∧ mkΘ(χ, g) = mkΘ(χ, f) := by
  let A : Submodule ℂ P := (globalArchimedeanFlatTests F (ω(χ) = 1)).comap (P).subtype
  let q : P →ₗ[ℂ] Θ₀(χ) := (Π(χ)).mkQ
  have hle : archNuclearityDenominator χ ≤ A.map q :=
    Submodule.span_le.mpr (by
      rintro _ ⟨g, hg, rfl⟩
      exact ⟨g, hg, rfl⟩)
  constructor
  · intro hf
    exact hle ((Submodule.Quotient.mk_eq_zero (archNuclearityDenominator χ)).mp hf)
  · rintro ⟨g, hg, he⟩
    exact (Submodule.Quotient.mk_eq_zero (archNuclearityDenominator χ)).mpr
      (Submodule.subset_span ⟨g, hg, he.symm⟩)

-- The finite factors of (7.4.3.6) on p. 369 also carry their integer-unit
-- Tamagawa masses. A positive archimedean bump on the trivial isotype needs a
-- difference of dilates to give zero additive integral.

-- Theorem 7.4.3.1(1) (`archNuclearityDenominator_nonzero_closed`) is stated below,
-- after the jet coordinate equivalence, because its closedness half is proved from it.

local notation "gammaOrder(" χ ", " s ")" =>
  (analyticOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) s).toNat
local notation "atZeroPole(" χ ", " τ ", " hτ ")" =>
  (-(((existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose : ℝ) : ℂ) * Complex.I)

/-- Paper: Equations (7.4.3.2)–(7.4.3.3), p. 368.
In the fixed norm chart the archimedean pole set is the zero set of the reciprocal gamma
product. The pole set in that chart is discrete and closed. -/
theorem archNuclearityPoleSet_discrete :
    let S := {s : ℂ | 0 < gammaOrder(χ, s)}
    IsClosed S ∧ IsDiscrete S := by
  apply compl_mem_codiscrete_iff.mp
  have ha : AnalyticOnNhd ℂ (fun z ↦ (heckeGammaFactor χ z)⁻¹) univ :=
    fun z _ ↦ (differentiable_inv_heckeGammaFactor χ).analyticAt z
  filter_upwards [ha.codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top] with z hz
  rcases hz with hz | hz <;> simp [Set.mem_compl_iff, hz]

/-- Paper: Equations (7.4.3.2)–(7.4.3.3), p. 368.
The raw order in the global chart counts the same places as the local
multiplicity of Proposition 5.3.4.5 for the restricted character. -/
theorem archNuclearityGammaOrder_eq_sLocal (S : Finset V)
    (η : PontryaginDual (SIdeleQuotient F S))
    (h : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (_hη : sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, h⟩ =
      (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η) (s : ℂ) :
    gammaOrder(χ, s) = sLocalArchimedeanPoleMultiplicity η s := by
  classical
  let c : ℂ → QuasiCharacter (SIdeleQuotient F S) := fun z ↦
    quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous
      ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η) z
  let E : InfinitePlace F → ℂ → ℂ := fun w z ↦
    infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (c z))
  -- The chart through `η` evaluates the global twist on inserted S-ideles.
  have htwist (z : ℂ) (g : (SAdeleRing F S)ˣ) :
      c z (QuotientGroup.mk g) =
        ideleClassNormTwist χ z (QuotientGroup.mk (sIdeleInsertion F S g)) := by
    have hbase := DFunLike.congr_fun _hη (QuotientGroup.mk g)
    rw [sIdeleRestriction_mk] at hbase
    change (χ (QuotientGroup.mk (sIdeleInsertion F S g)) : ℂ) * _ ^ (0 : ℂ) =
      (η (QuotientGroup.mk g) : ℂ) at hbase
    simp only [Complex.cpow_zero, mul_one] at hbase
    change (η (QuotientGroup.mk g) : ℂ) *
        (((sIdeleQuotientNorm F S (QuotientGroup.mk g) : ℝ≥0) : ℝ) : ℂ) ^ z =
      (χ (QuotientGroup.mk (sIdeleInsertion F S g)) : ℂ) * _ ^ z
    rw [← hbase, sIdeleQuotientNorm_mk, ← ideleNorm_sIdeleInsertion]
    rfl
  have hinf (w : InfinitePlace F) (z : ℂ) : sLocalInfiniteRestriction w (c z) =
      infinitePlaceRestriction F w (ideleClassNormTwist χ z) := by
    ext1 x
    refine (htwist z _).trans ?_
    rw [sIdeleInsertion_infiniteUnit]
    rfl
  have hprod : (fun z ↦ heckeGammaFactor χ z) = ∏ w, E w := by
    funext z
    rw [Finset.prod_apply, ← prod_infiniteLocalEulerFactor_eq_heckeGammaFactor]
    simp only [E, hinf]
  -- Each local factor is a translate of a gamma factor, with entire reciprocal.
  have hEinv (w : InfinitePlace F) : Differentiable ℂ fun z ↦ (E w z)⁻¹ := by
    by_cases hw : w.IsReal
    · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_real η w hw
      simp only [E, c, hb]
      exact Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const b)
    · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_complex η w
        (InfinitePlace.not_isReal_iff_isComplex.mp hw)
      simp only [E, c, hb]
      convert (Complex.differentiable_Gammaℂ_inv.comp (differentiable_id.add_const b)).const_mul
        (2 : ℂ) using 1
      funext z
      rw [inv_div, div_eq_mul_inv]
      rfl
  have hEval (w : InfinitePlace F) : ∃ z₁, (E w z₁)⁻¹ ≠ 0 := by
    by_cases hw : w.IsReal
    · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_real η w hw
      refine ⟨1 - b, ?_⟩
      simp only [E, c, hb, sub_add_cancel]
      exact inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num))
    · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_complex η w
        (InfinitePlace.not_isReal_iff_isComplex.mp hw)
      refine ⟨1 - b, ?_⟩
      simp only [E, c, hb, sub_add_cancel]
      simp [Complex.Gammaℂ_def, Real.pi_ne_zero]
  have hmer (w : InfinitePlace F) : MeromorphicAt (E w) s := by
    convert ((hEinv w).analyticAt s).meromorphicAt.inv using 1
    funext z
    simp
  have hntop (w : InfinitePlace F) : meromorphicOrderAt (E w) s ≠ ⊤ := by
    intro htop
    have h1 : meromorphicOrderAt (fun z ↦ (E w z)⁻¹) s = ⊤ := by
      rw [show meromorphicOrderAt (fun z ↦ (E w z)⁻¹) s = -meromorphicOrderAt (E w) s from
        meromorphicOrderAt_inv, htop]
      rfl
    rw [((hEinv w).analyticAt s).meromorphicOrderAt_eq] at h1
    have h2 : analyticOrderAt (fun z ↦ (E w z)⁻¹) s = ⊤ := by
      cases hn : analyticOrderAt (fun z ↦ (E w z)⁻¹) s with
      | top => rfl
      | coe n => rw [hn] at h1; simp at h1
    have hA : AnalyticOnNhd ℂ (fun z ↦ (E w z)⁻¹) univ := fun z _ ↦ (hEinv w).analyticAt z
    obtain ⟨z₁, hz₁⟩ := hEval w
    exact hz₁ (hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ s) (analyticOrderAt_eq_top.1 h2) (mem_univ z₁))
  have hle (w : InfinitePlace F) : meromorphicOrderAt (E w) s ≤ 0 := by
    have h0 := ((hEinv w).analyticAt s).meromorphicOrderAt_nonneg
    rw [show meromorphicOrderAt (fun z ↦ (E w z)⁻¹) s = -meromorphicOrderAt (E w) s from
      meromorphicOrderAt_inv] at h0
    cases hn : meromorphicOrderAt (E w) s with
    | top => exact absurd hn (hntop w)
    | coe n =>
      rw [hn] at h0
      have h0' : (0 : ℤ) ≤ -n := by exact_mod_cast h0
      exact_mod_cast (by omega : n ≤ 0)
  have key := sLocalArchimedeanPoleMultiplicity_eq_sum η s
  have hG : meromorphicOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) s =
      ((sLocalArchimedeanPoleMultiplicity η s : ℤ) : WithTop ℤ) := by
    rw [show meromorphicOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) s =
        -meromorphicOrderAt (fun z ↦ heckeGammaFactor χ z) s from meromorphicOrderAt_inv,
      hprod, meromorphicOrderAt_prod fun w _ ↦ hmer w,
      Finset.sum_congr rfl fun w _ ↦ (min_eq_right (hle w)).symm]
    change -(∑ w, min 0 (meromorphicOrderAt (fun z ↦ infiniteLocalEulerFactor w
      (sLocalInfiniteRestriction w (c z))) s)) = _
    rw [← key]
    exact_mod_cast neg_neg (sLocalArchimedeanPoleMultiplicity η s : ℤ)
  rw [((differentiable_inv_heckeGammaFactor χ).analyticAt s).meromorphicOrderAt_eq] at hG
  cases hn : analyticOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) s with
  | top => rw [hn] at hG; simp at hG
  | coe n =>
    rw [hn] at hG
    have hn' : (n : ℤ) = (sLocalArchimedeanPoleMultiplicity η s : ℤ) := by simpa using hG
    simpa using hn'

/-- The reciprocal Gamma function vanishes to order at most one everywhere, by the
recursion `1/Γ(s) = s · 1/Γ(s + 1)`. -/
private theorem archNuclearity_trace_gammaInv_order_le (w : ℂ) :
    analyticOrderAt (fun s ↦ (Complex.Gamma s)⁻¹) w ≤ 1 := by
  have han (z : ℂ) : AnalyticAt ℂ (fun s ↦ (Complex.Gamma s)⁻¹) z :=
    Complex.differentiable_one_div_Gamma.analyticAt z
  by_cases hw : (Complex.Gamma w)⁻¹ = 0
  · obtain ⟨n, rfl⟩ := (Complex.Gamma_eq_zero_iff w).mp (inv_eq_zero.mp hw)
    induction n with
    | zero =>
      have hrec : (fun s ↦ (Complex.Gamma s)⁻¹) =
          (fun s : ℂ ↦ s - 0) * ((fun s ↦ (Complex.Gamma s)⁻¹) ∘ (fun s : ℂ ↦ s + 1)) := by
        funext s
        simp [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one s]
      rw [hrec, analyticOrderAt_mul (by fun_prop) ((han _).comp (by fun_prop)),
        analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp)]
      simp only [Nat.cast_zero, neg_zero]
      rw [analyticOrderAt_id_sub_const_self, zero_add,
        ((han 1).analyticOrderAt_eq_zero).mpr (by simp)]
      simp
    | succ n ih =>
      have hrec : (fun s ↦ (Complex.Gamma s)⁻¹) =
          (fun s : ℂ ↦ s) * ((fun s ↦ (Complex.Gamma s)⁻¹) ∘ (fun s : ℂ ↦ s + 1)) := by
        funext s
        simp [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one s]
      rw [hrec, analyticOrderAt_mul (by fun_prop) ((han _).comp (by fun_prop)),
        analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp)]
      have h0 : analyticOrderAt (fun s : ℂ ↦ s) (-((n + 1 : ℕ) : ℂ)) = 0 :=
        (analyticAt_id.analyticOrderAt_eq_zero).mpr (by
          show -(((n + 1 : ℕ) : ℂ)) ≠ 0
          rw [neg_ne_zero, Nat.cast_ne_zero]
          exact Nat.succ_ne_zero n)
      have h1 : -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) := by push_cast; ring
      rw [h0, zero_add, h1]
      exact ih (by
        rw [inv_eq_zero]
        exact Complex.Gamma_neg_nat_eq_zero n)
  · rw [((han w).analyticOrderAt_eq_zero).mpr hw]
    exact zero_le

/-- A nonvanishing analytic factor times the reciprocal Gamma function at an affine
argument vanishes to order at most one. -/
private theorem archNuclearity_trace_affine_order_le (u : ℂ → ℂ) (a c z : ℂ) (ha : a ≠ 0)
    (hu : AnalyticAt ℂ u z) (hu0 : u z ≠ 0) :
    analyticOrderAt (fun s ↦ u s * (Complex.Gamma (a * s + c))⁻¹) z ≤ 1 := by
  have hg : AnalyticAt ℂ (fun s : ℂ ↦ a * s + c) z := by fun_prop
  have hΓ : AnalyticAt ℂ ((fun s ↦ (Complex.Gamma s)⁻¹) ∘ (fun s : ℂ ↦ a * s + c)) z :=
    (Complex.differentiable_one_div_Gamma.analyticAt _).comp hg
  change analyticOrderAt (u * ((fun s ↦ (Complex.Gamma s)⁻¹) ∘ (fun s : ℂ ↦ a * s + c))) z ≤ 1
  rw [analyticOrderAt_mul hu hΓ, (hu.analyticOrderAt_eq_zero).mpr hu0, zero_add,
    analyticOrderAt_comp_of_deriv_ne_zero hg (by
      rw [deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'']
      simpa using ha)]
  exact archNuclearity_trace_gammaInv_order_le _

/-- The reciprocal of an archimedean Gamma factor is entire, vanishes to order at most
one, and vanishes only at `-c - k` for natural `k`. -/
private theorem archNuclearity_trace_factor (f : ℂ → ℂ) (c : ℂ)
    (hf : (∀ s, f s = Complex.Gammaℝ (s + c)) ∨ (∀ s, f s = Complex.Gammaℂ (s + c) / 2))
    (z : ℂ) :
    AnalyticAt ℂ (fun s ↦ (f s)⁻¹) z ∧ analyticOrderAt (fun s ↦ (f s)⁻¹) z ≤ 1 ∧
      ((f z)⁻¹ = 0 → ∃ k : ℕ, z = -c - k) := by
  rcases hf with hf | hf
  · have he : (fun s ↦ (f s)⁻¹) = fun s ↦ ((Real.pi : ℂ) ^ (-(s + c) / 2))⁻¹ *
        (Complex.Gamma ((1 / 2 : ℂ) * s + c / 2))⁻¹ := by
      funext s
      rw [hf, Complex.Gammaℝ_def, mul_inv, show (s + c) / 2 = 1 / 2 * s + c / 2 by ring]
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hu : Differentiable ℂ fun s : ℂ ↦ ((Real.pi : ℂ) ^ (-(s + c) / 2))⁻¹ :=
      fun s ↦ ((((differentiable_id.add_const c).neg.div_const 2) s).const_cpow
        (Or.inl hπ)).inv (Complex.cpow_ne_zero_iff.mpr (Or.inl hπ))
    refine ⟨?_, ?_, fun h0 ↦ ?_⟩
    · rw [he]
      exact (hu.analyticAt z).mul ((Complex.differentiable_one_div_Gamma.analyticAt _).comp
        (by fun_prop))
    · rw [he]
      exact archNuclearity_trace_affine_order_le _ _ _ z (by norm_num) (hu.analyticAt z)
        (inv_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hπ)))
    · rw [hf] at h0
      obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp (inv_eq_zero.mp h0)
      exact ⟨2 * n, by push_cast; linear_combination hn⟩
  · have he : (fun s ↦ (f s)⁻¹) = fun s ↦ (2 * (2 * (2 * Real.pi : ℂ) ^ (-(s + c)))⁻¹) *
        (Complex.Gamma (1 * s + c))⁻¹ := by
      funext s
      rw [hf, Complex.Gammaℂ_def, one_mul]
      simp only [div_eq_mul_inv, mul_inv, inv_inv]
      ring
    have h2π : (2 * Real.pi : ℂ) ≠ 0 :=
      mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    have hpow (s : ℂ) : (2 * Real.pi : ℂ) ^ (-(s + c)) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl h2π)
    have hu : Differentiable ℂ fun s : ℂ ↦ 2 * (2 * (2 * Real.pi : ℂ) ^ (-(s + c)))⁻¹ :=
      fun s ↦ ((((differentiable_id.add_const c).neg s).const_cpow (Or.inl h2π)).const_mul
        2).inv (mul_ne_zero two_ne_zero (hpow s)) |>.const_mul 2
    refine ⟨?_, ?_, fun h0 ↦ ?_⟩
    · rw [he]
      exact (hu.analyticAt z).mul ((Complex.differentiable_one_div_Gamma.analyticAt _).comp
        (by fun_prop))
    · rw [he]
      exact archNuclearity_trace_affine_order_le _ _ _ z one_ne_zero (hu.analyticAt z)
        (mul_ne_zero two_ne_zero (inv_ne_zero (mul_ne_zero two_ne_zero (hpow z))))
    · rw [hf, inv_eq_zero, div_eq_zero_iff, Complex.Gammaℂ_def] at h0
      have hΓ : Complex.Gamma (z + c) = 0 := by
        rcases h0 with h0 | h0
        · rcases mul_eq_zero.mp h0 with h | h
          · exact absurd h (mul_ne_zero two_ne_zero (hpow z))
          · exact h
        · exact absurd h0 two_ne_zero
      obtain ⟨n, hn⟩ := (Complex.Gamma_eq_zero_iff _).mp hΓ
      exact ⟨n, by linear_combination hn⟩

/-- The reciprocal of a finite product of archimedean Gamma factors vanishes to order at
most the number of factors, and only at points `-c i - k`. -/
private theorem archNuclearity_trace_prod {ι : Type*} [Fintype ι] (f : ι → ℂ → ℂ)
    (c : ι → ℂ) (hf : ∀ i, (∀ s, f i s = Complex.Gammaℝ (s + c i)) ∨
      (∀ s, f i s = Complex.Gammaℂ (s + c i) / 2)) (z : ℂ) :
    analyticOrderAt (fun s ↦ (∏ i, f i s)⁻¹) z ≤ Fintype.card ι ∧
      ((∏ i, f i z)⁻¹ = 0 → ∃ i, ∃ k : ℕ, z = -c i - k) := by
  classical
  have hinv : (fun s ↦ (∏ i, f i s)⁻¹) = fun s ↦ ∏ i, (f i s)⁻¹ := by
    funext s
    rw [Finset.prod_inv_distrib]
  refine ⟨?_, fun h0 ↦ ?_⟩
  · rw [hinv, ← Finset.card_univ]
    have key : ∀ s : Finset ι, AnalyticAt ℂ (fun w ↦ ∏ i ∈ s, (f i w)⁻¹) z ∧
        analyticOrderAt (fun w ↦ ∏ i ∈ s, (f i w)⁻¹) z ≤ s.card := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        refine ⟨by simpa using analyticAt_const, ?_⟩
        simp only [Finset.prod_empty, Finset.card_empty, Nat.cast_zero]
        exact ((analyticAt_const).analyticOrderAt_eq_zero.mpr one_ne_zero).le
      | insert a s ha ih =>
        obtain ⟨hfa, hoa, -⟩ := archNuclearity_trace_factor (f a) (c a) (hf a) z
        have he : (fun w ↦ ∏ i ∈ insert a s, (f i w)⁻¹) =
            (fun w ↦ (f a w)⁻¹) * fun w ↦ ∏ i ∈ s, (f i w)⁻¹ := by
          funext w
          rw [Finset.prod_insert ha]
          rfl
        rw [he]
        refine ⟨hfa.mul ih.1, ?_⟩
        rw [analyticOrderAt_mul hfa ih.1, Finset.card_insert_of_notMem ha, Nat.cast_add,
          Nat.cast_one, add_comm (s.card : ℕ∞)]
        exact add_le_add hoa ih.2
    exact (key Finset.univ).2
  · rw [← Finset.prod_inv_distrib, Finset.prod_eq_zero_iff] at h0
    obtain ⟨i, -, hi⟩ := h0
    obtain ⟨k, hk⟩ := (archNuclearity_trace_factor (f i) (c i) (hf i) z).2.2 hi
    exact ⟨i, k, hk⟩

/-- The reciprocal archimedean gamma factor of `χ` vanishes to order at most the number of
infinite places, and only at points `-c v - k` with `k` a natural number. -/
private theorem archNuclearity_trace_gammaOrder :
    ∃ c : InfinitePlace F → ℂ, ∀ z : ℂ, gammaOrder(χ, z) ≤ Fintype.card (InfinitePlace F) ∧
      (0 < gammaOrder(χ, z) → ∃ v, ∃ k : ℕ, z = -c v - k) := by
  let G : InfinitePlace F → ℂ → ℂ := fun v s ↦ if hv : v.IsReal then
      Complex.Gammaℝ (s + (realHeckeCharacter_parameters χ v hv).exists.choose.1 +
        ((realHeckeCharacter_parameters χ v hv).exists.choose.2.val : ℂ))
    else Complex.Gammaℂ (s + (complexHeckeCharacter_parameters χ v
        (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose.1 +
        ((complexHeckeCharacter_parameters χ v
          (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose.2.natAbs : ℂ) / 2) / 2
  let c : InfinitePlace F → ℂ := fun v ↦ if hv : v.IsReal then
      (realHeckeCharacter_parameters χ v hv).exists.choose.1 +
        ((realHeckeCharacter_parameters χ v hv).exists.choose.2.val : ℂ)
    else (complexHeckeCharacter_parameters χ v
        (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose.1 +
        ((complexHeckeCharacter_parameters χ v
          (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose.2.natAbs : ℂ) / 2
  have hG (s : ℂ) : heckeGammaFactor χ s = ∏ v, G v s := by
    unfold heckeGammaFactor
    rfl
  have hc (v : InfinitePlace F) : (∀ s, G v s = Complex.Gammaℝ (s + c v)) ∨
      (∀ s, G v s = Complex.Gammaℂ (s + c v) / 2) := by
    by_cases hv : v.IsReal
    · exact Or.inl fun s ↦ by simp only [G, c, hv, ↓reduceDIte, add_assoc]
    · exact Or.inr fun s ↦ by simp only [G, c, hv, ↓reduceDIte, add_assoc]
  refine ⟨c, fun z ↦ ?_⟩
  have hfun : (fun s ↦ (heckeGammaFactor χ s)⁻¹) = fun s ↦ (∏ v, G v s)⁻¹ :=
    funext fun s ↦ by rw [hG]
  obtain ⟨hord, hzero⟩ := archNuclearity_trace_prod G c hc z
  have han := (differentiable_inv_heckeGammaFactor χ).analyticAt z
  constructor
  · rw [hfun]
    cases h : analyticOrderAt (fun s ↦ (∏ v, G v s)⁻¹) z with
    | top => simp
    | coe n =>
      rw [h] at hord
      simpa using hord
  · intro hpos
    apply hzero
    rw [← hG]
    by_contra hne
    rw [(han.analyticOrderAt_eq_zero).mpr hne] at hpos
    simp at hpos

/-- Paper: Theorem 7.4.3.1(2), p. 368.
The raw total pole order is reduced by one at the trivial quasi-character,
when it lies on the chosen component.
Deviation: Page 368 names the quasi-character |·|^(it₀). The chart parameter it₀
corresponds to the trivial quasi-character when χ = |·|^(−it₀). -/
def archNuclearityMultiplicity (s : ℂ) : ℕ :=
  gammaOrder(χ, s) - if ω(χ) = 1 ∧ s = atZeroPole(χ, τ, hτ) then 1 else 0

/-- Paper: Theorem 7.4.3.1(2), p. 368.
For the trivial rational character, the adjusted order at zero vanishes and the
simple gamma pole at minus two remains. -/
theorem archNuclearityMultiplicity_rat_one
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 ℚ) ℚ) (hτ : RightInverse τ (ideleNorm ℚ)) :
    archNuclearityMultiplicity (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) τ hτ 0 = 0 ∧
      archNuclearityMultiplicity (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) τ hτ (-2) = 1 :=
  by
  have hphase := existsUnique_ideleNormSection_character_phase
    (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) τ hτ
  have hx : hphase.exists.choose = 0 :=
    hphase.unique hphase.exists.choose_spec fun t ↦ by simp
  have hω : (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)).comp
      (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ :
        (ideleClassNorm ℚ).ker →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ) = 1 :=
    ContinuousMonoidHom.ext fun _ ↦ rfl
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hπz (z : ℂ) : (Real.pi : ℂ) ^ (z / 2) ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hπ)
  have hG (z : ℂ) : (heckeGammaFactor (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) z)⁻¹ =
      (Real.pi : ℂ) ^ (z / 2) * (z / 2 * ((z / 2 + 1) * (Complex.Gamma (z / 2 + 1 + 1))⁻¹)) := by
    rw [heckeGammaFactor_one,
      InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one (Module.finrank_self ℚ),
      InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ),
      pow_one, pow_zero, mul_one, Complex.Gammaℝ, mul_inv, neg_div, Complex.cpow_neg, inv_inv,
      Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one,
      Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (z / 2 + 1)]
  have hpow : Differentiable ℂ fun z : ℂ ↦ (Real.pi : ℂ) ^ (z / 2) :=
    (differentiable_id.div_const 2).const_cpow (Or.inl hπ)
  have hΓ : Differentiable ℂ fun z : ℂ ↦ (Complex.Gamma (z / 2 + 1 + 1))⁻¹ :=
    Complex.differentiable_one_div_Gamma.comp (by fun_prop)
  have hf : Differentiable ℂ fun z ↦
      (heckeGammaFactor (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) z)⁻¹ := by
    simp only [hG]
    exact hpow.mul ((differentiable_id.div_const 2).mul
      (((differentiable_id.div_const 2).add_const 1).mul hΓ))
  have hΓne (z : ℂ) (hz : 0 < z.re) : (Complex.Gamma z)⁻¹ ≠ 0 :=
    inv_ne_zero (Complex.Gamma_ne_zero_of_re_pos hz)
  have h0 : (analyticOrderAt (fun z ↦
      (heckeGammaFactor (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) z)⁻¹) 0).toNat = 1 := by
    rw [((hf.analyticAt 0).analyticOrderAt_eq_natCast (n := 1)).2 ⟨fun z ↦
      (Real.pi : ℂ) ^ (z / 2) * (1 / 2 * ((z / 2 + 1) * (Complex.Gamma (z / 2 + 1 + 1))⁻¹)),
      (hpow.mul ((differentiable_const _).mul
        (((differentiable_id.div_const 2).add_const 1).mul hΓ))).analyticAt 0, ?_,
      Filter.Eventually.of_forall fun z ↦ ?_⟩]
    · rfl
    · refine mul_ne_zero (hπz 0) (mul_ne_zero (by norm_num) (mul_ne_zero (by norm_num)
        (hΓne _ (by norm_num))))
    · rw [hG, smul_eq_mul]
      ring
  have h2 : (analyticOrderAt (fun z ↦
      (heckeGammaFactor (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) z)⁻¹) (-2)).toNat = 1 := by
    rw [((hf.analyticAt (-2)).analyticOrderAt_eq_natCast (n := 1)).2 ⟨fun z ↦
      (Real.pi : ℂ) ^ (z / 2) * (z / 2 * (1 / 2 * (Complex.Gamma (z / 2 + 1 + 1))⁻¹)),
      (hpow.mul ((differentiable_id.div_const 2).mul
        ((differentiable_const _).mul hΓ))).analyticAt (-2), ?_,
      Filter.Eventually.of_forall fun z ↦ ?_⟩]
    · rfl
    · refine mul_ne_zero (hπz _) (mul_ne_zero (by norm_num) (mul_ne_zero (by norm_num)
        (hΓne _ (by norm_num))))
    · rw [hG, smul_eq_mul]
      ring
  refine ⟨?_, ?_⟩ <;> unfold archNuclearityMultiplicity
  · rw [h0, hx]
    simp [hω]
  · rw [h2, hx]
    simp

/-- Paper: Theorem 7.4.3.1(2), p. 368.
Each pole contributes derivative indices from zero up to its adjusted order. -/
abbrev ArchNuclearityJetIndex := {j : ℂ × ℕ // j.2 < archNuclearityMultiplicity χ τ hτ j.1}

/-- Paper: Equation (7.4.3.4), p. 368.
The orbital jet applies a continuous entire derivative to the Mellin transform of
a zero-moment theta class. -/
def archNuclearityJet (j : ArchNuclearityJetIndex χ τ hτ) : StrongDual ℂ (Θ₀(χ)) :=
  ((entireJet j.val.1 j.val.2).comp schwartzBergmanEntireInclusion).comp (Z(χ, τ, hτ))

section AdjustedJetRealization

local notation "completedGenerator" => regularizedCompletedHeckeL χ τ hτ
  (continuedCompletedHeckeL χ) (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2

/-- Reflection preserves the meromorphic order. The inverse character has no zero
at or to the right of the line of absolute convergence. -/
private theorem archJet_completed_order_nonpos {s : ℂ} (hs : s.re ≤ 0) :
    meromorphicOrderAt (continuedCompletedHeckeL χ) s ≤ 0 := by
  obtain ⟨ε, hε, hne, he⟩ := completedHeckeL_continuation_functionalEquation χ
    (continuedCompletedHeckeL χ) (continuedCompletedHeckeL χ⁻¹)
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
    (continuedCompletedHeckeL_spec χ⁻¹).1 (continuedCompletedHeckeL_spec χ⁻¹).2
  let r (z : ℂ) := 1 - z
  have hr : HasDerivAt r (-1) s := by simpa [r] using (hasDerivAt_id s).const_sub 1
  have e : continuedCompletedHeckeL χ⁻¹ ∘ r = fun z ↦ ε z * continuedCompletedHeckeL χ z :=
    funext he
  have ho := meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL χ⁻¹)
    (show AnalyticAt ℂ r s by dsimp [r]; fun_prop) (hr.deriv.trans_ne (by norm_num))
  rw [e] at ho
  change meromorphicOrderAt (ε * continuedCompletedHeckeL χ) s = _ at ho
  rw [meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt s) (hne s)] at ho
  rw [ho]
  have hright : 1 ≤ (r s).re := by change 1 ≤ 1 - s.re; linarith
  exact le_of_not_gt (fun hz ↦ (completedHeckeL_continuation_zeros χ⁻¹ _
    (continuedCompletedHeckeL_spec χ⁻¹).1 (continuedCompletedHeckeL_spec χ⁻¹).2
    (zero_lt_one.trans_le hright) hz).not_ge hright)

/-- The entire pole-removed factor is nonzero throughout the closed left half-plane. -/
private theorem archJet_regularized_nonzero {s : ℂ} (hs : s.re ≤ 0) : (completedGenerator).val s ≠ 0 := by
  classical
  let L := continuedCompletedHeckeL χ
  let b := (((existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose : ℝ) : ℂ) * Complex.I
  let δ : ℕ := if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0
  let polePolynomial (z : ℂ) := (z + b) ^ δ * (1 - z - b) ^ δ
  have hL := (continuedCompletedHeckeL_spec χ).1
  by_cases hcan : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 ∧ (s = -b ∨ s = 1 - b)
  · have hp := regularizedCompletedHeckeL_ne_zero_at_canceled_poles χ τ hτ L hL
      (continuedCompletedHeckeL_spec χ).2 hcan.1
    rcases hcan.2 with rfl | rfl
    · exact hp.1
    · exact hp.2
  have hP : polePolynomial s ≠ 0 := by
    by_cases htriv : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
    · have h := not_or.mp (fun hh ↦ hcan ⟨htriv,hh⟩)
      simp only [polePolynomial, δ, ite_eq_left htriv, pow_one]
      refine mul_ne_zero (fun hz ↦ h.1 (eq_neg_of_add_eq_zero_left hz)) ?_
      intro hz
      apply h.2
      linear_combination -hz
    · simp [polePolynomial, δ, htriv]
  have hPa (z : ℂ) : AnalyticAt ℂ polePolynomial z := by dsimp [polePolynomial]; fun_prop
  have hPL : MeromorphicOn (polePolynomial * L) univ := fun z hz ↦
    (hPa z).meromorphicAt.mul (hL hz).meromorphicAt
  have he : ((completedGenerator).val : ℂ → ℂ) = toMeromorphicNFOn (polePolynomial * L) univ := rfl
  have hor : meromorphicOrderAt ((completedGenerator).val : ℂ → ℂ) s = meromorphicOrderAt L s := by
    rw [he, meromorphicOrderAt_toMeromorphicNFOn hPL (mem_univ _),
      meromorphicOrderAt_mul_of_ne_zero (hPa s) hP]
  have ha := (completedGenerator).property.analyticAt s
  apply ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp
  exact le_antisymm (hor.trans_le (archJet_completed_order_nonpos χ hs)) ha.meromorphicOrderAt_nonneg

private theorem archJet_completed_nonzero (ρ : ℂ) (hρ : 0 < archNuclearityMultiplicity χ τ hτ ρ) :
    (completedGenerator).val ρ ≠ 0 := by
  apply archJet_regularized_nonzero χ τ hτ
  by_contra! hpos
  have hn := inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ hpos)
  have hzero := ((differentiable_inv_heckeGammaFactor χ).analyticAt ρ).analyticOrderAt_eq_zero.mpr hn
  simp [archNuclearityMultiplicity, hzero] at hρ

/-- Only finitely many adjusted gamma pole centres lie to the right of a given line.
The multiplicities are bounded by the number of infinite places. -/
private theorem archJet_support_finite :
    (∀ z, archNuclearityMultiplicity χ τ hτ z ≤ Fintype.card (InfinitePlace F)) ∧
      ∀ a : ℝ, {z : ℂ | 0 < archNuclearityMultiplicity χ τ hτ z ∧ a ≤ z.re}.Finite := by
  classical
  obtain ⟨c, hc⟩ := archNuclearity_trace_gammaOrder χ
  have hle (z : ℂ) : archNuclearityMultiplicity χ τ hτ z ≤ gammaOrder(χ, z) :=
    Nat.sub_le _ _
  refine ⟨fun z ↦ (hle z).trans (hc z).1, fun a ↦ ?_⟩
  choose N hN using fun v : InfinitePlace F ↦ exists_nat_gt (-(c v).re - a)
  let T (v : InfinitePlace F) := (fun k : ℕ ↦ -c v - (k : ℂ)) '' Iic (N v)
  have hT (v : InfinitePlace F) : (T v).Finite :=
    (finite_Iic (N v)).image (fun k : ℕ ↦ -c v - (k : ℂ))
  refine (finite_iUnion hT).subset fun z hz ↦ ?_
  obtain ⟨v, k, rfl⟩ := (hc z).2 (hz.1.trans_le (hle z))
  have hz' : a ≤ -(c v).re - (k : ℝ) := by
    simpa only [Complex.sub_re, Complex.neg_re, Complex.natCast_re] using hz.2
  have hk : (k : ℝ) < (N v : ℝ) := by linarith [hN v]
  exact mem_iUnion.mpr ⟨v, k, (by exact_mod_cast hk.le : k ≤ N v), rfl⟩

private theorem archJet_surjective :
    Function.Surjective (fun (x : Θ₀(χ)) j ↦ archNuclearityJet χ τ hτ j x) := by
  intro c
  obtain ⟨hord, hfin⟩ := archJet_support_finite χ τ hτ
  let d := Fintype.card (InfinitePlace F) + 1
  let L := continuedCompletedHeckeL χ
  obtain ⟨hL, hEq⟩ := continuedCompletedHeckeL_spec χ
  have hΛ : orbitalHeckeGenerator χ τ hτ L hL hEq ∅ = completedGenerator :=
    orbitalHeckeGenerator_empty χ τ hτ L hL hEq
  have hne (z : ℂ) (hz : 0 < archNuclearityMultiplicity χ τ hτ z) :
      (orbitalHeckeGenerator χ τ hτ L hL hEq ∅).val z ≠ 0 := by
    rw [hΛ]
    exact archJet_completed_nonzero χ τ hτ z hz
  obtain ⟨f, hf, hjet⟩ := orbitalSchwartzBergman_jetInterpolation χ τ hτ L hL hEq ∅
    (archNuclearityMultiplicity χ τ hτ) d (Nat.succ_pos _) (fun z ↦ (hord z).trans (Nat.le_succ _))
    hfin hne c
  rw [hΛ] at hf
  obtain ⟨x, hx⟩ := (mem_range_globalPolarThetaMellin_iff χ τ hτ f).2 ((mem_schwartzBergmanDivisible_iff _ f).1 hf)
  refine ⟨x, funext fun j ↦ ?_⟩
  change archNuclearityJet χ τ hτ j x = c j
  unfold archNuclearityJet
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, entireJet_apply, hx]
  have heq : ((schwartzBergmanEntireInclusion f).val : ℂ → ℂ) = f.val :=
    funext (schwartzBergmanEntireInclusion_apply f)
  rw [heq]
  exact hjet j

end AdjustedJetRealization

/-- Paper: Equation (7.4.3.4), p. 368.
On a representative the orbital jet is the derivative of the idelic zeta integral.
Its inverse Mellin formula is the convergent logarithmic moment.
Deviation: Uses the normalized inverse Mellin transform, including the missing
factor 1/(2πi) in the printed vertical integral. -/
theorem archNuclearityJet_apply (j : ArchNuclearityJetIndex χ τ hτ) (f : P) :
    let u : ℂ → ℂ := ((Z(χ, τ, hτ)) mkΘ(χ, f)).val
    let moment := fun t : ℝ ↦ (Real.log t : ℂ) ^ j.val.2 * mellinInv 0 u t
    Complex.VerticalIntegrable u 0 ∧ MellinConvergent moment j.val.1.re ∧
      archNuclearityJet χ τ hτ j mkΘ(χ, f) =
        iteratedDeriv j.val.2 (fun s ↦ globalIdelicZFunction f.val (ideleClassNormTwist χ s)) j.val.1 ∧
      archNuclearityJet χ τ hτ j mkΘ(χ, f) = mellin moment j.val.1 := by
  let v : B := (Z(χ, τ, hτ)) mkΘ(χ, f)
  have hmoment := schwartzBergman_jet_eq_mellinInv_moment v j.val.1 j.val.2
  have hz : (v.val : ℂ → ℂ) = (fun s ↦ globalIdelicZFunction f.val (ideleClassNormTwist χ s)) :=
    funext fun s ↦ ((exists_globalPolarThetaMellin χ τ hτ).choose_spec f s).2
  have hjet : archNuclearityJet χ τ hτ j mkΘ(χ, f) = iteratedDeriv j.val.2 v.val j.val.1 := by
    unfold archNuclearityJet
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, entireJet_apply]
    exact congrArg (fun g : ℂ → ℂ ↦ iteratedDeriv j.val.2 g j.val.1)
      (funext (schwartzBergmanEntireInclusion_apply v))
  exact ⟨hmoment.1, hmoment.2.1, hjet.trans (congrArg (fun g : ℂ → ℂ ↦
    iteratedDeriv j.val.2 g j.val.1) hz), hjet.trans hmoment.2.2⟩

/-- At one infinite place the gamma factor vanishes, by Mathlib's convention at the poles
of `Γ`, along an arithmetic progression. So the reciprocal gamma product has a zero of
positive finite order at infinitely many points. -/
private theorem archNuclearityJet_basis_poles_infinite
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :
    {s : ℂ | 0 < gammaOrder(χ, s)}.Infinite := by
  classical
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
  let c : ℂ := if hv : v.IsReal then
      (realHeckeCharacter_parameters χ v hv).exists.choose.1 +
        ((realHeckeCharacter_parameters χ v hv).exists.choose.2.val : ℂ)
    else
      (complexHeckeCharacter_parameters χ v
          (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose.1 +
        ((complexHeckeCharacter_parameters χ v
          (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose.2.natAbs : ℂ) / 2
  let s : ℕ → ℂ := fun n ↦ -c - 2 * n
  have hzero (n : ℕ) : heckeGammaFactor χ (s n) = 0 := by
    unfold heckeGammaFactor
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    by_cases hv : v.IsReal
    · simp only [s, c, hv, ↓reduceDIte]
      rw [Complex.Gammaℝ_eq_zero_iff]
      exact ⟨n, by ring⟩
    · simp only [s, c, hv, ↓reduceDIte]
      rw [div_eq_zero_iff]
      left
      rw [show -(_ + _) - 2 * (n : ℂ) + _ + _ = -((2 * n : ℕ) : ℂ) by push_cast; ring,
        Complex.Gammaℂ_def, Complex.Gamma_neg_nat_eq_zero, mul_zero]
  let f := fun z ↦ (heckeGammaFactor χ z)⁻¹
  have hA : AnalyticOnNhd ℂ f univ :=
    fun z _ ↦ (differentiable_inv_heckeGammaFactor χ).analyticAt z
  have hpos (n : ℕ) : s n ∈ {s : ℂ | 0 < gammaOrder(χ, s)} := by
    have h0 : analyticOrderAt f (s n) ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨hA _ (mem_univ _), by simp [f, hzero n]⟩
    have htop : analyticOrderAt f (s n) ≠ ⊤ := by
      intro htop
      have h1 := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
        (mem_univ (s n)) (analyticOrderAt_eq_top.1 htop) (mem_univ 1)
      exact inv_ne_zero
        (heckeGammaFactor_ne_zero_of_re_pos χ (by norm_num : (0 : ℝ) < (1 : ℂ).re)) h1
    change 0 < (analyticOrderAt f (s n)).toNat
    cases hn : analyticOrderAt f (s n) with
    | top => exact absurd hn htop
    | coe m =>
      rw [hn] at h0
      simpa [Nat.pos_iff_ne_zero] using h0
  refine Set.infinite_of_injective_forall_mem (fun n m h ↦ ?_) hpos
  have := congrArg Complex.re h
  simp only [s, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im] at this
  norm_num at this
  exact_mod_cast this

/-- The adjusted jet indices are countably infinite: they lie over the closed discrete
pole set, and the adjustment removes at most one index from an infinite pole set. -/
private theorem archNuclearityJet_basis_index_equiv
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F)) :
    Nonempty (ℕ ≃ ArchNuclearityJetIndex χ τ hτ) := by
  let S := {s : ℂ | 0 < gammaOrder(χ, s)}
  have hS : S.Countable := by
    have hd := (archNuclearityPoleSet_discrete χ).2
    have : DiscreteTopology S := hd.to_subtype
    exact Set.countable_coe_iff.mp
      (TopologicalSpace.separableSpace_iff_countable.mp inferInstance)
  have hmem (j : ArchNuclearityJetIndex χ τ hτ) : j.val.1 ∈ S := by
    have h := j.property
    unfold archNuclearityMultiplicity at h
    show 0 < gammaOrder(χ, j.val.1)
    omega
  have : Countable (ArchNuclearityJetIndex χ τ hτ) := by
    have := hS.to_subtype
    refine Function.Injective.countable
      (f := fun j : ArchNuclearityJetIndex χ τ hτ ↦ ((⟨j.val.1, hmem j⟩ : S), j.val.2)) ?_
    intro a b h
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    exact Subtype.ext (Prod.ext h.1 h.2)
  have : Infinite (ArchNuclearityJetIndex χ τ hτ) := by
    have := ((archNuclearityJet_basis_poles_infinite χ).sdiff
      (Set.finite_singleton (atZeroPole(χ, τ, hτ)))).to_subtype
    refine Infinite.of_injective
      (fun s : ↥(S \ {atZeroPole(χ, τ, hτ)}) ↦
        (⟨(s.val, 0), ?_⟩ : ArchNuclearityJetIndex χ τ hτ)) ?_
    · have hs := s.property
      simp only [Set.mem_sdiff, Set.mem_singleton_iff] at hs
      change 0 < archNuclearityMultiplicity χ τ hτ s.val
      unfold archNuclearityMultiplicity
      have hne : ¬(ω(χ) = 1 ∧ s.val = atZeroPole(χ, τ, hτ)) := fun h ↦ hs.2 h.2
      simp only [hne, ↓reduceIte, Nat.sub_zero]
      simpa [S] using hs.1
    · intro a b h
      exact Subtype.ext (congrArg (fun j : ArchNuclearityJetIndex χ τ hτ ↦ j.val.1) h)
  exact ⟨(nonempty_equiv_of_countable (α := ArchNuclearityJetIndex χ τ hτ)).some.symm⟩

local notation "finiteL(" χ ")" => (finiteHeckeL_exists_continuation χ).choose
local notation "poleFactor(" χ ", " τ ", " hτ ", " s ")" =>
  ((s : ℂ) - 1 - atZeroPole(χ, τ, hτ)) ^ (if ω(χ) = 1 then (1 : ℕ) else 0)

private theorem archRegularizedFiniteHeckeL_cancel_simplePole {A Z : ℂ → ℂ} {z : ℂ}
    (ha : AnalyticAt ℂ A z) (hvan : A z = 0)
    (hZ : MeromorphicAt Z z) (hpole : meromorphicOrderAt Z z = -1) :
    0 ≤ meromorphicOrderAt (A * Z) z := by
  have hpos : 0 < meromorphicOrderAt A z := lt_of_le_of_ne ha.meromorphicOrderAt_nonneg
    (fun he ↦ ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp he.symm hvan)
  rw [meromorphicOrderAt_mul ha.meromorphicAt hZ, hpole]
  cases ho : meromorphicOrderAt A z with
  | top => simp
  | coe k =>
    rw [ho] at hpos
    have hk : (0 : ℤ) < k := WithTop.coe_lt_coe.mp hpos
    exact WithTop.coe_le_coe.mpr (show (0 : ℤ) ≤ k + (-1) by omega)

/-- Paper: Equation (7.4.3.5), p. 368.
After cancellation of the pole on the trivial norm-one component, the continued
finite Hecke function is entire. -/
theorem archRegularizedFiniteHeckeL_differentiable :
    Differentiable ℂ (toMeromorphicNFOn
      (fun s ↦ poleFactor(χ, τ, hτ, s) * finiteL(χ) s) univ) := by
  let p : ℂ → ℂ := fun z ↦ poleFactor(χ, τ, hτ, z)
  let R : ℂ → ℂ := fun z ↦ (heckeGammaFactor χ z)⁻¹
  let L := finiteL(χ)
  let Z := continuedCompletedHeckeL χ
  obtain ⟨hL, heL⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  obtain ⟨hZ, heZ⟩ := continuedCompletedHeckeL_spec χ
  have hp : Differentiable ℂ p := by
    dsimp only [p]
    fun_prop
  have hR : Differentiable ℂ R := differentiable_inv_heckeGammaFactor χ
  have hA : Differentiable ℂ (p * R) := hp.mul hR
  have hm : MeromorphicOn ((p * R) * Z) univ := fun z _ ↦
    (hA.analyticAt z).meromorphicAt.mul (hZ (mem_univ z)).meromorphicAt
  change Differentiable ℂ (toMeromorphicNFOn (p * L) univ)
  rw [heckeEulerProductOutside_eq_finite_nf_eq (p * L) ((p * R) * Z)
    (fun z _ ↦ (hp.analyticAt z).meromorphicAt.mul (hL (mem_univ z)).meromorphicAt) hm (by
      intro z hz
      change p z * L z = p z * (heckeGammaFactor χ z)⁻¹ * Z z
      rw [show L z = _ from heL ⟨z, hz⟩, show Z z = _ from heZ ⟨z, hz⟩]
      change _ = p z * (heckeGammaFactor χ z)⁻¹ * (heckeGammaFactor χ z * _)
      rw [mul_assoc, inv_mul_cancel_left₀ (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hz))]
      rfl)]
  by_cases hk : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
  · have hω : ω(χ) = 1 := by
      ext1 u
      exact DFunLike.congr_fun hk u
    obtain ⟨t, ⟨hc, hzero, hone, haway⟩, -⟩ := completedHeckeL_continuation_simplePoles χ Z hZ heZ hk
    let b : ℂ := Complex.I * (t : ℂ)
    have hphase := existsUnique_ideleNormSection_character_phase χ τ hτ
    have hx : -t = hphase.exists.choose := by
      apply hphase.unique _ hphase.exists.choose_spec
      intro u
      have he := DFunLike.congr_fun hc (QuotientGroup.mk (τ u))
      change (χ (QuotientGroup.mk (τ u)) : ℂ) * _ ^ (0 : ℂ) =
        1 * ((((ideleNorm F (τ u)).val : ℝ) : ℂ) ^ (-Complex.I * (t : ℂ))) at he
      rw [Complex.cpow_zero, mul_one, one_mul, hτ u] at he
      simpa only [Complex.ofReal_neg, neg_mul, mul_comm (t : ℂ) Complex.I] using he
    have hpole : atZeroPole(χ, τ, hτ) = b := by
      change -(hphase.exists.choose : ℂ) * Complex.I = b
      rw [← hx, Complex.ofReal_neg, neg_neg, mul_comm]
    have hz₀ : (p * R) b = 0 := by
      have hshift := heckeGammaFactor_of_normTwist χ (-Complex.I * (t : ℂ)) (by simp [Complex.mul_re]) hc b
      have hneg : b + -Complex.I * (t : ℂ) = 0 := by
        dsimp [b]
        ring
      have hg : R b = 0 := by
        change (heckeGammaFactor χ b)⁻¹ = 0
        rw [hshift, hneg]
        simpa using inv_heckeGammaFactor_one_neg_even (F := F) 0
      simp [hg]
    have hz₁ : (p * R) (1 + b) = 0 := by simp [p, hω, hpole]
    intro z
    apply AnalyticAt.differentiableAt
    apply (meromorphicNFOn_toMeromorphicNFOn _ _ (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ _)]
    by_cases hz : z = b ∨ z = 1 + b
    · rcases hz with rfl | rfl
      · exact archRegularizedFiniteHeckeL_cancel_simplePole (hA.analyticAt _) hz₀
          (hZ (mem_univ _)).meromorphicAt hzero
      · exact archRegularizedFiniteHeckeL_cancel_simplePole (hA.analyticAt _) hz₁
          (hZ (mem_univ _)).meromorphicAt hone
    · exact ((hA.analyticAt z).mul (haway z (by simpa [b] using hz))).meromorphicOrderAt_nonneg
  · have hd := hA.mul (completedHeckeL_continuation_entire χ Z hZ heZ hk)
    rwa [toMeromorphicNFOn_eq_self.mpr (fun z _ ↦ (hd.analyticAt z).meromorphicNFAt)]

/-- Paper: Equation (7.4.3.5), p. 368.
The generator of the archimedean ideal is the pole-removed finite Hecke function.
Normal form supplies the removable value at its canceled pole. -/
def archRegularizedFiniteHeckeL : Entire :=
  let h := archRegularizedFiniteHeckeL_differentiable χ τ hτ
  ⟨⟨_, h.continuous⟩, h⟩

/-- Paper: Equation (7.4.3.5), p. 368.
On the half-plane of absolute convergence the generator equals the Euler product
times the pole-removing factor. -/
theorem archRegularizedFiniteHeckeL_apply (s : {s : ℂ // 1 < s.re}) :
    (archRegularizedFiniteHeckeL χ τ hτ).val s.val =
      poleFactor(χ, τ, hτ, s.val) * finiteHeckeL χ s := by
  let pole : ℂ → ℂ := fun z ↦ poleFactor(χ, τ, hτ, z)
  have hP (z : ℂ) : AnalyticAt ℂ pole z := by
    dsimp only [pole]
    fun_prop
  have hne : pole s ≠ 0 := by
    apply pow_ne_zero
    intro h
    have hr := congrArg Complex.re h
    have hs := s.property
    simp at hr
    linarith
  have hL := (finiteHeckeL_exists_continuation χ).choose_spec
  have hm : MeromorphicOn (fun z ↦ pole z * finiteL(χ) z) univ :=
    fun z hz ↦ (hP z).meromorphicAt.mul (hL.1 hz).meromorphicAt
  have hNF : MeromorphicNFAt (fun z ↦ pole z * finiteL(χ) z) s :=
    (meromorphicNFAt_mul_iff_right (hP s) hne).2 (hL.1 (mem_univ _))
  change toMeromorphicNFOn (fun z ↦ pole z * finiteL(χ) z) univ s = pole s * finiteHeckeL χ s
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ _),
    toMeromorphicNFAt_eq_self.mpr hNF]
  exact congrArg (pole s * ·) (hL.2 s)

-- TODO(paper-gap): Before (7.4.3.12) on p. 371, not every numerator class
-- comes from a flat test. For ℚ, S = {∞}, χ = 1, finite PV is the identity.
-- The real Gaussian combination in Printed.archNuclearityJet_apply_false has
-- nonzero global Z(-2), whereas a flat real test times the finite integer
-- indicator has Z(-2) = 0. Also, odd flat bumps have zero trivial theta class.
-- Apply §6.2 to homogeneous classes of polar tests, then identify the image
-- of the flat denominator under insertion. Uniqueness is a quotient assertion.
-- TODO(paper-gap): On p. 371, injectivity of the comparison quotient map requires
-- the range identification below. Density of the inclusion into entire functions
-- does not give that identification. Evaluations at nontrivial completed zeros
-- lie in the kernel of the printed adjoint to the theta annihilator. Pass to
-- the relative quotient of the completed ideal by the finite ideal.

/-- Paper: Equation (7.4.3.13), p. 372.
Each adjusted jet annihilates the archimedean orbital denominator, so the jets are
well defined on the quotient by it. -/
theorem archNuclearityQuotient_jetEquiv_annihilate (j : ArchNuclearityJetIndex χ τ hτ)
    (x : archNuclearityDenominator χ) :
    archNuclearityJet χ τ hτ j x.val = 0 := by sorry

/-- Paper: Equation (7.4.3.13), p. 372.
The adjusted jets assemble into a single continuous linear map from the archimedean
orbital quotient to the product of the coefficient spaces. -/
theorem archNuclearityQuotient_jetEquiv_coefficients :
    ∃ L : ArchNuclearityQuotient χ →L[ℂ] (ArchNuclearityJetIndex χ τ hτ → ℂ),
      ∀ (x : Θ₀(χ)) (j : ArchNuclearityJetIndex χ τ hτ),
        L ((archNuclearityDenominator χ).mkQ x) j = archNuclearityJet χ τ hτ j x := by
  have hker : ∀ j : ArchNuclearityJetIndex χ τ hτ,
      archNuclearityDenominator χ ≤ (archNuclearityJet χ τ hτ j).ker :=
    fun j _ hy ↦ archNuclearityQuotient_jetEquiv_annihilate (χ := χ) (τ := τ) (hτ := hτ) j ⟨_, hy⟩
  refine ⟨ContinuousLinearMap.pi fun j ↦ (archNuclearityDenominator χ).liftQL
    (archNuclearityJet χ τ hτ j) (hker j), ?_⟩
  intro x j
  exact Submodule.liftQ_apply (p := archNuclearityDenominator χ)
    (f := (archNuclearityJet χ τ hτ j).toLinearMap) (h := hker j) (x := x)

/-- Paper: Equation (7.4.3.13), p. 372.
The adjusted jets separate the classes of the archimedean orbital quotient: a class
on which every jet vanishes is the class of a flat test, that is, it lies in the
denominator. -/
theorem archNuclearityQuotient_jetEquiv_separating (x : Θ₀(χ))
    (hx : ∀ j, archNuclearityJet χ τ hτ j x = 0) : x ∈ archNuclearityDenominator χ := by
  sorry

/-- Entire divisibility is equivalent to the corresponding pointwise inequalities of vanishing orders. -/
private theorem archNuclearityMellin_range_entire_dvd
    (g f : entireContinuousMapSubalgebra) :
    g ∣ f ↔ ∀ z : ℂ, analyticOrderAt (g.val : ℂ → ℂ) z ≤
      analyticOrderAt (f.val : ℂ → ℂ) z := by
  have ha (a : entireContinuousMapSubalgebra) (z : ℂ) : AnalyticAt ℂ (a.val : ℂ → ℂ) z :=
    (show Differentiable ℂ a.val from a.property).analyticAt z
  constructor
  · rintro ⟨k, rfl⟩ z
    change _ ≤ analyticOrderAt ((g.val : ℂ → ℂ) * (k.val : ℂ → ℂ)) z
    rw [analyticOrderAt_mul (ha g z) (ha k z)]
    exact self_le_add_right _ _
  · intro hord
    let q := (f.val : ℂ → ℂ) / (g.val : ℂ → ℂ)
    have hq : MeromorphicOn q univ := fun z _ ↦ (ha f z).meromorphicAt.div (ha g z).meromorphicAt
    have hdiff : Differentiable ℂ (toMeromorphicNFOn q univ) := by
      intro z
      apply AnalyticAt.differentiableAt
      have hnf := meromorphicNFOn_toMeromorphicNFOn q univ (mem_univ z)
      apply hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp
      rw [meromorphicOrderAt_toMeromorphicNFOn hq (mem_univ z),
        meromorphicOrderAt_div (ha f z).meromorphicAt (ha g z).meromorphicAt,
        (ha f z).meromorphicOrderAt_eq, (ha g z).meromorphicOrderAt_eq]
      have hle := hord z
      generalize analyticOrderAt (f.val : ℂ → ℂ) z = m at hle ⊢
      generalize analyticOrderAt (g.val : ℂ → ℂ) z = n at hle ⊢
      cases m using ENat.recTopCoe with
      | top => simp
      | coe m =>
        cases n using ENat.recTopCoe with
        | top => simp at hle
        | coe n =>
          exact WithTop.coe_le_coe.mpr (sub_nonneg.mpr (by exact_mod_cast hle : (n : ℤ) ≤ m))
    refine ⟨⟨⟨_, hdiff.continuous⟩, hdiff⟩, Subtype.ext (ContinuousMap.ext fun z ↦ ?_)⟩
    change f.val z = g.val z * toMeromorphicNFOn q univ z
    by_cases hz : g.val z = 0
    · have hpos := lt_of_lt_of_le (pos_iff_ne_zero.mpr ((ha g z).analyticOrderAt_ne_zero.mpr hz))
          (hord z)
      rw [hz, zero_mul]
      exact (ha f z).analyticOrderAt_ne_zero.mp hpos.ne'
    · rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hq (mem_univ z),
        toMeromorphicNFAt_eq_self.mpr ((ha f z).div (ha g z) hz).meromorphicNFAt]
      exact (mul_div_cancel₀ _ hz).symm

/-- A maximum of vanishing orders identifies an entire divisibility condition with an ideal and additional jets. -/
private theorem archNuclearityMellin_range_ideal_intersection
    (g h : entireContinuousMapSubalgebra) (m : ℂ → ℕ)
    (horder : ∀ z : ℂ, analyticOrderAt (h.val : ℂ → ℂ) z =
      max (analyticOrderAt (g.val : ℂ → ℂ) z) (m z : ℕ∞))
    (φ : SchwartzBergman (univ : Set ℝ)) :
    φ ∈ schwartzBergmanDivisible h ↔
      φ ∈ schwartzBergmanDivisible g ∧
        ∀ z : ℂ, ∀ k : ℕ, k < m z → iteratedDeriv k (φ.val : ℂ → ℂ) z = 0 := by
  have hval : ((schwartzBergmanEntireInclusion φ).val : ℂ → ℂ) = φ.val :=
    funext (schwartzBergmanEntireInclusion_apply φ)
  have hφdiff : Differentiable ℂ (φ.val : ℂ → ℂ) := fun z ↦
    (φ.property.2.1 z (mem_univ _)).differentiableAt
      (Filter.univ_mem' fun _ ↦ mem_univ _)
  have hmem (g : entireContinuousMapSubalgebra) :
      φ ∈ schwartzBergmanDivisible g ↔
        ∀ z : ℂ, analyticOrderAt (g.val : ℂ → ℂ) z ≤
          analyticOrderAt (φ.val : ℂ → ℂ) z := by
    change schwartzBergmanEntireInclusion φ ∈ Ideal.span ({g} : Set entireContinuousMapSubalgebra) ↔ _
    rw [Ideal.mem_span_singleton, archNuclearityMellin_range_entire_dvd]
    simp only [hval]
  rw [hmem h, hmem g]
  simp_rw [horder, max_le_iff]
  rw [forall_and]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro z
  exact natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (hφdiff.analyticAt z)

/-- Separated zero sets in the two half-planes turn the generator product into a maximum of vanishing orders. -/
private theorem archNuclearityMellin_range_max_order
    (g h r : ℂ → ℂ) (hg : Differentiable ℂ g) (hh : Differentiable ℂ h)
    (hr : Differentiable ℂ r) (b : ℂ) (hb : b.re = 0) (δ : ℕ)
    (hδ : δ = 0 ∨ δ = 1)
    (he : ∀ z : ℂ, (z + b) ^ δ * h z = (-1 : ℂ) ^ δ * (g z * r z))
    (hgleft : ∀ z : ℂ, z.re ≤ 0 → g z ≠ 0)
    (hrright : ∀ z : ℂ, 0 < z.re → r z ≠ 0) (z : ℂ) :
    analyticOrderAt h z = max (analyticOrderAt g z)
      (((analyticOrderAt r z).toNat - if δ = 1 ∧ z = -b then 1 else 0 : ℕ) : ℕ∞) := by
  classical
  have har : AnalyticOnNhd ℂ r Set.univ := fun w _ ↦ hr.analyticAt w
  have hrone : analyticOrderAt r 1 = 0 :=
    (hr.analyticAt 1).analyticOrderAt_eq_zero.mpr (hrright 1 (by norm_num))
  have hrfinite : analyticOrderAt r z ≠ ⊤ :=
    har.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ 1)
      (Set.mem_univ z) (by rw [hrone]; simp)
  let p : ℂ → ℂ := fun w ↦ (w + b) ^ δ
  have hp : Differentiable ℂ p := (differentiable_id.add_const b).pow δ
  have hfunc : p * h = (fun _ ↦ (-1 : ℂ) ^ δ) * (g * r) := funext he
  have ho := congrArg (fun f : ℂ → ℂ ↦ analyticOrderAt f z) hfunc
  rw [analyticOrderAt_mul (hp.analyticAt z) (hh.analyticAt z),
    analyticOrderAt_const_mul ((hg.analyticAt z).mul (hr.analyticAt z))
      ((-1 : ℂ) ^ δ), ite_eq_right (pow_ne_zero δ (by norm_num : (-1 : ℂ) ≠ 0)),
    analyticOrderAt_mul (hg.analyticAt z) (hr.analyticAt z)] at ho
  have hporder : analyticOrderAt p z = if z = -b then (δ : ℕ∞) else 0 := by
    by_cases hz : z = -b
    · subst z
      have hlinear : analyticOrderAt (fun w : ℂ ↦ w + b) (-b) = 1 := by
        simpa only [sub_neg_eq_add] using
          (analyticOrderAt_id_sub_const_self (c := -b) :
            analyticOrderAt (fun w : ℂ ↦ w - -b) (-b) = 1)
      change analyticOrderAt ((fun w : ℂ ↦ w + b) ^ δ) (-b) = _
      rw [analyticOrderAt_pow (show AnalyticAt ℂ (fun w : ℂ ↦ w + b) (-b) by fun_prop), hlinear]
      simp
    · rw [ite_eq_right hz]
      apply (hp.analyticAt z).analyticOrderAt_eq_zero.mpr
      apply pow_ne_zero
      intro heq
      exact hz (eq_neg_of_add_eq_zero_left heq)
  rw [hporder] at ho
  by_cases hpos : 0 < z.re
  · have hz : z ≠ -b := by
      intro heq
      have hzre := congrArg Complex.re heq
      simp only [Complex.neg_re, hb, neg_zero] at hzre
      linarith
    have hrzero : analyticOrderAt r z = 0 :=
      (hr.analyticAt z).analyticOrderAt_eq_zero.mpr (hrright z hpos)
    have horder : analyticOrderAt h z = analyticOrderAt g z := by simpa [hz, hrzero] using ho
    simpa [hrzero] using horder
  · have hgz : analyticOrderAt g z = 0 :=
      (hg.analyticAt z).analyticOrderAt_eq_zero.mpr (hgleft z (le_of_not_gt hpos))
    rw [hgz, zero_add] at ho
    rw [hgz, max_eq_right (by positivity)]
    cases hRz : analyticOrderAt r z using ENat.recTopCoe with
    | top => exact (hrfinite hRz).elim
    | coe m =>
      cases hHz : analyticOrderAt h z using ENat.recTopCoe with
      | top => simp [hHz, hRz] at ho
      | coe n =>
        rw [hHz, hRz] at ho
        rcases hδ with rfl | rfl
        · simpa using ho
        · by_cases hz : z = -b
          · have hnatcast : ((1 + n : ℕ) : ℕ∞) = (m : ℕ∞) := by
              simpa [hz, Nat.cast_add] using ho
            have hn : 1 + n = m := by exact_mod_cast hnatcast
            simpa [hz] using (show (n : ℕ∞) = ((m - 1 : ℕ) : ℕ∞) from
              by exact_mod_cast (show n = m - 1 by omega))
          · simpa [hz] using ho

/-- The functional equation and the zero-free right boundary exclude completed zeros in the closed left half-plane. -/
private theorem archNuclearityMellin_range_completed_order_left
    (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (s : ℂ) (hs : s.re ≤ 0) :
    meromorphicOrderAt (continuedCompletedHeckeL χ) s ≤ 0 := by
  obtain ⟨ε, hε, hne, he⟩ := completedHeckeL_continuation_functionalEquation χ
    (continuedCompletedHeckeL χ) (continuedCompletedHeckeL χ⁻¹)
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
    (continuedCompletedHeckeL_spec χ⁻¹).1 (continuedCompletedHeckeL_spec χ⁻¹).2
  let r (z : ℂ) := 1 - z
  have hr : HasDerivAt r (-1) s := by simpa [r] using (hasDerivAt_id s).const_sub 1
  have e : continuedCompletedHeckeL χ⁻¹ ∘ r = fun z ↦ ε z * continuedCompletedHeckeL χ z :=
    funext he
  have ho := meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL χ⁻¹)
    (show AnalyticAt ℂ r s by dsimp [r]; fun_prop) (hr.deriv.trans_ne (by norm_num))
  rw [e] at ho
  change meromorphicOrderAt (ε * continuedCompletedHeckeL χ) s = _ at ho
  rw [meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt s) (hne s)] at ho
  rw [ho]
  apply le_of_not_gt
  intro hz
  have hzre := completedHeckeL_continuation_zeros χ⁻¹ (continuedCompletedHeckeL χ⁻¹)
    (continuedCompletedHeckeL_spec χ⁻¹).1 (continuedCompletedHeckeL_spec χ⁻¹).2
    (s := r s) (by change 0 < 1 - s.re; linarith) hz
  change 1 - s.re < 1 at hzre
  linarith

/-- After removing the two poles, the completed generator is nonzero in the closed left half-plane. -/
private theorem archNuclearityMellin_range_completed_ne_zero_left
    (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
    (s : ℂ) (hs : s.re ≤ 0) :
    (regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
      (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2).val s ≠ 0 := by
  classical
  let L := continuedCompletedHeckeL χ
  let G := regularizedCompletedHeckeL χ τ hτ L
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
  let x : ℝ := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
  let b : ℂ := (x : ℂ) * Complex.I
  let δ : ℕ := if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0
  let p : ℂ → ℂ := fun z ↦ (z + b) ^ δ * (1 - z - b) ^ δ
  have hG : Differentiable ℂ (G.val : ℂ → ℂ) := G.property
  have hp : Differentiable ℂ p := by dsimp [p]; fun_prop
  have hL := (continuedCompletedHeckeL_spec χ).1
  by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
  · by_cases hs₀ : s = -b
    · subst s
      exact (regularizedCompletedHeckeL_ne_zero_at_canceled_poles χ τ hτ L
        (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2 hχ).1
    · have hp₀ : p s ≠ 0 := by
        simp only [p, δ, ite_eq_left hχ, pow_one]
        apply mul_ne_zero
        · intro h
          exact hs₀ (eq_neg_of_add_eq_zero_left h)
        · intro h
          have hreal := congrArg Complex.re h
          simp only [Complex.sub_re, Complex.one_re, Complex.zero_re,
            b, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
            Complex.ofReal_im, Complex.I_im, zero_mul, sub_self] at hreal
          linarith
      have hm : MeromorphicOn (p * L) univ := fun z _ ↦
        (hp.analyticAt z).meromorphicAt.mul (hL (mem_univ z)).meromorphicAt
      have hord : meromorphicOrderAt (G.val : ℂ → ℂ) s = meromorphicOrderAt L s := by
        change meromorphicOrderAt (toMeromorphicNFOn (p * L) univ) s = _
        rw [meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ s),
          meromorphicOrderAt_mul_of_ne_zero (hp.analyticAt s) hp₀]
      apply (hG.analyticAt s).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp
      apply le_antisymm
      · rw [hord]
        exact archNuclearityMellin_range_completed_order_left F χ s hs
      · exact (hG.analyticAt s).meromorphicOrderAt_nonneg
  · have he : (G.val : ℂ → ℂ) = L := by
      change toMeromorphicNFOn (fun z ↦ (z + b) ^ δ * (1 - z - b) ^ δ * L z) univ = L
      simp only [δ, ite_eq_right hχ, pow_zero, one_mul]
      exact toMeromorphicNFOn_eq_self.mpr hL
    apply (hG.analyticAt s).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp
    apply le_antisymm
    · rw [he]
      exact archNuclearityMellin_range_completed_order_left F χ s hs
    · exact (hG.analyticAt s).meromorphicOrderAt_nonneg


/-- The finite and completed regularized generators differ by the reciprocal gamma factor and one linear factor. -/
private theorem archNuclearityMellin_range_generator_identity
    (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F)) :
    let x := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
    let b := (x : ℂ) * Complex.I
    let δ : ℕ := if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0
    let H := archRegularizedFiniteHeckeL χ τ hτ
    let G := regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
      (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
    ∀ z : ℂ, (z + b) ^ δ * H.val z =
      (-1 : ℂ) ^ δ * G.val z * (heckeGammaFactor χ z)⁻¹ := by
  classical
  intro x b δ H G
  let p : ℂ → ℂ := fun z ↦ (z + b) ^ δ * (1 - z - b) ^ δ
  let L := continuedCompletedHeckeL χ
  have hp : Differentiable ℂ p := by dsimp [p]; fun_prop
  have hL := (continuedCompletedHeckeL_spec χ).1
  have hm : MeromorphicOn (p * L) univ := fun z _ ↦
    (hp.analyticAt z).meromorphicAt.mul (hL (mem_univ z)).meromorphicAt
  have hb : b.re = 0 := by simp [b]
  have hδ : (if (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F)) = 1 then (1 : ℕ) else 0) = δ := by
    by_cases hω : (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F)) = 1
    · simp [δ, hω, normOneRestrict_eq_one χ hω]
    · simp [δ, hω, normOneRestrict_ne_one χ hω]
  have hGval (z : ℂ) (hz : 1 < z.re) :
      G.val z = p z * completedHeckeL χ ⟨z, hz⟩ := by
    have hpne : p z ≠ 0 := by
      apply mul_ne_zero <;> apply pow_ne_zero <;> intro he
      · have := congrArg Complex.re he
        simp only [Complex.add_re, hb, add_zero, Complex.zero_re] at this
        linarith
      · have := congrArg Complex.re he
        simp only [Complex.sub_re, Complex.one_re, hb, sub_zero, Complex.zero_re] at this
        linarith
    have hnf : MeromorphicNFAt (p * L) z :=
      (meromorphicNFAt_mul_iff_right (hp.analyticAt z) hpne).2 (hL (mem_univ z))
    change toMeromorphicNFOn (p * L) univ z = p z * completedHeckeL χ ⟨z, hz⟩
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ z),
      toMeromorphicNFAt_eq_self.mpr hnf]
    exact congrArg (p z * ·) ((continuedCompletedHeckeL_spec χ).2 ⟨z, hz⟩)
  have hHval (z : ℂ) (hz : 1 < z.re) :
      H.val z = (z - 1 + b) ^ δ * finiteHeckeL χ ⟨z, hz⟩ := by
    have h := archRegularizedFiniteHeckeL_apply χ τ hτ ⟨z, hz⟩
    change H.val z = (z - 1 - (-(x : ℂ) * Complex.I)) ^
      (if (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F)) = 1 then 1 else 0) * finiteHeckeL χ ⟨z, hz⟩ at h
    rw [neg_mul, sub_neg_eq_add, hδ] at h
    exact h
  have hleft : Differentiable ℂ (fun z : ℂ ↦ (z + b) ^ δ * H.val z) :=
    ((differentiable_id.add_const b).pow δ).mul H.property
  have hright : Differentiable ℂ (fun z : ℂ ↦
      (-1 : ℂ) ^ δ * G.val z * (heckeGammaFactor χ z)⁻¹) :=
    ((G.property.const_mul _).mul (differentiable_inv_heckeGammaFactor χ))
  have hnear : (fun z : ℂ ↦ (z + b) ^ δ * H.val z) =ᶠ[𝓝 (2 : ℂ)]
      (fun z : ℂ ↦ (-1 : ℂ) ^ δ * G.val z * (heckeGammaFactor χ z)⁻¹) := by
    have hU : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (show IsOpen {z : ℂ | 1 < z.re} from
        isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hU] with z hz
    rw [hHval z hz, hGval z hz]
    change (z + b) ^ δ * ((z - 1 + b) ^ δ * finiteHeckeL χ ⟨z, hz⟩) =
      (-1 : ℂ) ^ δ * ((z + b) ^ δ * (1 - z - b) ^ δ *
        (heckeGammaFactor χ z * finiteHeckeL χ ⟨z, hz⟩)) * (heckeGammaFactor χ z)⁻¹
    rw [show z - 1 + b = (-1 : ℂ) * (1 - z - b) by ring, mul_pow]
    have hne := heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hz)
    field_simp [hne]
  have hA : AnalyticOnNhd ℂ (fun z : ℂ ↦ (z + b) ^ δ * H.val z) univ :=
    fun z _ ↦ hleft.analyticAt z
  have hB : AnalyticOnNhd ℂ (fun z : ℂ ↦
      (-1 : ℂ) ^ δ * G.val z * (heckeGammaFactor χ z)⁻¹) univ :=
    fun z _ ↦ hright.analyticAt z
  exact congrFun (hA.eq_of_eventuallyEq hB hnear)

/-- The finite generator has the completed vanishing orders together with the adjusted archimedean multiplicities. -/
private theorem archNuclearityMellin_range_orders
    (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F)) :
    ∀ z : ℂ, analyticOrderAt ((archRegularizedFiniteHeckeL χ τ hτ).val : ℂ → ℂ) z =
      max (analyticOrderAt ((regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
        (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2).val : ℂ → ℂ) z)
        (archNuclearityMultiplicity χ τ hτ z : ℕ∞) := by
  classical
  let x : ℝ := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
  let b : ℂ := (x : ℂ) * Complex.I
  let δ : ℕ := if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0
  let H := archRegularizedFiniteHeckeL χ τ hτ
  let G := regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
  have hb : b.re = 0 := by simp [b]
  have hδ : δ = 0 ∨ δ = 1 := by dsimp [δ]; split_ifs <;> simp
  have hδone : δ = 1 ↔ (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F)) = 1 := by
    by_cases hω : (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F)) = 1
    · simp [δ, hω, normOneRestrict_eq_one χ hω]
    · simp [δ, hω, normOneRestrict_ne_one χ hω]
  have hpole : (-(((existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose : ℝ) : ℂ) * Complex.I) = -b := by simp only [b, x, neg_mul]
  intro z
  have h := archNuclearityMellin_range_max_order (G.val : ℂ → ℂ) (H.val : ℂ → ℂ)
    (fun z ↦ (heckeGammaFactor χ z)⁻¹) G.property H.property
    (differentiable_inv_heckeGammaFactor χ) b hb δ hδ
    (fun z ↦ (archNuclearityMellin_range_generator_identity F χ τ hτ z).trans
      (mul_assoc _ _ _))
    (fun z hz ↦ archNuclearityMellin_range_completed_ne_zero_left F χ τ hτ z hz)
    (fun z hz ↦ inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ hz)) z
  have hmult : archNuclearityMultiplicity χ τ hτ z =
      (analyticOrderAt (fun w ↦ (heckeGammaFactor χ w)⁻¹) z).toNat -
        if δ = 1 ∧ z = -b then 1 else 0 := by
    simp only [archNuclearityMultiplicity, hpole, hδone]
  rw [hmult]
  exact h

/-- Paper: Theorem 7.4.3.1(4), p. 368.
The Mellin image of the flat denominator is the intersection of the entire
principal ideal generated by the regularized finite Hecke function with the
Schwartz–Bergman space. That image is closed. -/
theorem archNuclearityMellin_range :
    let D := (Z(χ, τ, hτ)) '' (archNuclearityDenominator χ : Set (Θ₀(χ)))
    D = (schwartzBergmanDivisible (archRegularizedFiniteHeckeL χ τ hτ) : Set B) ∧ IsClosed D := by
  classical
  let P₀ := adelePolarSubspace F
  let ω := (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : (ideleClassNorm F).ker →ₜ* IdeleClassGroup (𝓞 F) F))
  let K := LinearMap.ker ((homogeneousAdelicThetaLinearMap F ω).domRestrict P₀)
  let E := ↥P₀ ⧸ K
  let Z := (exists_globalPolarThetaMellin χ τ hτ).choose
  let G := regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
  let H := archRegularizedFiniteHeckeL χ τ hτ
  let : PolynormableSpace ℂ (E) := polynormableSpace_quotient (K)
  have hD (x : E) : x ∈ archNuclearityDenominator χ ↔
      ∀ j : ArchNuclearityJetIndex χ τ hτ, archNuclearityJet χ τ hτ j x = 0 :=
    ⟨fun hx j ↦ archNuclearityQuotient_jetEquiv_annihilate
        (χ := χ) (τ := τ) (hτ := hτ) j ⟨x, hx⟩,
      fun hx ↦ archNuclearityQuotient_jetEquiv_separating
        (χ := χ) (τ := τ) (hτ := hτ) x hx⟩
  have hjet (x : E) (j : ArchNuclearityJetIndex χ τ hτ) :
      archNuclearityJet χ τ hτ j x =
        iteratedDeriv j.val.2 (Z x).val j.val.1 := by
    unfold archNuclearityJet
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, entireJet_apply]
    exact congrArg (fun f : ℂ → ℂ ↦ iteratedDeriv j.val.2 f j.val.1)
      (funext (schwartzBergmanEntireInclusion_apply (Z x)))
  have hD0 : spectralNuclearityDenominator χ τ hτ 0 = schwartzBergmanDivisible G := by
    unfold spectralNuclearityDenominator
    apply congrArg schwartzBergmanDivisible
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    change G.val (z + (0 : ℂ)) = G.val z
    simp only [add_zero]
  have hZrange (φ : SchwartzBergman (univ : Set ℝ)) :
      (∃ x : E, Z x = φ) ↔ φ ∈ schwartzBergmanDivisible G := by
    change φ ∈ Z.toLinearMap.range ↔ φ ∈ schwartzBergmanDivisible G
    rw [← spectralNuclearityDenominator_zero χ τ hτ, hD0]
  have horder := archNuclearityMellin_range_orders F χ τ hτ
  have hideal (φ : SchwartzBergman (univ : Set ℝ)) : φ ∈ schwartzBergmanDivisible H ↔
      φ ∈ schwartzBergmanDivisible G ∧ ∀ z k,
        k < archNuclearityMultiplicity χ τ hτ z → iteratedDeriv k φ.val z = 0 :=
    archNuclearityMellin_range_ideal_intersection G H (archNuclearityMultiplicity χ τ hτ)
      horder φ
  have heq : Z '' (archNuclearityDenominator χ : Set (E)) =
      (schwartzBergmanDivisible H : Set (SchwartzBergman (univ : Set ℝ))) := by
    ext φ
    constructor
    · rintro ⟨x, hx, rfl⟩
      apply (hideal _).mpr
      refine ⟨(hZrange _).mp ⟨x, rfl⟩, fun z k hk ↦ ?_⟩
      exact (hjet x ⟨(z, k), hk⟩).symm.trans ((hD x).mp hx ⟨(z, k), hk⟩)
    · intro hφ
      obtain ⟨hrange, hjets⟩ := (hideal φ).mp hφ
      obtain ⟨x, hx⟩ := (hZrange φ).mpr hrange
      refine ⟨x, (hD x).mpr ?_, hx⟩
      intro j
      rw [hjet x j, hx]
      exact hjets j.val.1 j.val.2 j.property
  exact ⟨heq, heq.symm ▸ schwartzBergmanDivisible_isClosed H⟩

/-- Paper: Equation (7.4.3.13), p. 372.
Every family of coefficient values is realized by a class of the archimedean
orbital quotient: the coefficient map is onto the whole product. -/
theorem archNuclearityQuotient_jetEquiv_realization
    (y : ArchNuclearityJetIndex χ τ hτ → ℂ) :
    ∃ x : Θ₀(χ), ∀ j, archNuclearityJet χ τ hτ j x = y j := by
  obtain ⟨x, hx⟩ := archJet_surjective χ τ hτ y
  exact ⟨x, congrFun hx⟩

/-- A continuous bijection from a quotient of a closed part of a strict LF-space onto
a countable product of scalar lines is open. Intersect each Fréchet stage with the closed
part to obtain the increasing family of images used by the open mapping theorem. -/
private theorem archNuclearityQuotient_jetEquiv_inverse_continuous_open
    {A Y ι : Type*} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [ContinuousSMul ℂ A] [AddCommGroup Y] [Module ℂ Y]
    [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℂ Y] [Countable ι]
    (hA : IsStrictLFSpace A) (B₀ : Submodule ℂ A) (hB : IsClosed (B₀ : Set A))
    (q : B₀ →L[ℂ] Y) (hq : Surjective q) (T : Y →L[ℂ] (ι → ℂ)) (hT : Bijective T) :
    IsOpenMap T := by
  let : T2Space Y := T2Space.of_injective_continuous hT.1 T.continuous
  obtain ⟨_, stage, hmono, hV, hcover, _⟩ := hA
  let slice (n : ℕ) := B₀.comap (stage n).subtype
  let j (n : ℕ) : slice n →L[ℂ] B₀ :=
    ((stage n).subtypeL.comp (slice n).subtypeL).codRestrict B₀ (fun z ↦ z.property)
  have hW (n : ℕ) : IsFrechetTVS (slice n) := by
    obtain ⟨hadd, hpoly, hmet, hcomp⟩ := hV n
    let : UniformSpace (stage n) := IsTopologicalAddGroup.rightUniformSpace _
    let : IsUniformAddGroup (stage n) := isUniformAddGroup_of_addCommGroup
    let : CompleteSpace (stage n) := hcomp
    have hc : IsClosed (slice n : Set (stage n)) := hB.preimage continuous_subtype_val
    let : UniformSpace (slice n) := UniformSpace.comap Subtype.val inferInstance
    let : IsUniformAddGroup (slice n) := (slice n).toAddSubgroup.isUniformAddGroup
    let : TopologicalSpace.MetrizableSpace (slice n) := IsEmbedding.subtypeVal.metrizableSpace
    let : CompleteSpace (slice n) := hc.completeSpace_coe
    refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  have hPi : IsFrechetTVS (ι → ℂ) := by
    refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  apply isOpenMap_of_surjective_toLF (isLFSpace_of_isFrechetTVS hPi) hW
    (fun n ↦ q.comp (j n)) _ _ T hT.2
  · rintro n _ ⟨y, rfl⟩
    exact ⟨⟨⟨y.val.val, hmono (Nat.le_succ n) y.val.property⟩, y.property⟩, rfl⟩
  · intro x
    obtain ⟨y, rfl⟩ := hq x
    obtain ⟨n, hn⟩ := hcover y.val
    exact ⟨n, ⟨⟨⟨y.val, hn⟩, y.property⟩, rfl⟩⟩

/-- Paper: Equation (7.4.3.13), p. 372.
The coefficient map of the archimedean orbital quotient is a topological isomorphism:
the inverse of the bijective coefficient map is continuous. -/
theorem archNuclearityQuotient_jetEquiv_inverse_continuous
    (L : ArchNuclearityQuotient χ →L[ℂ] (ArchNuclearityJetIndex χ τ hτ → ℂ))
    (hL : ∀ (x : Θ₀(χ)) (j : ArchNuclearityJetIndex χ τ hτ),
      L ((archNuclearityDenominator χ).mkQ x) j = archNuclearityJet χ τ hτ j x)
    (h : Function.Bijective L) :
    Continuous ((LinearEquiv.ofBijective L.toLinearMap h).symm :
      (ArchNuclearityJetIndex χ τ hτ → ℂ) → ArchNuclearityQuotient χ) := by
  -- Openness follows from the LF structure for any coordinate map with this bijectivity.
  have _ := hL
  obtain ⟨e⟩ := archNuclearityJet_basis_index_equiv χ τ hτ
  let : Countable (ArchNuclearityJetIndex χ τ hτ) := e.symm.injective.countable
  let q : P →L[ℂ] ArchNuclearityQuotient χ :=
    (archNuclearityDenominator χ).mkQL.comp (Π(χ)).mkQL
  have hq : Surjective q :=
    (archNuclearityDenominator χ).mkQ_surjective.comp (Π(χ)).mkQ_surjective
  have hopen := archNuclearityQuotient_jetEquiv_inverse_continuous_open
    (adeleSchwartz_strictLF (F := F)).2 P (adelePolarSubspace_closed (F := F)) q hq L h
  exact (LinearEquiv.ofBijective L.toLinearMap h).toEquiv.continuous_symm_iff.mpr hopen

/-- Paper: Equation (7.4.3.13) and the following paragraph, p. 372.
The coefficients of a quotient class are its adjusted jets, with the product topology.
The map includes simultaneous realization of every family of coefficients. -/
theorem archNuclearityQuotient_jetEquiv :
    ∃ e : ArchNuclearityQuotient χ ≃L[ℂ] (ArchNuclearityJetIndex χ τ hτ → ℂ),
      ∀ (x : Θ₀(χ)) j, e ((archNuclearityDenominator χ).mkQ x) j =
        archNuclearityJet χ τ hτ j x := by
  obtain ⟨L, hL⟩ := archNuclearityQuotient_jetEquiv_coefficients (χ := χ) (τ := τ) (hτ := hτ)
  have hinj : Function.Injective L := by
    intro a b hab
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (archNuclearityDenominator χ) a
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (archNuclearityDenominator χ) b
    have hzero : x - y ∈ archNuclearityDenominator χ := by
      refine archNuclearityQuotient_jetEquiv_separating (χ := χ) (τ := τ) (hτ := hτ)
        (x - y) fun j ↦ ?_
      rw [map_sub, ← hL x j, ← hL y j]
      exact sub_eq_zero.mpr (congrArg (fun f : (ArchNuclearityJetIndex χ τ hτ → ℂ) ↦ f j) hab)
    have hsub : (archNuclearityDenominator χ).mkQ x - (archNuclearityDenominator χ).mkQ y = 0 := by
      rw [← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hzero
    exact sub_eq_zero.mp hsub
  have hsurj : Function.Surjective L := by
    intro y
    obtain ⟨x, hx⟩ := archNuclearityQuotient_jetEquiv_realization (χ := χ) (τ := τ) (hτ := hτ) y
    exact ⟨(archNuclearityDenominator χ).mkQ x, funext fun j ↦ (hL x j).trans (hx j)⟩
  refine ⟨⟨LinearEquiv.ofBijective L.toLinearMap ⟨hinj, hsurj⟩, L.continuous, ?_⟩, hL⟩
  exact archNuclearityQuotient_jetEquiv_inverse_continuous (χ := χ) (τ := τ) (hτ := hτ)
    L hL ⟨hinj, hsurj⟩

/-- A continuous linear functional on a product of copies of `ℂ` depends on only finitely
many coordinates: the preimage of the unit ball contains a box that is unrestricted outside a
finite set of coordinates. -/
private theorem archNuclearityJet_span_finiteCoordinates {J : Type*} [DecidableEq J]
    (g : (J → ℂ) →L[ℂ] ℂ) :
    ∃ I : Finset J, ∀ y : J → ℂ, g y = ∑ i ∈ I, y i * g (Pi.single i 1) := by
  have h0 : (g : (J → ℂ) → ℂ) ⁻¹' Metric.ball 0 1 ∈ 𝓝 (0 : J → ℂ) :=
    g.continuous.continuousAt.preimage_mem_nhds
      (by simpa using Metric.ball_mem_nhds (0 : ℂ) one_pos)
  rw [nhds_pi, Filter.mem_pi'] at h0
  obtain ⟨I, t, ht, hsub⟩ := h0
  refine ⟨I, fun y ↦ ?_⟩
  set r : J → ℂ := y - ∑ i ∈ I, y i • Pi.single i 1 with hr
  have hrI : ∀ i ∈ I, r i = 0 := by
    intro i hi
    simp [hr, Finset.sum_apply, Pi.single_apply, hi]
  have hgr : g r = 0 := by
    by_contra hne
    have hmem : (2 / g r) • r ∈ (I : Set J).pi t := by
      intro i hi
      simp only [Pi.smul_apply, hrI i hi, smul_zero]
      exact mem_of_mem_nhds (ht i)
    have := hsub hmem
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, map_smul, smul_eq_mul] at this
    rw [div_mul_cancel₀ _ hne] at this
    norm_num at this
  have hy : y = r + ∑ i ∈ I, y i • Pi.single i 1 := by simp [hr]
  conv_lhs => rw [hy]
  rw [map_add, hgr, zero_add, map_sum]
  simp [map_smul]

/-- If the quotient by `D` is identified with the product of copies of `ℂ` indexed by `J`,
with coordinates the functionals `jet j`, then the closed span of the `jet j` in the strong
dual is the annihilator of `D`. -/
private theorem archNuclearityJet_span_of_equiv {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (D : Submodule ℂ E) {J : Type*} (jet : J → StrongDual ℂ E)
    (e : (E ⧸ D) ≃L[ℂ] (J → ℂ)) (he : ∀ x j, e (D.mkQ x) j = jet j x) :
    ((Submodule.span ℂ (Set.range jet)).topologicalClosure : Set (StrongDual ℂ E)) =
      {ℓ | ∀ x : D, ℓ x.val = 0} := by
  classical
  apply Set.Subset.antisymm
  · let A : Submodule ℂ (StrongDual ℂ E) :=
      { carrier := {ℓ | ∀ x : D, ℓ x.val = 0}
        add_mem' := fun ha hb x ↦ by simp [ha x, hb x]
        zero_mem' := fun x ↦ rfl
        smul_mem' := fun c ℓ hℓ x ↦ by simp [hℓ x] }
    have hA : IsClosed (A : Set (StrongDual ℂ E)) := by
      have : (A : Set (StrongDual ℂ E)) = ⋂ x : D, {ℓ | ℓ x.val = 0} := by
        ext ℓ; simp [A]
      rw [this]
      exact isClosed_iInter fun x ↦ isClosed_eq (continuous_eval_const _) continuous_const
    have hle : Submodule.span ℂ (Set.range jet) ≤ A := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩ x
      rw [← he, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero D).mpr x.property, map_zero,
        Pi.zero_apply]
    exact Submodule.topologicalClosure_minimal _ hle hA
  · intro ℓ hℓ
    apply Submodule.le_topologicalClosure
    have hker : D ≤ LinearMap.ker ℓ.toLinearMap := fun x hx ↦ hℓ ⟨x, hx⟩
    let l₀ : (E ⧸ D) →ₗ[ℂ] ℂ := D.liftQ ℓ.toLinearMap hker
    have hl₀ : Continuous l₀ :=
      (Submodule.isQuotientMap_mkQ D).continuous_iff.mpr ℓ.continuous
    let g : (J → ℂ) →L[ℂ] ℂ :=
      (⟨l₀, hl₀⟩ : (E ⧸ D) →L[ℂ] ℂ).comp e.symm.toContinuousLinearMap
    obtain ⟨I, hI⟩ := archNuclearityJet_span_finiteCoordinates g
    have hℓeq : ℓ = ∑ i ∈ I, g (Pi.single i 1) • jet i := by
      ext x
      have h1 : ℓ x = g (e (D.mkQ x)) := by
        simp [g, l₀]
      rw [h1, hI]
      simp only [he, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
        smul_eq_mul, mul_comm]
    rw [hℓeq]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Paper: Theorem 7.4.3.1(2), p. 368.
The closure of the linear span of the jets in the strong dual is the annihilator
of the archimedean-flat image. -/
theorem archNuclearityJet_span :
    ((Submodule.span ℂ (Set.range (archNuclearityJet χ τ hτ))).topologicalClosure :
        Set (StrongDual ℂ (Θ₀(χ)))) =
      {ℓ | ∀ x : archNuclearityDenominator χ, ℓ x.val = 0} :=
  Exists.elim (archNuclearityQuotient_jetEquiv χ τ hτ) fun e he ↦
    archNuclearityJet_span_of_equiv (archNuclearityDenominator χ) (archNuclearityJet χ τ hτ) e he

/-- Transport the topology generated by all seminorms across a continuous linear equivalence. -/
private theorem archNuclearityStrongDual_finest_of_equiv {A E : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (e : FinestLocallyConvex A ≃L[ℂ] E) :
    (inferInstance : TopologicalSpace E) = (inferInstance : TopologicalSpace (FinestLocallyConvex E)) := by
  let := finestLocallyConvex_t2 A
  let := finestLocallyConvex_t2 E
  have h := continuous_of_finestLocallyConvex A
    (show FinestLocallyConvex A →ₗ[ℂ] FinestLocallyConvex E from e.toLinearMap)
  have h' := continuous_of_finestLocallyConvex E
    (show FinestLocallyConvex E →ₗ[ℂ] FinestLocallyConvex A from e.symm.toLinearMap)
  apply le_antisymm <;> apply continuous_id_iff_le.mp
  · exact (h.comp e.symm.continuous).congr (fun x ↦ e.apply_symm_apply x)
  · exact (e.continuous.comp h').congr (fun x ↦ e.apply_symm_apply x)

/-- Paper: Theorem 7.4.3.1(3), p. 368.
For a fixed enumeration of the adjusted jets, the descended jets form a Schauder basis
of the strong dual of the archimedean quotient, with continuous coefficient functionals
on that strong dual. Pullback along the quotient map recovers the original jets.
Under the quotient's jet-coordinate equivalence, the basis consists of the coordinate
projections. Its coefficient functionals evaluate at the corresponding unit vectors.
Each dual vector is already recovered by a finite coordinate truncation. -/
private theorem archNuclearityJet_basis_schauder
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
    (σ : ℕ ≃ ArchNuclearityJetIndex χ τ hτ) :
    ∃ (d : ℕ → StrongDual ℂ (ArchNuclearityQuotient χ))
      (b : ℕ → StrongDual ℂ (StrongDual ℂ (ArchNuclearityQuotient χ))),
      (∀ n x, d n ((archNuclearityDenominator χ).mkQ x) = archNuclearityJet χ τ hτ (σ n) x) ∧
        IsSchauderBasis d b := by
  classical
  obtain ⟨e, he⟩ := archNuclearityQuotient_jetEquiv χ τ hτ
  let d (n : ℕ) : StrongDual ℂ (ArchNuclearityQuotient χ) :=
    (ContinuousLinearMap.proj (σ n)).comp e.toContinuousLinearMap
  let v (n : ℕ) : ArchNuclearityQuotient χ := e.symm (Pi.single (σ n) 1)
  let b (n : ℕ) : StrongDual ℂ (StrongDual ℂ (ArchNuclearityQuotient χ)) :=
    ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (v n)
  refine ⟨d, b, fun n x ↦ he x (σ n), ⟨fun m n ↦ ?_, fun ℓ ↦ ?_⟩⟩
  · change e (e.symm (Pi.single (σ m) 1)) (σ n) = if m = n then 1 else 0
    rw [e.apply_symm_apply, Pi.single_apply]
    by_cases hmn : m = n
    · subst n
      simp
    · simp [hmn, show σ n ≠ σ m from fun h ↦ hmn (σ.injective h).symm]
  · let L := ℓ.comp e.symm.toContinuousLinearMap
    -- Adapted from sLocalGammaOrbitalQuotient_dual_basis_finite in Sec3b:
    -- continuity in the product topology gives a finite set of coordinates
    -- on which the functional depends.
    have hU : L ⁻¹' Metric.ball 0 1 ∈ 𝓝 0 :=
      L.continuous.continuousAt.preimage_mem_nhds (by
        rw [map_zero]
        exact Metric.ball_mem_nhds 0 one_pos)
    rw [nhds_pi, Filter.mem_pi'] at hU
    obtain ⟨T, neighborhoods, hU, hsub⟩ := hU
    have hzero (y : ArchNuclearityJetIndex χ τ hτ → ℂ) (hy : ∀ i ∈ T, y i = 0) :
        L y = 0 := by
      by_contra hne
      have hval : L ((2 / L y) • y) = 2 := by
        rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne]
      have hmem : (2 / L y) • y ∈ Set.pi (↑T) neighborhoods := fun i hi ↦ by
        rw [Pi.smul_apply, hy i hi, smul_zero]
        exact mem_of_mem_nhds (hU i)
      have hball := hsub hmem
      rw [Set.mem_preimage, hval, Metric.mem_ball, dist_zero_right] at hball
      norm_num at hball
    let K := (T.image σ.symm).sup id + 1
    unfold HasSum
    rw [SummationFilter.conditional_filter_eq_map_range, Filter.tendsto_map'_iff]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop K] with k hk
    symm
    change ∑ m ∈ Finset.range k, b m ℓ • d m = ℓ
    ext q
    have hvan := hzero (e q - ∑ m ∈ Finset.range k, e q (σ m) • Pi.single (σ m) (1 : ℂ))
      fun j hj ↦ by
        have hjk : σ.symm j ∈ Finset.range k := by
          have hjle := Finset.le_sup (f := id) (Finset.mem_image_of_mem σ.symm hj)
          exact Finset.mem_range.mpr (by dsimp [K, id] at hk hjle; omega)
        simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]
        rw [Finset.sum_eq_single_of_mem (σ.symm j) hjk]
        · simp
        · intro m _ hm
          have hne : j ≠ σ m := fun h ↦ hm (by rw [h, σ.symm_apply_apply])
          simp [hne]
    simp only [map_sub, map_sum, map_smul, sub_eq_zero] at hvan
    change ℓ (e.symm (e q)) = ∑ m ∈ Finset.range k, e q (σ m) • ℓ (v m) at hvan
    rw [e.symm_apply_apply] at hvan
    simpa [b, d, mul_comm] using hvan.symm

/-- Paper: Theorem 7.4.3.1(3), p. 368.
Every enumeration of the adjusted jets gives a Schauder basis on the quotient strong
dual. Pullback along the quotient map recovers the original jets. -/
theorem archNuclearityJet_basis :
    let Q := ArchNuclearityQuotient χ
    let J := ArchNuclearityJetIndex χ τ hτ
    Nonempty (ℕ ≃ J) ∧
      ∀ σ : ℕ ≃ J, ∃ (d : ℕ → StrongDual ℂ Q) (b : ℕ → StrongDual ℂ (StrongDual ℂ Q)),
        (∀ n x, d n ((archNuclearityDenominator χ).mkQ x) = archNuclearityJet χ τ hτ (σ n) x) ∧
        IsSchauderBasis d b :=
  ⟨archNuclearityJet_basis_index_equiv χ τ hτ, archNuclearityJet_basis_schauder χ τ hτ⟩

/-- Enumerating the adjusted jets identifies the quotient with the space of complex sequences. -/
private theorem archNuclearityStrongDual_finest_sequenceEquiv
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :
    Nonempty (ArchNuclearityQuotient χ ≃L[ℂ] (ℕ → ℂ)) := by
  let τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F :=
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hτ : RightInverse τ (ideleNorm F) := canonicalIdeleNormSection_rightInverse F
  obtain ⟨q, _⟩ := archNuclearityQuotient_jetEquiv χ τ hτ
  obtain ⟨σ⟩ := (archNuclearityJet_basis χ τ hτ).1
  exact ⟨q.trans (ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : ℕ ↦ ℂ) σ.symm)⟩

/-- Paper: Theorem 7.4.3.1(1), p. 368.
The archimedean-flat theta image is closed in the zero-moment theta space, because
`archNuclearityQuotient_jetEquiv` identifies the quotient by it with a product of
copies of `ℂ`, which is Hausdorff, and the quotient map is continuous. -/
private theorem archNuclearityDenominator_isClosed_jetEquiv
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F)) :
    IsClosed (archNuclearityDenominator χ : Set (Θ₀(χ))) := by
  obtain ⟨e, -⟩ := archNuclearityQuotient_jetEquiv (χ := χ) (τ := τ) (hτ := hτ)
  have h : (archNuclearityDenominator χ : Set (Θ₀(χ))) =
      (fun x ↦ e (Submodule.mkQ (archNuclearityDenominator χ) x)) ⁻¹'
        {(0 : ArchNuclearityJetIndex χ τ hτ → ℂ)} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    have h0 (y : ArchNuclearityQuotient χ) : e y = 0 ↔ y = 0 := by
      rw [← map_zero e]
      exact e.injective.eq_iff
    exact ⟨fun hx ↦ (h0 _).mpr ((Submodule.Quotient.mk_eq_zero _).mpr hx),
      fun hx ↦ (Submodule.Quotient.mk_eq_zero _).mp ((h0 _).mp hx)⟩
  rw [h]
  exact isClosed_singleton.preimage
    (e.continuous.comp (Submodule.continuous_mkQ (archNuclearityDenominator χ)))

/-- Paper: Theorem 7.4.3.1(1), p. 368.
The archimedean-flat theta image is nontrivial: some archimedean-flat test whose
archimedean factors have zero additive integral has a nonzero class in the
zero-moment theta space.

A proof needs an explicit witness, and two routes are open. Either produce a nonzero
flat archimedean factor of zero additive integral together with a finite test that
the theta map does not kill; the comment above this section records that a
difference of dilates of a bump times the characteristic function of the integer
units has that shape on the trivial norm-one component. Or use
`archNuclearityMellin_range`, which is stated below this point: the Mellin image
of the denominator is the Schwartz-Bergman part of the ideal generated by
`archRegularizedFiniteHeckeL χ τ hτ`, so the denominator is trivial only if that
generator has no nonzero Schwartz-Bergman multiple; on `1 < Re s` its value is a
product of two nonzero factors by `archRegularizedFiniteHeckeL_apply` and
`finiteHeckeL_ne_zero_of_one_lt_re`. -/
private theorem archNuclearityDenominator_ne_bot :
    archNuclearityDenominator χ ≠ ⊥ := by sorry

/-- Paper: Theorem 7.4.3.1(1), p. 368.
The zero-moment archimedean-flat theta image is nonzero and closed.
Deviation: Uses the Fourier-moment correction from the prose after (7.4.3.1).
Without it the printed image need not be contained in the zero-moment theta space. -/
theorem archNuclearityDenominator_nonzero_closed :
    archNuclearityDenominator χ ≠ ⊥ ∧
      IsClosed (archNuclearityDenominator χ : Set (Θ₀(χ))) :=
  ⟨archNuclearityDenominator_ne_bot χ,
    archNuclearityDenominator_isClosed_jetEquiv (χ := χ)
      ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
      (canonicalIdeleNormSection_rightInverse F)⟩

/-- Paper: Theorem 7.4.3.1(5), pp. 368–369.
The strong dual of the archimedean quotient carries the finest locally convex topology. -/
theorem archNuclearityStrongDual_finest :
    let E := StrongDual ℂ (ArchNuclearityQuotient χ)
    (inferInstance : TopologicalSpace E) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex E)) := by
  obtain ⟨q⟩ := archNuclearityStrongDual_finest_sequenceEquiv χ
  obtain ⟨t, _⟩ := realSchwartzTaylor_equiv
  obtain ⟨p, _⟩ := realDiracDerivatives_polynomialEquiv
  let : TopologicalSpace (PowerSeries ℂ) := inferInstanceAs (TopologicalSpace ((Unit →₀ ℕ) → ℂ))
  let idx := (Finsupp.uniqueLinearEquiv ℕ ℕ ()).symm.toEquiv
  let series := ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Unit →₀ ℕ ↦ ℂ) idx
  let e := (q.trans series).trans t.symm
  exact archNuclearityStrongDual_finest_of_equiv
    (p.trans (e.symm.arrowCongr (ContinuousLinearEquiv.refl ℂ ℂ)))

local notation "Aθ(" φ ")" => (exists_polarThetaNuclearityAction χ τ hτ φ).choose

/-- Paper: Theorem 7.4.3.2(1), p. 372.
The archimedean-flat theta denominator is a closed subspace stable under the
regularized action of every Bruhat test. -/
theorem archNuclearityDenominator_closed_invariant (φ : 𝒟) :
    let D := archNuclearityDenominator χ
    IsClosed (D : Set (Θ₀(χ))) ∧ Set.MapsTo (Aθ(φ)) (D : Set (Θ₀(χ))) D := by
  let D := archNuclearityDenominator χ
  obtain ⟨e, he⟩ := archNuclearityQuotient_jetEquiv χ τ hτ
  have hmem (x : Θ₀(χ)) : x ∈ D ↔ ∀ j, archNuclearityJet χ τ hτ j x = 0 := by
    rw [← Submodule.Quotient.mk_eq_zero D]
    change (archNuclearityDenominator χ).mkQ x = (0 : ArchNuclearityQuotient χ) ↔ _
    constructor
    · intro hx j
      rw [← he x j, hx, map_zero, Pi.zero_apply]
    · intro hx
      apply e.injective
      funext j
      rw [he x j, hx j, map_zero, Pi.zero_apply]
  have hjet (x : Θ₀(χ)) (j : ArchNuclearityJetIndex χ τ hτ) :
      archNuclearityJet χ τ hτ j x = iteratedDeriv j.val.2 ((Z(χ, τ, hτ)) x).val j.val.1 := by
    unfold archNuclearityJet
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, entireJet_apply]
    exact congrArg (fun g : ℂ → ℂ ↦ iteratedDeriv j.val.2 g j.val.1)
      (funext (schwartzBergmanEntireInclusion_apply _))
  constructor
  · rw [show (D : Set (Θ₀(χ))) = ⋂ j, (archNuclearityJet χ τ hτ j) ⁻¹' {0} by
      apply Set.ext
      intro x
      rw [mem_iInter]
      exact hmem x]
    exact isClosed_iInter fun j ↦ isClosed_singleton.preimage (archNuclearityJet χ τ hτ j).continuous
  · intro x hx
    apply (hmem _).mpr
    intro j
    let v := (Z(χ, τ, hτ)) x
    have hv : Differentiable ℂ v.val := fun z ↦
      (v.property.2.1 z (mem_univ _)).differentiableAt (Filter.univ_mem' fun _ ↦ mem_univ _)
    have hprod : ((Z(χ, τ, hτ)) (Aθ(φ) x)).val = nuclearityTestMellin χ φ * v.val :=
      funext ((exists_polarThetaNuclearityAction χ τ hτ φ).choose_spec.1 x)
    rw [hjet, hprod, iteratedDeriv_mul
      ((differentiable_nuclearityTestMellin χ φ).contDiff.contDiffAt)
      hv.contDiff.contDiffAt]
    apply Finset.sum_eq_zero
    intro i _
    have hk := (hmem x).mp hx ⟨(j.val.1, j.val.2 - i), (Nat.sub_le _ _).trans_lt j.property⟩
    rw [hjet] at hk
    exact mul_eq_zero_of_right _ hk

/-- A test supported where the modulus lies in `[r, R]` has Mellin transform bounded by
`(r^σ + R^σ) ∫ ‖φ‖` on the line of real part `σ`. -/
private theorem archNuclearity_trace_mellin_bound {G : Type*} [MeasurableSpace G]
    (μ : Measure G) (φ : G → ℂ) (hφ : Integrable (fun g ↦ ‖φ g‖) μ) (n : G → ℝ) (r R : ℝ)
    (hr : 0 < r) (hsupp : ∀ g, φ g ≠ 0 → r ≤ n g ∧ n g ≤ R) (w : G → ℂ) (σ : ℝ)
    (hw : ∀ g, φ g ≠ 0 → ‖w g‖ = n g ^ σ) :
    ‖∫ g, φ g * w g ∂μ‖ ≤ (r ^ σ + R ^ σ) * ∫ g, ‖φ g‖ ∂μ := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hφ.const_mul _) (ae_of_all _ fun g ↦ ?_)
  by_cases h0 : φ g = 0
  · simp only [h0, zero_mul, norm_zero, mul_zero, le_refl]
  obtain ⟨hlo, hhi⟩ := hsupp g h0
  have hn : 0 < n g := hr.trans_le hlo
  rw [norm_mul, hw g h0, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rcases le_total 0 σ with hσ | hσ
  · exact (Real.rpow_le_rpow hn.le hhi hσ).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hr.le σ))
  · exact (Real.rpow_le_rpow_of_nonpos hr hlo hσ).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg (hn.trans_le hhi).le σ))

/-- Poles at `-c v - k` with bounded orders, and transforms bounded by `r^σ + R^σ` with
`1 < r ≤ R`, give an absolutely convergent pole sum. -/
private theorem archNuclearity_trace_pole_summable {W : Type*} [Finite W] (c : W → ℂ)
    (ord : ℂ → ℕ) (N : ℕ) (hord : ∀ z, ord z ≤ N)
    (hpole : ∀ z, 0 < ord z → ∃ v, ∃ k : ℕ, z = -c v - k) (M : ℂ → ℂ) (K r R : ℝ)
    (hK : 0 ≤ K) (hr : 1 < r) (hR : 1 < R)
    (hM : ∀ z, ‖M z‖ ≤ (r ^ z.re + R ^ z.re) * K) :
    Summable fun z : ℂ ↦ (ord z : ℝ) * ‖M z‖ := by
  classical
  let Pz := {z : ℂ // 0 < ord z}
  have hsub : ∀ x ∉ Set.range (Subtype.val : Pz → ℂ), (ord x : ℝ) * ‖M x‖ = 0 := by
    intro x hx
    have : ord x = 0 := by
      by_contra h
      exact hx ⟨⟨x, Nat.pos_of_ne_zero h⟩, rfl⟩
    simp [this]
  rw [← Function.Injective.summable_iff Subtype.val_injective hsub]
  choose v k hvk using fun z : Pz ↦ hpole z.val z.property
  let ι : Pz → W × ℕ := fun z ↦ (v z, k z)
  have hι : Function.Injective ι := by
    intro a b h
    apply Subtype.ext
    rw [hvk a, hvk b]
    simp only [ι, Prod.mk.injEq] at h
    rw [h.1, h.2]
  let g : W × ℕ → ℝ := fun p ↦ N * K * (r ^ (-(c p.1).re) * (r⁻¹) ^ p.2 +
    R ^ (-(c p.1).re) * (R⁻¹) ^ p.2)
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hR0 : 0 < R := zero_lt_one.trans hR
  have hNK : 0 ≤ (N : ℝ) * K := mul_nonneg (Nat.cast_nonneg _) hK
  have hg0 (p : W × ℕ) : 0 ≤ g p :=
    mul_nonneg hNK (add_nonneg
      (mul_nonneg (Real.rpow_nonneg hr0.le _) (pow_nonneg (inv_nonneg.mpr hr0.le) _))
      (mul_nonneg (Real.rpow_nonneg hR0.le _) (pow_nonneg (inv_nonneg.mpr hR0.le) _)))
  have hg : Summable g := by
    refine (summable_prod_of_nonneg hg0).mpr ⟨fun x ↦ ?_, Summable.of_finite⟩
    have h1 : Summable fun y : ℕ ↦ r ^ (-(c x).re) * (r⁻¹) ^ y :=
      Summable.mul_left (r ^ (-(c x).re))
        (summable_geometric_of_lt_one (inv_nonneg.mpr hr0.le) (inv_lt_one_of_one_lt₀ hr))
    have h2 : Summable fun y : ℕ ↦ R ^ (-(c x).re) * (R⁻¹) ^ y :=
      Summable.mul_left (R ^ (-(c x).re))
        (summable_geometric_of_lt_one (inv_nonneg.mpr hR0.le) (inv_lt_one_of_one_lt₀ hR))
    have h3 := Summable.mul_left ((N : ℝ) * K) (h1.add h2)
    exact h3
  refine Summable.of_nonneg_of_le (fun _ ↦ mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
    (fun z ↦ ?_) (hg.comp_injective hι)
  have hz : (z.val).re = -(c (v z)).re - k z := by
    rw [hvk z]
    simp
  have hpow (a : ℝ) (ha : 0 < a) : a ^ (z.val).re = a ^ (-(c (v z)).re) * (a⁻¹) ^ k z := by
    rw [hz, Real.rpow_sub ha, Real.rpow_natCast, div_eq_mul_inv, inv_pow]
  change (ord z.val : ℝ) * ‖M z.val‖ ≤ N * K * (r ^ (-(c (v z)).re) * (r⁻¹) ^ k z +
    R ^ (-(c (v z)).re) * (R⁻¹) ^ k z)
  rw [← hpow r hr0, ← hpow R hR0, mul_assoc, mul_comm K]
  exact mul_le_mul (by exact_mod_cast hord _) (hM _) (norm_nonneg _) (Nat.cast_nonneg _)

/-- Summing a function of the center over all jet indices counts each center with its
multiplicity, in any enumeration of the indices. -/
private theorem archNuclearity_trace_reindex (m : ℂ → ℕ) (M : ℂ → ℂ)
    (σ : ℕ ≃ {j : ℂ × ℕ // j.2 < m j.1})
    (h : Summable fun z : ℂ ↦ (m z : ℝ) * ‖M z‖) :
    Summable (fun n ↦ ‖M (σ n).val.1‖) ∧
      HasSum (fun n ↦ M (σ n).val.1) (∑' z, (m z : ℂ) * M z) := by
  let J := {j : ℂ × ℕ // j.2 < m j.1}
  let e : J ≃ Σ z : ℂ, Fin (m z) :=
    { toFun := fun j ↦ ⟨j.val.1, ⟨j.val.2, j.property⟩⟩
      invFun := fun p ↦ ⟨(p.1, p.2.val), p.2.isLt⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let f : (Σ z : ℂ, Fin (m z)) → ℂ := fun p ↦ M p.1
  have hfib (z : ℂ) : ∑' _ : Fin (m z), ‖M z‖ = (m z : ℝ) * ‖M z‖ := by
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnorm : Summable fun p ↦ ‖f p‖ :=
    (summable_sigma_of_nonneg fun _ ↦ norm_nonneg _).mpr
      ⟨fun _ ↦ Summable.of_finite, by simpa only [f, hfib] using h⟩
  have hf : Summable f := hnorm.of_norm
  have hsum : ∑' p, f p = ∑' z, (m z : ℂ) * M z := by
    rw [hf.tsum_sigma' fun _ ↦ Summable.of_finite]
    refine tsum_congr fun z ↦ ?_
    rw [tsum_fintype]
    change ∑ _b : Fin (m z), M z = _
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcomp : (fun n ↦ M (σ n).val.1) = f ∘ (σ.trans e) := rfl
  have hcompn : (fun n ↦ ‖M (σ n).val.1‖) = (fun p ↦ ‖f p‖) ∘ (σ.trans e) := rfl
  refine ⟨?_, ?_⟩
  · rw [hcompn]
    exact (σ.trans e).summable_iff.mpr hnorm
  · rw [hcomp, ← hsum]
    exact (σ.trans e).hasSum_iff.mpr hf.hasSum

/-- A biorthogonal coefficient functional picks out the coefficient of its own vector
from a finite combination in which that vector occurs exactly once. -/
private theorem archNuclearity_trace_diag {E ι : Type*} [AddCommGroup E] [Module ℂ E]
    (d : ℕ → E) (b : ℕ → E →ₗ[ℂ] ℂ) (hb : ∀ m n, b m (d n) = if m = n then 1 else 0)
    (n : ℕ) (s : Finset ι) (i₀ : ι) (hi₀ : i₀ ∈ s) (coef : ι → ℂ) (idx : ι → ℕ)
    (h₀ : idx i₀ = n) (hne : ∀ i ∈ s, i ≠ i₀ → idx i ≠ n) :
    b n (∑ i ∈ s, coef i • d (idx i)) = coef i₀ := by
  rw [map_sum, Finset.sum_eq_single i₀]
  · simp [hb, h₀]
  · intro i hi hi'
    have hn : ¬ n = idx i := fun h ↦ hne i hi hi' h.symm
    simp [hb, hn]
  · intro h
    exact absurd hi₀ h

/-- A Bruhat test supported where the norm exceeds one has Mellin transform bounded by
`(r^σ + R^σ) K` on the line of real part `σ`, for some `1 < r` and `1 < R`: the norm is
bounded above and below on the compact support. -/
private theorem archNuclearity_trace_mellin (φ : 𝒟)
    (hφ : tsupport φ.val ⊆ {g : C𝔽 | 1 < ((ideleClassNorm F g).val : ℝ)}) :
    ∃ K r R : ℝ, 0 ≤ K ∧ 1 < r ∧ 1 < R ∧
      ∀ z, ‖nuclearityTestMellin χ φ z‖ ≤ (r ^ z.re + R ^ z.re) * K := by
  let n : C𝔽 → ℝ := fun g ↦ ((ideleClassNorm F g).val : ℝ)
  have hn : Continuous n := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have hK : IsCompact (tsupport φ.val) := φ.property.2
  obtain ⟨r, R, hr, hR, hrR⟩ : ∃ r R : ℝ, 1 < r ∧ 1 < R ∧
      ∀ g ∈ tsupport φ.val, r ≤ n g ∧ n g ≤ R := by
    rcases (tsupport φ.val).eq_empty_or_nonempty with he | hne
    · exact ⟨2, 2, by norm_num, by norm_num, fun g hg ↦ by simp [he] at hg⟩
    · obtain ⟨a, ha, hamin⟩ := hK.exists_isMinOn hne hn.continuousOn
      obtain ⟨b, hb, hbmax⟩ := hK.exists_isMaxOn hne hn.continuousOn
      exact ⟨n a, n b, hφ ha, hφ hb, fun g hg ↦
        ⟨isMinOn_iff.mp hamin g hg, isMaxOn_iff.mp hbmax g hg⟩⟩
  have htw (s : ℂ) (g : C𝔽) : ‖ideleClassNormTwist χ s g‖ = n g ^ s.re := by
    change ‖(χ g : ℂ) * ((n g : ℝ) : ℂ) ^ s‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]
  have hint : Integrable (fun g ↦ ‖φ.val g‖) μ𝔽 := by
    refine ((nuclearityTestMellin_integrable χ φ).1 0).norm.congr (ae_of_all _ fun g ↦ ?_)
    change ‖φ.val g * ideleClassNormTwist χ 0 g‖ = ‖φ.val g‖
    rw [norm_mul, htw, Complex.zero_re, Real.rpow_zero, mul_one]
  refine ⟨∫ g, ‖φ.val g‖ ∂μ𝔽, r, R, integral_nonneg fun _ ↦ norm_nonneg _, hr, hR,
    fun z ↦ ?_⟩
  exact archNuclearity_trace_mellin_bound μ𝔽 φ.val hint n r R (zero_lt_one.trans hr)
    (fun g hg ↦ hrR g (subset_tsupport _ hg)) (ideleClassNormTwist χ z) z.re
    (fun g _ ↦ htw z g)

/-- On a trivial norm-one isotype the omitted jet sits at a gamma pole, and the
norm twist of `χ` there is the trivial quasi-character. -/
private theorem archNuclearity_trace_trivial (hω : ω(χ) = 1) :
    1 ≤ gammaOrder(χ, atZeroPole(χ, τ, hτ)) ∧
      ∀ g, ideleClassNormTwist χ atZeroPole(χ, τ, hτ) g = ideleClassNormTwist 1 0 g := by
  have hk : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 := by
    ext1 u
    exact DFunLike.congr_fun hω u
  obtain ⟨hZ, heZ⟩ := continuedCompletedHeckeL_spec χ
  obtain ⟨t, ⟨hc, -, -, -⟩, -⟩ := completedHeckeL_continuation_simplePoles χ _ hZ heZ hk
  let b : ℂ := Complex.I * (t : ℂ)
  have hphase := existsUnique_ideleNormSection_character_phase χ τ hτ
  have hx : -t = hphase.exists.choose := by
    apply hphase.unique _ hphase.exists.choose_spec
    intro u
    have he := DFunLike.congr_fun hc (QuotientGroup.mk (τ u))
    change (χ (QuotientGroup.mk (τ u)) : ℂ) * _ ^ (0 : ℂ) =
      1 * ((((ideleNorm F (τ u)).val : ℝ) : ℂ) ^ (-Complex.I * (t : ℂ))) at he
    rw [Complex.cpow_zero, mul_one, one_mul, hτ u] at he
    simpa only [Complex.ofReal_neg, neg_mul, mul_comm (t : ℂ) Complex.I] using he
  have hpole : atZeroPole(χ, τ, hτ) = b := by
    change -(hphase.exists.choose : ℂ) * Complex.I = b
    rw [← hx, Complex.ofReal_neg, neg_neg, mul_comm]
  rw [hpole]
  have hR0 : (heckeGammaFactor χ b)⁻¹ = 0 := by
    have hshift := heckeGammaFactor_of_normTwist χ (-Complex.I * (t : ℂ))
      (by simp [Complex.mul_re]) hc b
    have hneg : b + -Complex.I * (t : ℂ) = 0 := by
      dsimp [b]
      ring
    rw [hshift, hneg]
    simpa using inv_heckeGammaFactor_one_neg_even (F := F) 0
  have han : AnalyticOnNhd ℂ (fun s ↦ (heckeGammaFactor χ s)⁻¹) univ :=
    fun s _ ↦ (differentiable_inv_heckeGammaFactor χ).analyticAt s
  have hne0 : analyticOrderAt (fun s ↦ (heckeGammaFactor χ s)⁻¹) b ≠ 0 := by
    rw [Ne, (han b (mem_univ _)).analyticOrderAt_eq_zero, not_not]
    exact hR0
  have hnetop : analyticOrderAt (fun s ↦ (heckeGammaFactor χ s)⁻¹) b ≠ ⊤ := by
    intro htop
    have h1 : (heckeGammaFactor χ 1)⁻¹ ≠ 0 :=
      inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ (by norm_num))
    exact h1 (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ b) (analyticOrderAt_eq_top.1 htop) (mem_univ 1))
  refine ⟨?_, fun g ↦ ?_⟩
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hnetop
    rw [← hm] at hne0 ⊢
    rw [ENat.toNat_natCast]
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hne0)
  · have hx0 : ((((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
    have he := DFunLike.congr_fun hc g
    change (χ g : ℂ) * ((((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ) =
      1 * ((((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) ^ (-Complex.I * (t : ℂ)) at he
    change (χ g : ℂ) * ((((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) ^ b =
      1 * ((((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ)
    rw [Complex.cpow_zero, mul_one, one_mul] at he
    rw [he, ← Complex.cpow_add _ _ hx0, show -Complex.I * (t : ℂ) + b = 0 by dsimp [b]; ring,
      Complex.cpow_zero, mul_one]

/-- Continuous functionals on a quotient agree once they agree on representatives. -/
private theorem archNuclearity_trace_qext {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (D : Submodule ℂ E) (f g : StrongDual ℂ (E ⧸ D))
    (h : ∀ x, f (D.mkQ x) = g (D.mkQ x)) : f = g :=
  ContinuousLinearMap.ext fun q ↦ by
    obtain ⟨x, rfl⟩ := D.mkQ_surjective q
    exact h x

/-- Abstract form of the diagonal computation: if an operator `A` acts on jet coordinates by
the Leibniz rule with multiplier derivatives `Md i`, then for biorthogonal coefficient
functionals the diagonal entry of the induced quotient operator is the multiplier at the
center of the jet. -/
private theorem archNuclearity_trace_diagonal {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (D : Submodule ℂ E) (A : E →ₗ[ℂ] E) (T : (E ⧸ D) →L[ℂ] (E ⧸ D))
    (hT : ∀ x, T (D.mkQ x) = D.mkQ (A x)) (m : ℂ → ℕ)
    (σ : ℕ ≃ {j : ℂ × ℕ // j.2 < m j.1}) (jet : {j : ℂ × ℕ // j.2 < m j.1} → E → ℂ)
    (Md : ℕ → ℂ → ℂ) (M₀ : ℂ → ℂ) (hMd₀ : ∀ z, Md 0 z = M₀ z)
    (hjetA : ∀ x (j : {j : ℂ × ℕ // j.2 < m j.1}), jet j (A x) =
      ∑ i ∈ Finset.range (j.val.2 + 1), (j.val.2.choose i : ℂ) * Md i j.val.1 *
        jet ⟨(j.val.1, j.val.2 - i), (Nat.sub_le _ _).trans_lt j.property⟩ x)
    (d : ℕ → StrongDual ℂ (E ⧸ D)) (b : ℕ → StrongDual ℂ (StrongDual ℂ (E ⧸ D)))
    (hd : ∀ n x, d n (D.mkQ x) = jet (σ n) x)
    (hb : ∀ m n, b m (d n) = if m = n then 1 else 0) (n : ℕ) :
    b n ((d n).comp T) = M₀ (σ n).val.1 := by
  have hcomp : (d n).comp T = ∑ i ∈ Finset.range ((σ n).val.2 + 1),
      (((σ n).val.2.choose i : ℂ) * Md i (σ n).val.1) •
        d (σ.symm ⟨((σ n).val.1, (σ n).val.2 - i),
          (Nat.sub_le _ _).trans_lt (σ n).property⟩) := by
    refine archNuclearity_trace_qext D _ _ fun x ↦ ?_
    rw [ContinuousLinearMap.comp_apply, hT, hd, hjetA, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [ContinuousLinearMap.smul_apply, hd, Equiv.apply_symm_apply, smul_eq_mul]
  rw [hcomp]
  refine (archNuclearity_trace_diag d (fun m ↦ (b m).toLinearMap) hb n
    (Finset.range ((σ n).val.2 + 1)) 0 (by simp)
    (fun i ↦ ((σ n).val.2.choose i : ℂ) * Md i (σ n).val.1)
    (fun i ↦ σ.symm ⟨((σ n).val.1, (σ n).val.2 - i),
      (Nat.sub_le _ _).trans_lt (σ n).property⟩) ?_ ?_).trans ?_
  · rw [Equiv.symm_apply_eq]
    exact Subtype.ext (Prod.ext rfl (Nat.sub_zero _))
  · intro i hi hi0 heq
    rw [Equiv.symm_apply_eq] at heq
    have h2 := congrArg (fun j : {j : ℂ × ℕ // j.2 < m j.1} ↦ j.val.2) heq
    have hik := Finset.mem_range.mp hi
    simp only at h2
    omega
  · simp [hMd₀]

/-- The scalar half of Theorem 7.4.3.2(2): the gamma-pole series converges absolutely, and
for every enumeration of the jets the Mellin values at the jet centers sum absolutely to
the pole series minus the omitted trivial jet. -/
private theorem archNuclearity_trace_scalar (φ : 𝒟)
    (hφ : tsupport φ.val ⊆ {g : C𝔽 | 1 < ((ideleClassNorm F g).val : ℝ)}) :
    let poles := {z : ℂ // 0 < gammaOrder(χ, z)}
    let term := fun z : poles ↦ (gammaOrder(χ, z.val) : ℂ) * nuclearityTestMellin χ φ z.val
    let correction := if ω(χ) = 1 then nuclearityTestMellin 1 φ 0 else 0
    Summable (fun z ↦ ‖term z‖) ∧ ∀ σ : ℕ ≃ ArchNuclearityJetIndex χ τ hτ,
      Summable (fun n ↦ ‖nuclearityTestMellin χ φ (σ n).val.1‖) ∧
      HasSum (fun n ↦ nuclearityTestMellin χ φ (σ n).val.1) ((∑' z, term z) - correction) := by
  intro poles term correction
  classical
  let M := nuclearityTestMellin χ φ
  obtain ⟨c, hc⟩ := archNuclearity_trace_gammaOrder χ
  obtain ⟨K, r, R, hK, hr, hR, hM⟩ := archNuclearity_trace_mellin χ φ hφ
  have hsum : Summable fun z : ℂ ↦ (gammaOrder(χ, z) : ℝ) * ‖M z‖ :=
    archNuclearity_trace_pole_summable c (fun z ↦ gammaOrder(χ, z)) _ (fun z ↦ (hc z).1)
      (fun z ↦ (hc z).2) M K r R hK hr hR hM
  refine ⟨(hsum.subtype fun z ↦ 0 < gammaOrder(χ, z)).congr fun z ↦ ?_, fun σ ↦ ?_⟩
  · simp only [Function.comp_apply, term, norm_mul, Complex.norm_natCast]
    rfl
  let mult := archNuclearityMultiplicity χ τ hτ
  have hmult : Summable fun z : ℂ ↦ (mult z : ℝ) * ‖M z‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
      (fun z ↦ mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le _ _) (norm_nonneg _))
      hsum
  obtain ⟨h1, h2⟩ := archNuclearity_trace_reindex mult M σ hmult
  refine ⟨h1, ?_⟩
  convert h2 using 1
  have hsupp : Function.support (fun z : ℂ ↦ (gammaOrder(χ, z) : ℂ) * M z) ⊆
      {z | 0 < gammaOrder(χ, z)} := by
    intro z hz
    by_contra h
    simp only [Set.mem_ofPred_eq, not_lt, Nat.le_zero] at h
    exact hz (by simp [h])
  have htsum : ∑' z : poles, term z = ∑' z : ℂ, (gammaOrder(χ, z) : ℂ) * M z :=
    tsum_subtype_eq_of_support_subset (s := {z | 0 < gammaOrder(χ, z)}) hsupp
  have hsumC : Summable fun z : ℂ ↦ (gammaOrder(χ, z) : ℂ) * M z :=
    Summable.of_norm (by simpa only [norm_mul, Complex.norm_natCast] using hsum)
  rw [htsum]
  by_cases hω : ω(χ) = 1
  · obtain ⟨hord1, htw⟩ := archNuclearity_trace_trivial χ τ hτ hω
    have hm (z : ℂ) : (mult z : ℂ) * M z = (gammaOrder(χ, z) : ℂ) * M z -
        if z = atZeroPole(χ, τ, hτ) then M atZeroPole(χ, τ, hτ) else 0 := by
      simp only [mult, archNuclearityMultiplicity, hω, true_and]
      split_ifs with h
      · subst h
        rw [Nat.cast_sub hord1]
        ring
      · simp
    have hcorr : correction = M atZeroPole(χ, τ, hτ) := by
      simp only [correction, hω, ↓reduceIte]
      refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
      change φ.val g * ideleClassNormTwist 1 0 g = φ.val g * ideleClassNormTwist χ _ g
      rw [htw g]
    rw [tsum_congr hm, hsumC.tsum_sub (hasSum_ite_eq _ _).summable, tsum_ite_eq, hcorr]
  · have hm (z : ℂ) : (mult z : ℂ) * M z = (gammaOrder(χ, z) : ℂ) * M z := by
      simp [mult, archNuclearityMultiplicity, hω]
    simp only [correction, hω, ↓reduceIte, sub_zero]
    exact (tsum_congr hm).symm


-- TODO(paper-gap): The contour identity (7.4.3.15) uses positive pole orders
-- on the right, but the logarithmic derivative has their negatives as residues.
-- Both boundary lines must avoid the poles. With χ = 1 over ℚ and a = 2,
-- the left line passes through the simple pole at -2.

/-- Paper: Theorem 7.4.3.2(2), pp. 372–373.
For tests supported where the norm is greater than one, the quotient operator has
an absolutely convergent matrix trace in every enumeration of the specified
basis of the strong dual. The gamma-pole series is also absolutely convergent.
Deviation: On a trivial norm-one isotype the omitted jet is at the trivial
quasi-character, so its weight is the integral of the test with no character factor. -/
theorem archNuclearity_trace (φ : 𝒟)
    (_hφ : tsupport φ.val ⊆ {g : C𝔽 | 1 < ((ideleClassNorm F g).val : ℝ)}) :
    let D := archNuclearityDenominator χ
    let Q := Θ₀(χ) ⧸ D
    let poles := {z : ℂ // 0 < gammaOrder(χ, z)}
    let term := fun z : poles ↦ (gammaOrder(χ, z.val) : ℂ) * nuclearityTestMellin χ φ z.val
    let correction := if ω(χ) = 1 then nuclearityTestMellin 1 φ 0 else 0
    ∃ T : Q →L[ℂ] Q,
      (∀ f, T (D.mkQ f) = D.mkQ (Aθ(φ) f)) ∧ Summable (fun z ↦ ‖term z‖) ∧
      ∀ (σ : ℕ ≃ ArchNuclearityJetIndex χ τ hτ) (d : ℕ → StrongDual ℂ Q)
        (b : ℕ → StrongDual ℂ (StrongDual ℂ Q)),
        (∀ n x, d n (D.mkQ x) = archNuclearityJet χ τ hτ (σ n) x) →
        IsSchauderBasis d b →
        let diagonal := fun n ↦ b n ((d n).comp T)
        Summable (fun n ↦ ‖diagonal n‖) ∧ HasSum diagonal ((∑' z, term z) - correction) := by
  intro D Q poles term correction
  obtain ⟨hterm, hσ⟩ := archNuclearity_trace_scalar χ τ hτ φ _hφ
  let M := nuclearityTestMellin χ φ
  have hmaps := (archNuclearityDenominator_closed_invariant χ τ hτ φ).2
  let T₀ : Q →ₗ[ℂ] Q := D.mapQ D (Aθ(φ)).toLinearMap fun x hx ↦ hmaps hx
  have hT₀ : Continuous T₀ := by
    apply (Submodule.isQuotientMap_mkQ D).continuous_iff.mpr
    exact (Submodule.isQuotientMap_mkQ D).continuous.comp (Aθ(φ)).continuous
  let T : Q →L[ℂ] Q := ⟨T₀, hT₀⟩
  have hT (x : Θ₀(χ)) : T (D.mkQ x) = D.mkQ (Aθ(φ) x) := rfl
  refine ⟨T, hT, hterm, ?_⟩
  intro σ d b hd hb diagonal
  have hjet (x : Θ₀(χ)) (j : ArchNuclearityJetIndex χ τ hτ) :
      archNuclearityJet χ τ hτ j x = iteratedDeriv j.val.2 ((Z(χ, τ, hτ)) x).val j.val.1 := by
    unfold archNuclearityJet
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, entireJet_apply]
    exact congrArg (fun g : ℂ → ℂ ↦ iteratedDeriv j.val.2 g j.val.1)
      (funext (schwartzBergmanEntireInclusion_apply _))
  have hjetA (x : Θ₀(χ)) (j : ArchNuclearityJetIndex χ τ hτ) :
      archNuclearityJet χ τ hτ j (Aθ(φ) x) = ∑ i ∈ Finset.range (j.val.2 + 1),
        (j.val.2.choose i : ℂ) * iteratedDeriv i M j.val.1 *
          archNuclearityJet χ τ hτ ⟨(j.val.1, j.val.2 - i),
            (Nat.sub_le _ _).trans_lt j.property⟩ x := by
    let v := (Z(χ, τ, hτ)) x
    have hv : Differentiable ℂ v.val := fun z ↦
      (v.property.2.1 z (mem_univ _)).differentiableAt (Filter.univ_mem' fun _ ↦ mem_univ _)
    have hprod : ((Z(χ, τ, hτ)) (Aθ(φ) x)).val = M * v.val :=
      funext ((exists_polarThetaNuclearityAction χ τ hτ φ).choose_spec.1 x)
    rw [hjet, hprod, iteratedDeriv_mul
      ((differentiable_nuclearityTestMellin χ φ).contDiff.contDiffAt)
      hv.contDiff.contDiffAt]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hjet]
  have hdiag (n : ℕ) : diagonal n = M (σ n).val.1 := by
    have h := archNuclearity_trace_diagonal D (Aθ(φ)).toLinearMap T hT
      (archNuclearityMultiplicity χ τ hτ) σ (fun j x ↦ archNuclearityJet χ τ hτ j x)
      (fun i z ↦ iteratedDeriv i M z) M (fun z ↦ by simp) hjetA d b hd (fun m n ↦ hb.1 m n) n
    exact h
  have hdiagfun : diagonal = fun n ↦ M (σ n).val.1 := funext hdiag
  rw [hdiagfun]
  exact hσ σ

/-- A von Neumann bounded set in a space carrying the finest locally convex topology
spans a finite-dimensional subspace: otherwise a linear functional unbounded on it
would be continuous. -/
private theorem archNuclearityStrongDual_finiteRank_bounded {E : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E]
    (h : (inferInstance : TopologicalSpace E) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex E)))
    (S : Set E) (hS : Bornology.IsVonNBounded ℂ S) :
    FiniteDimensional ℂ (Submodule.span ℂ S) := by
  by_contra hfin
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℂ S
  have hinf : b.Infinite := by
    intro hb
    apply hfin
    rw [← hspan]
    exact FiniteDimensional.span_of_finite ℂ hb
  let f := hinf.natEmbedding
  let v : ℕ → E := fun n ↦ (f n).val
  have hv : LinearIndependent ℂ v := hli.comp f f.injective
  let ℓ₀ : Submodule.span ℂ (Set.range v) →ₗ[ℂ] ℂ :=
    (Finsupp.linearCombination ℂ (fun n : ℕ ↦ (n : ℂ))).comp hv.repr
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
  have hℓv (n : ℕ) : ℓ (v n) = n := by
    have h1 := congrArg (fun g ↦ g ⟨v n, Submodule.subset_span ⟨n, rfl⟩⟩) hℓ
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h1
    rw [h1]
    simp [ℓ₀, hv.repr_eq_single n ⟨v n, Submodule.subset_span ⟨n, rfl⟩⟩ rfl]
  have hcont' : Continuous (show FinestLocallyConvex E →ₗ[ℂ] ℂ from ℓ) := by
    apply WithSeminorms.continuous_normedSpace_rng ℂ (finestLocallyConvex_withSeminorms (E := E))
    refine ⟨{(normSeminorm ℂ ℂ).comp ℓ}, 1, ?_⟩
    rw [one_smul]
    exact Finset.le_sup (f := id) (Finset.mem_singleton_self _)
  have hcont : Continuous ℓ := by
    have : @Continuous E ℂ (inferInstance : TopologicalSpace (FinestLocallyConvex E)) _ ℓ :=
      hcont'
    rwa [← h] at this
  let L : E →L[ℂ] ℂ := ⟨ℓ, hcont⟩
  have hb := (hS.image L)
  rw [NormedSpace.isVonNBounded_iff] at hb
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have := hC (L (v n)) ⟨v n, hbS (f n).property, rfl⟩
  change ‖ℓ (v n)‖ ≤ C at this
  rw [hℓv, Complex.norm_natCast] at this
  linarith

/-- In a Hausdorff space with the finest locally convex topology, an operator with a
nuclear presentation has range inside the span of its Banach disc, which is
finite-dimensional. -/
private theorem archNuclearityStrongDual_finiteRank_gen {E : Type*} [AddCommGroup E]
    [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [T2Space E] [ContinuousSMul ℂ E]
    (h : (inferInstance : TopologicalSpace E) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex E)))
    (T : E →L[ℂ] E) (hT : Nonempty (NuclearPresentation T)) :
    FiniteDimensional ℂ T.toLinearMap.range := by
  obtain ⟨r⟩ := hT
  let W := Submodule.span ℂ r.disc
  have hW : FiniteDimensional ℂ W :=
    archNuclearityStrongDual_finiteRank_bounded h r.disc r.isBanachDisc.bounded
  have hWc : IsClosed (W : Set E) := W.isClosed_of_finiteDimensional
  have hle : T.toLinearMap.range ≤ W := by
    rintro _ ⟨x, rfl⟩
    apply hWc.mem_of_tendsto (r.hasSum x)
    filter_upwards with s
    exact W.sum_mem fun n _ ↦ W.smul_mem _ (r.vector n).property
  exact Submodule.finiteDimensional_of_le hle

private theorem archNuclearityStrongDual_finiteRank_dual {Q : Type*} [AddCommGroup Q]
    [Module ℂ Q] [TopologicalSpace Q] [IsTopologicalAddGroup Q] [ContinuousSMul ℂ Q]
    (h : (inferInstance : TopologicalSpace (StrongDual ℂ Q)) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex (StrongDual ℂ Q))))
    (T : StrongDual ℂ Q →L[ℂ] StrongDual ℂ Q) (hT : Nonempty (NuclearPresentation T)) :
    FiniteDimensional ℂ T.toLinearMap.range :=
  archNuclearityStrongDual_finiteRank_gen h T hT

-- Stated over the same tower of quotients as `ArchNuclearityQuotient`, and concluding `FG`,
-- so that applying it to the concrete space needs only syntactic unification (#5398).
private theorem archNuclearityStrongDual_finiteRank_tower {X : Type*} {_ : AddCommGroup X}
    {_ : Module ℂ X} {_ : TopologicalSpace X} [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]
    (P0 : Submodule ℂ X) (k : Submodule ℂ P0) (p : Submodule ℂ (P0 ⧸ k))
    (h : let E := StrongDual ℂ ((P0 ⧸ k) ⧸ p)
      (inferInstance : TopologicalSpace E) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex E)))
    (T : StrongDual ℂ ((P0 ⧸ k) ⧸ p) →L[ℂ] StrongDual ℂ ((P0 ⧸ k) ⧸ p))
    (hT : Nonempty (NuclearPresentation T)) :
    (LinearMap.range T.toLinearMap).FG :=
  Module.Finite.iff_fg.mp (archNuclearityStrongDual_finiteRank_dual h T hT)

private theorem archNuclearityStrongDual_finiteRank_fd {E : Type*} {_ : AddCommGroup E}
    {_ : Module ℂ E} {S : Submodule ℂ E} (h : S.FG) : FiniteDimensional ℂ S :=
  Module.Finite.iff_fg.mpr h

/-- Paper: Remark 7.4.3.3, p. 373.
Nuclear endomorphisms of the strong dual of the archimedean quotient have finite rank.
Deviation: The printed universal nonnuclearity conclusion needs infinite rank,
which fails for the zero test. -/
theorem archNuclearityStrongDual_finiteRank
    (T : StrongDual ℂ (ArchNuclearityQuotient χ) →L[ℂ] StrongDual ℂ (ArchNuclearityQuotient χ))
    (_hT : Nonempty (NuclearPresentation T)) :
    FiniteDimensional ℂ T.toLinearMap.range :=
  archNuclearityStrongDual_finiteRank_fd
    (archNuclearityStrongDual_finiteRank_tower _ _ _ (archNuclearityStrongDual_finest χ) T _hT)

/-- An equicontinuous family of linear functionals on a sequence space sees only
a common finite set of coordinates. Otherwise rescaled tails tend to zero while
some member of the family still takes the value one. -/
private theorem archNuclearityQuotient_nuclear_iff_finiteRank_tail {E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (e : E ≃L[ℂ] (ℕ → ℂ))
    (φ : ℕ → StrongDual ℂ E) (hφ : EquicontinuousAt (fun k x ↦ φ k x) 0) :
    ∃ N : ℕ, ∀ x : E, (∀ j < N, e x j = 0) → ∀ k, φ k x = 0 := by
  by_contra! h
  choose x hx k hk using h
  let y (n : ℕ) : E := (φ (k n) (x n))⁻¹ • x n
  have he : Filter.Tendsto (fun n ↦ e (y n)) Filter.atTop (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro j
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop j] with n hn
    simp [y, hx n j hn]
  have hy : Filter.Tendsto y Filter.atTop (𝓝 0) := by
    simpa only [Function.comp_def, e.symm_apply_apply, map_zero] using
      (e.symm.continuous.tendsto 0).comp he
  obtain ⟨n, hn⟩ := (hy.eventually (Metric.equicontinuousAt_iff_right.mp hφ 1 one_pos)).exists
  simpa [y, hk n, dist_zero_left] using hn (k n)

/-- A nuclear presentation factors through the finite coordinates detected by its
equicontinuous functionals. -/
private theorem archNuclearityQuotient_nuclear_iff_finiteRank_range {E : Type*}
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [T2Space E]
    [ContinuousSMul ℂ E] (e : E ≃L[ℂ] (ℕ → ℂ)) (T : E →L[ℂ] E) (r : NuclearPresentation T) :
    FiniteDimensional ℂ T.toLinearMap.range := by
  obtain ⟨N, hN⟩ := archNuclearityQuotient_nuclear_iff_finiteRank_tail e r.functional r.equicontinuous
  let a : E →ₗ[ℂ] (Fin N → ℂ) := LinearMap.pi fun j ↦ (LinearMap.proj j.val).comp e.toLinearMap
  have hker : a.ker ≤ T.toLinearMap.ker := by
    intro x hx
    have hφ := hN x fun j hj ↦ congrFun (LinearMap.mem_ker.mp hx) ⟨j, hj⟩
    have hsum := r.hasSum x
    simp only [hφ, mul_zero, zero_smul] at hsum
    exact hsum.unique hasSum_zero
  let : FiniteDimensional ℂ (E ⧸ a.ker) :=
    FiniteDimensional.of_injective a.quotKerEquivRange.toLinearMap a.quotKerEquivRange.injective
  apply FiniteDimensional.of_surjective (a.ker.liftQ T.toLinearMap.rangeRestrict
    (by rwa [LinearMap.ker_rangeRestrict]))
  rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_rangeRestrict]

/-- A map to finitely many complex coordinates has a finite nuclear presentation,
using the coordinate vectors in the closed unit ball. -/
private theorem archNuclearityQuotient_nuclear_iff_finiteRank_coordinates {E : Type*}
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [PolynormableSpace ℂ E] [T2Space E] {d : ℕ} (A : E →L[ℂ] (Fin d → ℂ)) :
    IsNuclearOperator A := by
  classical
  let ball := Metric.closedBall (0 : Fin d → ℂ) 1
  let b (i : Fin d) : Fin d → ℂ := Pi.single i 1
  have hb (i : Fin d) : b i ∈ ball := by simp [ball, b, Metric.mem_closedBall, Pi.norm_single]
  have hz : (0 : Fin d → ℂ) ∈ ball := by simp [ball]
  let c (n : ℕ) : ℂ := if n < d then 1 else 0
  have hc (n : ℕ) (hn : n ∉ Finset.range d) : c n = 0 := ite_eq_right (fun h ↦ hn (Finset.mem_range.mpr h))
  let φ : Option (Fin d) → StrongDual ℂ E := fun i ↦
    i.elim 0 (fun j ↦ (ContinuousLinearMap.proj j).comp A)
  let idx (n : ℕ) : Option (Fin d) := if hn : n < d then some ⟨n, hn⟩ else none
  let y (n : ℕ) : Fin d → ℂ := if hn : n < d then b ⟨n, hn⟩ else 0
  have hy (n : ℕ) : y n ∈ ball := by
    by_cases hn : n < d
    · simpa only [y, dite_eq_left hn] using hb ⟨n, hn⟩
    · simpa only [y, dite_eq_right hn] using hz
  apply (isNuclearOperator_iff_nonempty_presentation A).mpr
  refine ⟨⟨c, fun n ↦ φ (idx n), ball, isBanachDisc_closedUnitBall,
    fun n ↦ ⟨y n, Submodule.subset_span (hy n)⟩, hy, ?_, ?_, fun x ↦ ?_⟩⟩
  · exact (hasSum_sum_of_ne_finset_zero (s := Finset.range d) fun n hn ↦ by
      simp only [hc n hn, norm_zero]).summable
  · exact (equicontinuousAt_finite.mpr (fun i ↦ (φ i).continuous.continuousAt)).comp idx
  · let term (n : ℕ) := (c n * φ (idx n) x) • y n
    have hsum : ∑ n ∈ Finset.range d, term n = A x := by
      rw [← Fin.sum_univ_eq_sum_range term]
      ext j
      simp [term, c, φ, idx, y, b, Pi.single_apply, Finset.sum_apply]
    change HasSum term (A x)
    rw [← hsum]
    exact hasSum_sum_of_ne_finset_zero fun n hn ↦ by simp only [term, hc n hn, zero_mul, zero_smul]

/-- Factor a finite-rank map through coordinates on its range and then include the
range back into the ambient space. -/
private theorem archNuclearityQuotient_nuclear_iff_finiteRank_of_finite {E : Type*}
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [PolynormableSpace ℂ E] [T2Space E] (T : E →L[ℂ] E) (hf : FiniteDimensional ℂ T.toLinearMap.range) :
    Nonempty (NuclearPresentation T) := by
  let b := (Module.finBasis ℂ T.toLinearMap.range).equivFun.toContinuousLinearEquiv
  let A := b.toContinuousLinearMap.comp T.rangeRestrict
  let i := T.toLinearMap.range.subtypeL.comp b.symm.toContinuousLinearMap
  have h := (isNuclearOperator_factor_comps i (Subtype.val_injective.comp b.symm.injective) A
    (archNuclearityQuotient_nuclear_iff_finiteRank_coordinates A)).2
  have he : i.comp A = T := by ext x; exact congrArg Subtype.val (b.symm_apply_apply (T.rangeRestrict x))
  exact (isNuclearOperator_iff_nonempty_presentation T).mp (he ▸ h)

/-- Apply the sequence-space rank criterion with the uniformity of the given
topological additive group. -/
private theorem archNuclearityQuotient_nuclear_iff_finiteRank_sequence {E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] (e : E ≃L[ℂ] (ℕ → ℂ)) :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    ∀ T : E →L[ℂ] E, Nonempty (NuclearPresentation T) ↔
      FiniteDimensional ℂ T.toLinearMap.range := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : T2Space E := e.symm.toHomeomorph.t2Space
  let : PolynormableSpace ℂ E := e.PolynormableSpace
  intro T
  exact ⟨fun ⟨r⟩ ↦ archNuclearityQuotient_nuclear_iff_finiteRank_range e T r,
    archNuclearityQuotient_nuclear_iff_finiteRank_of_finite T⟩

/-- Paper: Remark 7.4.3.3, p. 373.
A nuclear endomorphism of the archimedean quotient has finite-dimensional range,
and every continuous finite-rank endomorphism admits a nuclear presentation.
Deviation: This gives the rank criterion on the space carrying the test action. -/
theorem archNuclearityQuotient_nuclear_iff_finiteRank :
    let Q := ArchNuclearityQuotient χ
    letI instArchUniformSec4 : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
    ∀ T : Q →L[ℂ] Q, Nonempty (NuclearPresentation T) ↔
      FiniteDimensional ℂ T.toLinearMap.range := by
  obtain ⟨e⟩ := archNuclearityStrongDual_finest_sequenceEquiv χ
  exact archNuclearityQuotient_nuclear_iff_finiteRank_sequence (E := ArchNuclearityQuotient χ) e

/-- In block coordinates, an operator acting on each block by a lower-triangular
Toeplitz matrix with entries `d i z` has values zero on the blocks where all those
entries vanish. -/
private theorem archNuclearityAction_nuclear_iff_vanish {Q : Type*} [AddCommGroup Q]
    [Module ℂ Q] (m : ℂ → ℕ) (d : ℕ → ℂ → ℂ)
    (e : Q ≃ₗ[ℂ] ({j : ℂ × ℕ // j.2 < m j.1} → ℂ)) (T : Q →ₗ[ℂ] Q)
    (hT : ∀ q (j : {j : ℂ × ℕ // j.2 < m j.1}), e (T q) j = ∑ i ∈ Finset.range (j.val.2 + 1),
      (j.val.2.choose i : ℂ) * d i j.val.1 *
        e q ⟨(j.val.1, j.val.2 - i), (Nat.sub_le _ _).trans_lt j.property⟩)
    (q : Q) (j : {j : ℂ × ℕ // j.2 < m j.1})
    (hj : j.val.1 ∉ {z : ℂ | ∃ k : Fin (m z), d k.val z ≠ 0}) :
    e (T q) j = 0 := by
  rw [hT]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  have hi' : i < m j.val.1 :=
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans_lt j.property
  have h0 : d i j.val.1 = 0 := by
    by_contra h
    exact hj ⟨⟨i, hi'⟩, h⟩
  rw [h0, mul_zero, zero_mul]

/-- Applying the operator to the first basis vector of the block at `z` gives the
column of entries `d k z` in that block, and zero in the other blocks. -/
private theorem archNuclearityAction_nuclear_iff_column {Q : Type*} [AddCommGroup Q]
    [Module ℂ Q] (m : ℂ → ℕ) (d : ℕ → ℂ → ℂ)
    (e : Q ≃ₗ[ℂ] ({j : ℂ × ℕ // j.2 < m j.1} → ℂ)) (T : Q →ₗ[ℂ] Q)
    (hT : ∀ q (j : {j : ℂ × ℕ // j.2 < m j.1}), e (T q) j = ∑ i ∈ Finset.range (j.val.2 + 1),
      (j.val.2.choose i : ℂ) * d i j.val.1 *
        e q ⟨(j.val.1, j.val.2 - i), (Nat.sub_le _ _).trans_lt j.property⟩)
    (z : ℂ) (hz : 0 < m z) (j : {j : ℂ × ℕ // j.2 < m j.1}) :
    e (T (e.symm (Pi.single ⟨(z, 0), hz⟩ 1))) j = if j.val.1 = z then d j.val.2 z else 0 := by
  classical
  rw [hT]
  simp only [LinearEquiv.apply_symm_apply]
  split_ifs with hjz
  · rw [Finset.sum_eq_single j.val.2]
    · have : (⟨(j.val.1, j.val.2 - j.val.2), (Nat.sub_le _ _).trans_lt j.property⟩ :
          {j : ℂ × ℕ // j.2 < m j.1}) = ⟨(z, 0), hz⟩ := Subtype.ext (by simp [hjz])
      rw [this, Pi.single_eq_same, mul_one, Nat.choose_self, Nat.cast_one, one_mul, hjz]
    · intro i hi hne
      have hlt : i < j.val.2 :=
        lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hne
      rw [Pi.single_eq_of_ne, mul_zero]
      intro h
      have := congrArg (fun x : {j : ℂ × ℕ // j.2 < m j.1} ↦ x.val.2) h
      simp only at this
      omega
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h
  · refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [Pi.single_eq_of_ne, mul_zero]
    intro h
    exact hjz (congrArg (fun x : {j : ℂ × ℕ // j.2 < m j.1} ↦ x.val.1) h)

/-- Linear-algebra core of Remark 7.4.3.3: a block lower-triangular operator on the
product of the jet blocks has finite rank exactly when only finitely many blocks
carry a nonzero entry. -/
private theorem archNuclearityAction_nuclear_iff_blocks {Q : Type*} [AddCommGroup Q]
    [Module ℂ Q] (m : ℂ → ℕ) (d : ℕ → ℂ → ℂ)
    (e : Q ≃ₗ[ℂ] ({j : ℂ × ℕ // j.2 < m j.1} → ℂ)) (T : Q →ₗ[ℂ] Q)
    (hT : ∀ q (j : {j : ℂ × ℕ // j.2 < m j.1}), e (T q) j = ∑ i ∈ Finset.range (j.val.2 + 1),
      (j.val.2.choose i : ℂ) * d i j.val.1 *
        e q ⟨(j.val.1, j.val.2 - i), (Nat.sub_le _ _).trans_lt j.property⟩) :
    FiniteDimensional ℂ (LinearMap.range T) ↔
      {z : ℂ | ∃ k : Fin (m z), d k.val z ≠ 0}.Finite := by
  classical
  let J := {j : ℂ × ℕ // j.2 < m j.1}
  let Z := {z : ℂ | ∃ k : Fin (m z), d k.val z ≠ 0}
  constructor
  · intro hfin
    choose k hk using fun z : Z ↦ z.property
    have hpos (z : Z) : 0 < m z.val := (Nat.zero_le _).trans_lt (k z).isLt
    let w (z : Z) : LinearMap.range T :=
      ⟨T (e.symm (Pi.single ⟨(z.val, 0), hpos z⟩ 1)), LinearMap.mem_range_self _ _⟩
    let Φ : (J → ℂ) →ₗ[ℂ] (Z → ℂ) :=
      LinearMap.pi fun z ↦ LinearMap.proj (⟨(z.val, (k z).val), (k z).isLt⟩ : J)
    let L : LinearMap.range T →ₗ[ℂ] (Z → ℂ) :=
      Φ.comp (e.toLinearMap.comp (LinearMap.range T).subtype)
    have hL (z : Z) : L (w z) = Pi.single z (d (k z).val z.val) := by
      funext z'
      change e (T (e.symm (Pi.single ⟨(z.val, 0), hpos z⟩ 1)))
        ⟨(z'.val, (k z').val), (k z').isLt⟩ = _
      rw [archNuclearityAction_nuclear_iff_column m d e T hT z.val (hpos z)]
      by_cases h : z' = z
      · subst h
        simp
      · have h' : z'.val ≠ z.val := fun he ↦ h (Subtype.ext he)
        simp [h', Pi.single_eq_of_ne h]
    have hli : LinearIndependent ℂ (L ∘ w) := by
      have : L ∘ w = fun z ↦ Pi.single z (d (k z).val z.val) := funext hL
      rw [this]
      exact Pi.linearIndependent_single_of_ne_zero hk
    have := (LinearIndependent.of_comp L hli).finite_of_isNoetherian
    exact Set.toFinite Z
  · intro hZ
    have : Finite Z := hZ.to_subtype
    let JZ := {j : J // j.val.1 ∈ Z}
    have : Finite JZ := by
      refine Finite.of_injective (β := Σ z : Z, Fin (m z.val))
        (fun j ↦ ⟨⟨j.val.val.1, j.property⟩, ⟨j.val.val.2, j.val.property⟩⟩) ?_
      intro a b h
      simp only [Sigma.mk.inj_iff] at h
      obtain ⟨h1, h2⟩ := h
      have h1' : a.val.val.1 = b.val.val.1 := congrArg Subtype.val h1
      apply Subtype.ext
      apply Subtype.ext
      refine Prod.ext h1' ?_
      have := (Fin.heq_ext_iff (by rw [h1'])).mp h2
      exact this
    let R : LinearMap.range T →ₗ[ℂ] (JZ → ℂ) :=
      (LinearMap.pi fun j : JZ ↦ LinearMap.proj (R := ℂ) (φ := fun _ : J ↦ ℂ) j.val).comp
        (e.toLinearMap.comp (LinearMap.range T).subtype)
    refine Module.Finite.of_injective R ?_
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨_, q, rfl⟩ hx
    apply Subtype.ext
    change T q = 0
    apply e.injective
    funext j
    rw [map_zero, Pi.zero_apply]
    by_cases hj : j.val.1 ∈ Z
    · exact congrFun hx ⟨j, hj⟩
    · exact archNuclearityAction_nuclear_iff_vanish m d e T hT q j hj

/-- Paper: Remark 7.4.3.3, p. 373.
The quotient action is nuclear exactly when it is nonzero on finitely many jet blocks.
Deviation: A block of length m vanishes when all multiplier derivatives of orders
strictly below m vanish at its center. This allows tests whose induced action is zero. -/
theorem archNuclearityAction_nuclear_iff (φ : 𝒟) :
    let D := archNuclearityDenominator χ
    let Q := ArchNuclearityQuotient χ
    letI instArchActionUniformSec4 : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
    ∀ T : Q →L[ℂ] Q, (∀ x : Θ₀(χ), T (D.mkQ x) = D.mkQ (Aθ(φ) x)) →
      (Nonempty (NuclearPresentation T) ↔
        {z : ℂ | ∃ k : Fin (archNuclearityMultiplicity χ τ hτ z),
          iteratedDeriv k.val (nuclearityTestMellin χ φ) z ≠ 0}.Finite) := by
  intro D Q T hT
  obtain ⟨e, he⟩ := archNuclearityQuotient_jetEquiv χ τ hτ
  have hjet (x : Θ₀(χ)) (j : ArchNuclearityJetIndex χ τ hτ) :
      archNuclearityJet χ τ hτ j x = iteratedDeriv j.val.2 ((Z(χ, τ, hτ)) x).val j.val.1 := by
    unfold archNuclearityJet
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, entireJet_apply]
    exact congrArg (fun g : ℂ → ℂ ↦ iteratedDeriv j.val.2 g j.val.1)
      (funext (schwartzBergmanEntireInclusion_apply _))
  have hblock (q : Q) (j : ArchNuclearityJetIndex χ τ hτ) :
      e (T q) j = ∑ i ∈ Finset.range (j.val.2 + 1),
        (j.val.2.choose i : ℂ) * iteratedDeriv i (nuclearityTestMellin χ φ) j.val.1 *
          e q ⟨(j.val.1, j.val.2 - i), (Nat.sub_le _ _).trans_lt j.property⟩ := by
    obtain ⟨x, rfl⟩ := D.mkQ_surjective q
    let v := (Z(χ, τ, hτ)) x
    have hv : Differentiable ℂ v.val := fun z ↦
      (v.property.2.1 z (mem_univ _)).differentiableAt (Filter.univ_mem' fun _ ↦ mem_univ _)
    have hprod : ((Z(χ, τ, hτ)) (Aθ(φ) x)).val = nuclearityTestMellin χ φ * v.val :=
      funext ((exists_polarThetaNuclearityAction χ τ hτ φ).choose_spec.1 x)
    rw [hT x, he, hjet, hprod, iteratedDeriv_mul
      ((differentiable_nuclearityTestMellin χ φ).contDiff.contDiffAt)
      hv.contDiff.contDiffAt]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [he, hjet]
  rw [archNuclearityQuotient_nuclear_iff_finiteRank χ T]
  exact archNuclearityAction_nuclear_iff_blocks (archNuclearityMultiplicity χ τ hτ)
    (fun i z ↦ iteratedDeriv i (nuclearityTestMellin χ φ) z) e.toLinearEquiv T.toLinearMap hblock

end Archimedean

end RiemannMasullo
