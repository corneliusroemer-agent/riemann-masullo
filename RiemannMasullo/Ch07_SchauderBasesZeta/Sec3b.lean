module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3b_PWLevels

import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.MittagLefflerLift
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

import all RiemannMasullo.Ch05_ThetaZSpaces.Sec1
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec2
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec5
import RiemannMasullo.Ch06_LocalGlobal.Sec2
import RiemannMasullo.Ch06_LocalGlobal.Sec3
import all RiemannMasullo.Ch07_SchauderBasesZeta.Sec2

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3a_OrbitalJets
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import RiemannMasullo.ForMathlib.MeasureTheory.Integral.ProdPi
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Complex.ExpPolynomial

import all RiemannMasullo.Ch03_IdelicZeta.Sec3

/-! # §7.3.2–7.3.4 Paley–Wiener levels and archimedean principal parts

The finsets in this file list the finite places. Each S-local stage also
contains all the archimedean places. The PW constructions use the restriction
of the character to the norm-one group, which determines its theta isotype.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open Filter Function IsDedekindDomain NumberField Set Topology
open scoped NNReal NumberField.AdeleRing
set_option quotPrecheck false
set_option maxHeartbeats 600000
variable {F : Type*} [Field F] [NumberField F]
variable {S T R : Finset (HeightOneSpectrum (𝓞 F))}
local notation "C₁" => (ideleClassNorm F).ker
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "J(" T ")" => SIdeleQuotient F T
local notation "m(" T ")" => sIdeleQuotientNorm F T
local notation "J₁(" T ")" => (m(T)).ker
local notation "B(" T ")" => SchwartzBruhat (Multiplicative (SAdeleRing F T))
local notation "Θ(" T ", " ω ")" => SLocalHomogeneousThetaSpace F T ω
local notation "q(" T ", " ω ")" => (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F T ω)).mkQ
local notation "Z₀(" T ")" => sAdelePolarSubspace F T
local notation "Π(" h ")" => sAdeleSchwartzTransition F h
local notation "PicTrivial" => Subsingleton (CommRing.Pic ((S : Set V).integer F))
local notation "A(" T ", " ω ")" =>
  (existsUnique_sLocalHomogeneousThetaAction (F := F) (S := T) ω).exists.choose
local notation "PV(" h ", " ω ")" => sLocalHomogeneousThetaPrincipalValue (F := F) h ω
local notation "count(" S ")" => (Fintype.card (InfinitePlace F) + Finset.card S)
local notation "size(" R ")" => (∏ v ∈ R, (v.asIdeal.absNorm : ℝ))
local notation "large(" g ")" => (1 ≤ ((m(T) g).val : ℝ))
local notation "descend(" h ", " ω ", " hu ")" =>
  sLocalNormOneCharacter (F := F) T ω
    (NormOneCharacterUnramifiedOutside.mono (F := F) hu h)
local notation "onComponent(" c ", " ω ")" =>
  (normOneRestriction (m(S)) c =
    (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ω)
local notation "inBand(" K ", " f ")" =>
  (HasCompactSupport (sAdeleSchwartzFourier f).val ∧
    tsupport (sAdeleSchwartzFourier f).val ⊆ Multiplicative.toAdd ⁻¹' K)
local notation "level(" h ", " K ", " D ", " ω ")" =>
  (((sLocalPWTests h K ⊓ D).map (q(_, ω))).topologicalClosure)


section ArchimedeanPoles

local notation "Xₛ" => QuasiCharacter J(S)
local notation "fullPV(" ω ")" => (PV((Finset.Subset.refl S), ω)).range
local notation "noPoles(" ω ")" => sLocalThetaPoleBound (F := F) (S := S) ω (fun _ ↦ 0)
local notation "chart(" c ")" => quasiCharacterNormTwist (m(S))
  (isProperMap_sIdeleQuotientNorm F S).continuous c
local notation "shift(" c ", " z ")" => chart(c) z
local notation "arch(" c ")" => sLocalArchPolePlaces (F := F) (S := S) c
local notation "depths" => (InfinitePlace F → ℕ)

/-- Paper: Notation 7.3.4.1, p. 364.
The selected centers on a component are among the first specified number of poles
at one or more archimedean places, starting at the rightmost pole.
Deviation: The real and complex cutoff tuples are combined into a single
place-indexed family. Local poles are ranked by positive real norm shifts, so a
cutoff of n includes n + 1 local poles. -/
def sLocalGammaPoleCutoff (ω : PontryaginDual J₁(S)) (N : depths) : Set Xₛ :=
  {c | onComponent(c, ω) ∧
    ∃ w ∈ arch(c), ({t : ℝ | 0 < t ∧ w ∈ arch(shift(c, (t : ℂ)))} : Set ℝ).encard ≤ N w}

variable (S) in
/-- Paper: Notation 7.3.4.1, p. 364.
The zero cutoff selects the trivial quasi-character on the trivial component
and excludes its shift down by two. -/
theorem sLocalGammaPoleCutoff_zero :
    (1 : Xₛ) ∈ sLocalGammaPoleCutoff (F := F) (S := S) 1 (fun _ ↦ 0) ∧
      shift((1 : Xₛ), (-2 : ℂ)) ∉ sLocalGammaPoleCutoff (F := F) (S := S) 1 (fun _ ↦ 0) := by
  classical
  -- Twisting twice adds the exponents.
  have htw (a z : ℂ) : shift(shift((1 : Xₛ), a), z) = shift((1 : Xₛ), z + a) := by
    ext1 g
    change (1 : Xₛ) g * _ ^ a * _ ^ z = (1 : Xₛ) g * _ ^ (z + a)
    rw [add_comm, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
      (NNReal.coe_ne_zero.mpr (m(S) g).ne_zero)), mul_assoc]
  have h10 : shift((1 : Xₛ), 0) = 1 := by
    ext1 g
    change (1 : Xₛ) g * _ ^ (0 : ℂ) = (1 : Xₛ) g
    rw [Complex.cpow_zero, mul_one]
  -- The archimedean Euler factor along the chart through the trivial character.
  let G : InfinitePlace F → ℂ → ℂ := fun w s ↦
    if w.IsReal then Complex.Gammaℝ s else Complex.Gammaℂ s / 2
  have hres (w : InfinitePlace F) (s : ℂ) (g : w.Completionˣ) :
      sLocalInfiniteRestriction w (shift((1 : Xₛ), s)) g =
        ((((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ) g : ℝ≥0) : ℝ) :
          ℂ) ^ s := by
    have h1 : shift((1 : Xₛ), s) = quasiCharacterNormTwist (m(S))
        (isProperMap_sIdeleQuotientNorm F S).continuous
        ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp
          (1 : PontryaginDual J(S))) s := by
      ext1 x
      change (1 : ℂ) * _ = ((1 : Circle) : ℂ) * _
      rw [Circle.coe_one]
      rfl
    rw [h1]
    exact sLocalInfiniteRestriction_normTwist w s g
  have hE (w : InfinitePlace F) (s : ℂ) :
      infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (shift((1 : Xₛ), s))) = G w s := by
    by_cases hw : w.IsReal
    · let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
      have hshape : ∀ x : ℝˣ, sLocalInfiniteRestriction w (shift((1 : Xₛ), s))
          (Units.map e.toMonoidHom x) =
            (‖(x : ℝ)‖ : ℂ) ^ s * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ (0 : Fin 2).val := by
        intro x
        have hn : ‖(e (x : ℝ) : w.Completion)‖ = ‖(x : ℝ)‖ :=
          (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
            (map_zero e) (x : ℝ)
        have hm : (((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ)
            (Units.map e.toMonoidHom x) : ℝ≥0) : ℝ) = ‖(x : ℝ)‖ := by
          simp [InfinitePlace.mult, hw, hn]
        rw [hres, hm, Fin.val_zero, pow_zero, mul_one]
      have hq := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w
        (shift((1 : Xₛ), s)))).unique (realLocalEulerParameters w hw
          (sLocalInfiniteRestriction w (shift((1 : Xₛ), s)))).exists.choose_spec
        (y₂ := (s, 0)) hshape
      simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hq, G, ite_true, Fin.val_zero,
        Nat.cast_zero, add_zero]
    · have hwc := InfinitePlace.not_isReal_iff_isComplex.mp hw
      let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc).symm
      have hshape : ∀ x : ℂˣ, sLocalInfiniteRestriction w (shift((1 : Xₛ), s))
          (Units.map e.toMonoidHom x) =
            ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ (0 : ℤ) := by
        intro x
        have hn : ‖(e (x : ℂ) : w.Completion)‖ = ‖(x : ℂ)‖ :=
          (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
            hwc).symm.isometry.norm_map_of_map_zero (map_zero e) (x : ℂ)
        have hm : (((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ)
            (Units.map e.toMonoidHom x) : ℝ≥0) : ℝ) = ‖(x : ℂ)‖ ^ 2 := by
          simp [InfinitePlace.mult, hw, hn]
        rw [hres, hm, zpow_zero, mul_one]
      have hq := (complexLocalEulerParameters w hwc (sLocalInfiniteRestriction w
        (shift((1 : Xₛ), s)))).unique (complexLocalEulerParameters w hwc
          (sLocalInfiniteRestriction w (shift((1 : Xₛ), s)))).exists.choose_spec
        (y₂ := (s, 0)) hshape
      simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hq, G, ite_false, Int.natAbs_zero,
        Nat.cast_zero, zero_div, add_zero]
  -- `G w` has a pole at zero and is regular at every positive real point.
  have hinv (w : InfinitePlace F) : Differentiable ℂ (fun s ↦ (G w s)⁻¹) := by
    by_cases hw : w.IsReal
    · simpa only [G, hw, ite_true] using Complex.differentiable_Gammaℝ_inv
    · simp only [G, hw, ite_false, inv_div]
      exact Complex.differentiable_Gammaℂ_inv.const_mul 2
  have hmer (w : InfinitePlace F) (x : ℂ) : MeromorphicAt (G w) x := by
    convert ((hinv w).analyticAt x).meromorphicAt.inv using 1
    funext s
    simp
  have hpole (w : InfinitePlace F) : meromorphicOrderAt (G w) 0 < 0 := by
    have hlim : ∃ c ≠ (0 : ℂ), Tendsto (fun s ↦ s * G w s) (𝓝[≠] 0) (𝓝 c) := by
      by_cases hw : w.IsReal
      · exact ⟨2, two_ne_zero, by simpa only [G, hw, ite_true] using Complex.Gammaℝ_residue_zero⟩
      · refine ⟨1, one_ne_zero, ?_⟩
        have := Complex.Gammaℂ_residue_zero.div_const 2
        simp only [div_self (two_ne_zero' ℂ)] at this
        simpa only [G, hw, ite_false, mul_div_assoc] using this
    have h0 := (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero
      (analyticAt_id.meromorphicAt.mul (hmer w 0))).mp hlim
    have hm := meromorphicOrderAt_mul (f := id) analyticAt_id.meromorphicAt (hmer w 0)
    change meromorphicOrderAt (id * G w) 0 = 0 at h0
    rw [hm, meromorphicOrderAt_id] at h0
    cases hn : meromorphicOrderAt (G w) 0 with
    | top => rw [hn] at h0; simp at h0
    | coe n =>
      rw [hn] at h0
      have : 1 + n = 0 := by exact_mod_cast h0
      exact_mod_cast (by omega : n < 0)
  have hreg (w : InfinitePlace F) (t : ℝ) (ht : 0 < t) :
      ¬ meromorphicOrderAt (fun z ↦ G w (z + t)) 0 < 0 := by
    have hne : (G w t)⁻¹ ≠ 0 := by
      refine inv_ne_zero ?_
      by_cases hw : w.IsReal
      · simpa only [G, hw, ite_true] using Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using ht)
      · simp only [G, hw, ite_false, Complex.Gammaℂ_def]
        refine div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) two_ne_zero
        · exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by simpa using ht.ne')).mpr
            (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        · exact Complex.Gamma_ne_zero_of_re_pos (by simpa using ht)
    have han : AnalyticAt ℂ (fun z ↦ ((G w (z + t))⁻¹)⁻¹) 0 :=
      (((hinv w).analyticAt _).comp (f := fun z : ℂ ↦ z + t) (by fun_prop)).inv
        (by simpa using hne)
    simp only [inv_inv] at han
    exact not_lt.mpr han.meromorphicOrderAt_nonneg
  have harch (a : ℂ) (w : InfinitePlace F) :
      w ∈ arch(shift((1 : Xₛ), a)) ↔ meromorphicOrderAt (fun z ↦ G w (z + a)) 0 < 0 := by
    simp only [sLocalArchPolePlaces, Finset.mem_filter, Finset.mem_univ, true_and]
    refine iff_of_eq (congrArg (· < 0) (congrArg (meromorphicOrderAt · 0) ?_))
    funext z
    rw [htw, hE]
  have h1 (w : InfinitePlace F) : w ∈ arch((1 : Xₛ)) := by
    rw [← h10, harch]
    simpa only [add_zero] using hpole w
  refine ⟨⟨?_, Classical.arbitrary _, h1 _, ?_⟩, ?_⟩
  · ext g
    change (1 : ℂ) = ((1 : Circle) : ℂ)
    rw [Circle.coe_one]
  · have hempty : {t : ℝ | 0 < t ∧ Classical.arbitrary (InfinitePlace F) ∈
        arch(shift((1 : Xₛ), (t : ℂ)))} = ∅ :=
      Set.eq_empty_of_forall_notMem fun t ⟨ht, hw⟩ ↦ hreg _ t ht ((harch _ _).mp hw)
    rw [hempty, Set.encard_empty]
    exact zero_le
  · rintro ⟨-, w, -, hcard⟩
    have h2 : (2 : ℝ) ∈ {t : ℝ | 0 < t ∧ w ∈ arch(shift(shift((1 : Xₛ), (-2 : ℂ)), (t : ℂ)))} := by
      refine ⟨two_pos, ?_⟩
      rw [htw, show ((2 : ℝ) : ℂ) + -2 = 0 by push_cast; ring, h10]
      exact h1 w
    have hc : _ ≤ (0 : ℕ∞) := hcard
    exact (Set.encard_pos.mpr ⟨2, h2⟩).ne' (nonpos_iff_eq_zero.mp hc)

local notation "ΓIndex(" ω ", " U ")" =>
  {j : Xₛ × ℕ // onComponent(j.1, ω) ∧ j.1 ∈ U ∧ 0 < j.2 ∧ j.2 ≤ (arch(j.1)).card}
local notation "ΓCoeff(" ω ", " j ")" =>
  ((sLocalThetaPrincipalPartCoeff (F := F) (S := S) ω (j).val.1 (j).property.1 (j).val.2).comp
    (fullPV(ω)).subtypeL)

/-- Paper: Notation 7.3.4.1, p. 364.
The filtered subspace of the full finite principal-value image has no poles at
the selected archimedean centers. It carries the induced topology.
Deviation: Cutoffs are indexed by places. Increasing all local cutoffs gives
the filtration inclusions. -/
def sLocalGammaFiltration (ω : PontryaginDual J₁(S)) (N : depths) :
    Submodule ℂ (fullPV(ω)) :=
  ⨅ j : ΓIndex(ω, sLocalGammaPoleCutoff (F := F) (S := S) ω N), (ΓCoeff(ω, j)).ker

/-- On a full finite principal value only archimedean poles remain. Express the
pole bound of §5.3.4 in the norm coordinate centered at the given character. -/
private theorem gammaFiltration_principalValue_bound (g : B(S)) (c : Xₛ) :
    sLocalPolarMultiplicity (sAdelePrincipalValue F (Finset.Subset.refl S) g) c ≤
      (arch(c)).card := by
  classical
  obtain ⟨χ, a, rfl⟩ := exists_sLocalNormTwist (F := F) (S := S) c
  let d : Xₛ := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
  have translate (H : Xₛ → ℂ) :
      meromorphicOrderAt (fun z : ℂ ↦ H (shift(shift(d, a), z))) 0 =
        meromorphicOrderAt (fun z : ℂ ↦ H (shift(d, z))) a := by
    have e : (fun z : ℂ ↦ H (shift(shift(d, a), z))) =
        (fun z : ℂ ↦ H (shift(d, z))) ∘ (· + a) := by
      funext z
      rw [normTwist_normTwist]
      rfl
    rw [e, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt, zero_add]
  have places : (arch(shift(d, a))).card = sLocalArchimedeanPoleMultiplicity χ a := by
    unfold sLocalArchPolePlaces sLocalArchimedeanPoleMultiplicity
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro w _
    rw [translate (fun b ↦ infiniteLocalEulerFactor w (sLocalInfiniteRestriction w b))]
  let p := sAdelePrincipalValue F (Finset.Subset.refl S) g
  change (-(meromorphicOrderAt (fun z : ℂ ↦ sLocalIdelicZFunction p (shift(shift(d, a), z))) 0).untop₀).toNat ≤ _
  rw [translate (sLocalIdelicZFunction p), places]
  have hb := sLocalIdelicZFunction_principalValue_pole_bound g χ a
  change ((-(sLocalArchimedeanPoleMultiplicity χ a : ℤ) : ℤ) : WithTop ℤ) ≤
    meromorphicOrderAt (fun z : ℂ ↦ sLocalIdelicZFunction p (shift(d, z))) a at hb
  generalize meromorphicOrderAt (fun z : ℂ ↦ sLocalIdelicZFunction p (shift(d, z))) a = o at hb ⊢
  induction o using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    have hn := WithTop.coe_le_coe.mp hb
    simp only [WithTop.untop₀_coe]
    omega

/-- Paper: Notation 7.3.4.1, p. 364.
A class in the full finite principal-value image is in a filtered stage exactly
when its representative's Mellin transform has no poles at the selected centers. -/
theorem mem_sLocalGammaFiltration (ω : PontryaginDual J₁(S)) (N : depths)
    (x : fullPV(ω)) (f : B(S)) (_hf : q(S, ω) f = x.val) :
    x ∈ sLocalGammaFiltration ω N ↔
      ∀ c ∈ sLocalGammaPoleCutoff (F := F) (S := S) ω N,
        0 ≤ meromorphicOrderAt (fun z : ℂ ↦ sLocalIdelicZFunction f (shift(c, z))) 0 := by
  classical
  change (x ∈ ⨅ j : ΓIndex(ω, sLocalGammaPoleCutoff (F := F) (S := S) ω N),
    (ΓCoeff(ω, j)).ker) ↔ _
  rw [Submodule.mem_iInf]
  constructor
  · intro h c hc
    rw [← sLocalPolarMultiplicity_eq_zero_iff]
    by_contra hne
    let k := sLocalPolarMultiplicity f c
    have hk : 0 < k := Nat.pos_of_ne_zero hne
    let L := sLocalThetaPrincipalPartCoeff ω c hc.1 k
    have hL : L x.val ≠ 0 := by
      rw [← _hf]
      exact mem_sLocalThetaPoleBound_iff_leading (sLocalZ_centered f c).1 hk rfl
    obtain ⟨y, hy⟩ := x.property
    obtain ⟨g, rfl⟩ := (Submodule.mkQ_surjective _) y
    have hg : sLocalPrincipalPartCoeff c k (sAdelePrincipalValue F (Finset.Subset.refl S) g) ≠ 0 := by
      rw [← hy] at hL
      exact hL
    have hle := (sLocalPrincipalPartCoeff_ne_zero_imp_pole c k hk _ hg).2
    let j : ΓIndex(ω, sLocalGammaPoleCutoff (F := F) (S := S) ω N) :=
      ⟨(c, k), hc.1, hc, hk, hle.trans (gammaFiltration_principalValue_bound g c)⟩
    exact hL (h j)
  · intro h j
    change sLocalThetaPrincipalPartCoeff ω j.val.1 j.property.1 j.val.2 x.val = 0
    rw [← _hf]
    change sLocalPrincipalPartCoeff j.val.1 j.val.2 f = 0
    by_contra hne
    have hle := (sLocalPrincipalPartCoeff_ne_zero_imp_pole _ _ j.property.2.2.1 f hne).2
    rw [(sLocalPolarMultiplicity_eq_zero_iff f _).2 (h _ j.property.2.1)] at hle
    exact (not_lt_of_ge hle) j.property.2.2.1

/-- Paper: Notation 7.3.4.1, p. 364.
The denominator of the archimedean polar quotient is the subspace with entire Mellin transform.
Deviation: Uses the equivalent zero-pole-bound model for the theta image of S₀₀ from §7.2. -/
def sLocalGammaEntireSubmodule (ω : PontryaginDual J₁(S)) : Submodule ℂ (fullPV(ω)) :=
  (noPoles(ω)).comap (fullPV(ω)).subtype

local notation "Γker(" ω ")" => sLocalGammaEntireSubmodule (F := F) (S := S) ω

/-- Paper: Notation 7.3.4.1, p. 364.
The archimedean polar quotient divides the full finite principal-value image
by the subspace with entire Mellin transform, and carries the quotient topology.

This is a `def` with its own instances, not an `abbrev`, so that instance terms over it do
not spell out its definition (#5398). -/
def SLocalGammaOrbitalQuotient (ω : PontryaginDual J₁(S)) := fullPV(ω) ⧸ Γker(ω)

namespace SLocalGammaOrbitalQuotient

instance instAddCommGroup (ω : PontryaginDual J₁(S)) :
    AddCommGroup (SLocalGammaOrbitalQuotient ω) :=
  inferInstanceAs (AddCommGroup (fullPV(ω) ⧸ Γker(ω)))

instance instModule (ω : PontryaginDual J₁(S)) : Module ℂ (SLocalGammaOrbitalQuotient ω) :=
  inferInstanceAs (Module ℂ (fullPV(ω) ⧸ Γker(ω)))

instance instTopologicalSpace (ω : PontryaginDual J₁(S)) :
    TopologicalSpace (SLocalGammaOrbitalQuotient ω) :=
  inferInstanceAs (TopologicalSpace (fullPV(ω) ⧸ Γker(ω)))

instance instIsTopologicalAddGroup (ω : PontryaginDual J₁(S)) :
    IsTopologicalAddGroup (SLocalGammaOrbitalQuotient ω) :=
  inferInstanceAs (IsTopologicalAddGroup (fullPV(ω) ⧸ Γker(ω)))

instance instContinuousSMul (ω : PontryaginDual J₁(S)) :
    ContinuousSMul ℂ (SLocalGammaOrbitalQuotient ω) :=
  inferInstanceAs (ContinuousSMul ℂ (fullPV(ω) ⧸ Γker(ω)))

end SLocalGammaOrbitalQuotient

/-- Paper: Notation 7.3.4.1, p. 364.
A representative of the zero coset has a Mellin transform with no poles on the
component, and the entire-Mellin subspace consists of these representatives. -/
theorem mem_sLocalGammaEntireSubmodule (ω : PontryaginDual J₁(S))
    (x : fullPV(ω)) (f : B(S)) (_hf : q(S, ω) f = x.val) :
    x ∈ Γker(ω) ↔
      ∀ c : Xₛ, onComponent(c, ω) →
        0 ≤ meromorphicOrderAt (fun z : ℂ ↦ sLocalIdelicZFunction (F := F) (S := S) f (shift(c, z))) 0 :=
  by
  -- A germ with no pole has vanishing polar Laurent coefficients.
  have hres (Z : ℂ → ℂ) (hZ : MeromorphicAt Z 0) (h0 : 0 ≤ meromorphicOrderAt Z 0) (N : ℕ)
      (hN : 0 < N) : complexResidue (fun z ↦ Z z / z ^ (-(N : ℤ) + 1)) 0 = 0 := by
    have ha := hZ.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.1 h0
    have he : (fun z ↦ Z z / z ^ (-(N : ℤ) + 1)) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun z ↦ z ^ N * toMeromorphicNFAt Z 0 z / (z - 0)) := by
      filter_upwards [hZ.eq_nhdsNE_toMeromorphicNFAt, self_mem_nhdsWithin] with z hz hz0
      have hz0' : z ≠ 0 := hz0
      rw [hz, sub_zero, zpow_add₀ hz0', zpow_one, zpow_neg, zpow_natCast]
      field_simp
    have hg : AnalyticAt ℂ (fun z ↦ z ^ N * toMeromorphicNFAt Z 0 z) 0 :=
      (analyticAt_id.pow N).mul ha
    rw [mem_sLocalThetaPoleBound_iff_residue_congr he, complexResidue_div_sub hg]
    simp [zero_pow hN.ne']
  change x.val ∈ noPoles(ω) ↔ _
  rw [← _hf]
  constructor
  · intro hx c hc
    rw [← sLocalPolarMultiplicity_eq_zero_iff]
    by_contra hne
    have hN : 0 < sLocalPolarMultiplicity f c := Nat.pos_of_ne_zero hne
    let T := sLocalThetaPrincipalPartCoeff ω c hc (sLocalPolarMultiplicity f c)
    have hle : noPoles(ω) ≤ LinearMap.ker (T : Θ(S, ω) →ₗ[ℂ] ℂ) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, rfl, hg⟩
      change complexResidue (fun z ↦ sLocalIdelicZFunction g (shift(c, z)) /
        z ^ (-((sLocalPolarMultiplicity f c : ℕ) : ℤ) + 1)) 0 = 0
      exact hres _ (sLocalZ_centered g c).1
        ((sLocalPolarMultiplicity_eq_zero_iff g c).1 (Nat.le_zero.1 (hg c hc))) _ hN
    have h0 : complexResidue (fun z ↦ sLocalIdelicZFunction f (shift(c, z)) /
        z ^ (-((sLocalPolarMultiplicity f c : ℕ) : ℤ) + 1)) 0 = 0 := hle hx
    exact mem_sLocalThetaPoleBound_iff_leading (sLocalZ_centered f c).1 hN rfl h0
  · intro h
    exact Submodule.subset_span
      ⟨f, rfl, fun c hc ↦ ((sLocalPolarMultiplicity_eq_zero_iff f c).2 (h c hc)).le⟩

/-- Paper: Notation 7.3.4.1, p. 364.
The archimedean polar quotient is Fréchet. -/
theorem sLocalGammaOrbitalQuotient_frechet (ω : PontryaginDual J₁(S)) :
    let P := Γker(ω)
    @IsFrechetTVS _ (Submodule.Quotient.addCommGroup P) (Submodule.Quotient.module P)
      (QuotientModule.Quotient.topologicalSpace P) := by
  intro P
  have hP : IsClosed (P : Set (fullPV(ω))) :=
    (sLocalThetaPoleBound_isClosed (F := F) (S := S) ω (fun _ ↦ 0)).preimage continuous_subtype_val
  have hR := (sLocalHomogeneousThetaPrincipalValue_isClosedEmbedding (Finset.Subset.refl S) ω).isClosed_range
  exact isFrechetTVS_quotient
    (isFrechetTVS_of_isClosedEmbedding (fullPV(ω)).subtypeL ((fullPV(ω)).isClosedEmbedding_subtypeL hR)
      (sLocalHomogeneousThetaSpace_frechet (F := F) (S := S) ω)) P hP

/-- Paper: Notation 7.3.4.1, p. 364.
The archimedean polar quotient is nuclear. -/
theorem sLocalGammaOrbitalQuotient_nuclear (ω : PontryaginDual J₁(S)) :
    let P := Γker(ω)
    @IsNuclearTVS _ (Submodule.Quotient.addCommGroup P) (Submodule.Quotient.module P)
      (QuotientModule.Quotient.topologicalSpace P) := by
  intro P
  have hR := isNuclearTVS_submodule
    (sLocalHomogeneousThetaSpace_nuclear (F := F) (S := S) ω) (fullPV(ω))
  let := hR.2.1
  let : IsTopologicalAddGroup (fullPV(ω)) := PolynormableSpace.isTopologicalAddGroup ℂ _
  have hP : IsClosed (P : Set (fullPV(ω))) :=
    (sLocalThetaPoleBound_isClosed (F := F) (S := S) ω (fun _ ↦ 0)).preimage continuous_subtype_val
  let : T3Space (fullPV(ω) ⧸ P) := Submodule.t3_quotient_of_isClosed P
  let : T2Space (fullPV(ω) ⧸ P) := @T25Space.t2Space _ _ T3Space.t25Space
  exact isNuclearTVS_quotient hR P

/-- Paper: Notation 7.3.4.1, p. 364.
Increasing all local cutoffs decreases the corresponding subspace.
Deviation: Uses the pointwise order. Lexicographic order need not give nested stages. -/
theorem sLocalGammaFiltration_antitone (ω : PontryaginDual J₁(S)) :
    Antitone (sLocalGammaFiltration ω) := by
  intro N N' hN
  unfold sLocalGammaFiltration
  refine le_iInf fun j ↦ iInf_le_of_le ⟨j.val, j.property.1, ?_, j.property.2.2⟩ le_rfl
  obtain ⟨hc, w, hw, hcard⟩ := j.property.2.1
  exact ⟨hc, w, hw, hcard.trans (by exact_mod_cast hN w)⟩

private theorem isClosed_iInf_ker {E ι : Type*} [AddCommMonoid E] [Module ℂ E]
    [TopologicalSpace E] (f : ι → E →L[ℂ] ℂ) :
    IsClosed (↑(⨅ i, (f i).ker) : Set E) := by
  rw [Submodule.coe_iInf]
  exact isClosed_iInter fun i ↦ (f i).isClosed_ker

/-- Paper: Theorem 7.3.4.1(1), p. 364.
Each stage of the archimedean pole filtration is closed. -/
theorem sLocalGammaFiltration_isClosed (ω : PontryaginDual J₁(S)) (N : depths) :
    IsClosed (sLocalGammaFiltration ω N : Set (fullPV(ω))) := by
  exact isClosed_iInf_ker
    (fun j : ΓIndex(ω, sLocalGammaPoleCutoff (F := F) (S := S) ω N) ↦ ΓCoeff(ω, j))

private theorem meromorphicOrderAt_gamma_lt_zero_iff (u : ℂ) :
    meromorphicOrderAt (fun z : ℂ ↦ Complex.Gamma (z + u)) 0 < 0 ↔ ∃ m : ℕ, u = -(m : ℂ) := by
  have hg : ∀ y, AnalyticAt ℂ (fun x : ℂ ↦ (Complex.Gamma x)⁻¹) y := fun y ↦
    Complex.differentiable_one_div_Gamma.analyticAt y
  have hinv (y : ℂ) : meromorphicOrderAt Complex.Gamma y =
      -meromorphicOrderAt (fun x : ℂ ↦ (Complex.Gamma x)⁻¹) y := by
    have heq : (fun x : ℂ ↦ (Complex.Gamma x)⁻¹)⁻¹ = Complex.Gamma := by
      funext x; simp
    conv_lhs => rw [← heq, meromorphicOrderAt_inv]
  have hcomp : meromorphicOrderAt (fun z : ℂ ↦ Complex.Gamma (z + u)) 0 =
      meromorphicOrderAt Complex.Gamma u := by
    change meromorphicOrderAt (Complex.Gamma ∘ (· + u)) 0 = meromorphicOrderAt Complex.Gamma u
    simpa [zero_add] using meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt
      (f := Complex.Gamma) (x := (0 : ℂ)) (c := u)
  rw [hcomp]
  clear hcomp
  constructor
  · intro hlt
    by_contra hnot
    have hne : (Complex.Gamma u)⁻¹ ≠ 0 := inv_ne_zero (Complex.Gamma_ne_zero fun m ↦ by
      intro hm; exact hnot ⟨m, hm⟩)
    have han : AnalyticAt ℂ Complex.Gamma u :=
      ((hg u).inv hne).congr (Filter.Eventually.of_forall fun x ↦ by simp)
    exact not_lt_of_ge han.meromorphicOrderAt_nonneg hlt
  · rintro ⟨m, rfl⟩
    rw [hinv]
    have hstep (y : ℂ) : meromorphicOrderAt (fun x : ℂ ↦ (Complex.Gamma x)⁻¹) y =
        meromorphicOrderAt (id : ℂ → ℂ) y +
          meromorphicOrderAt (fun x : ℂ ↦ (Complex.Gamma x)⁻¹) (y + 1) := by
      have heq : (fun x : ℂ ↦ (Complex.Gamma x)⁻¹) =
          (id : ℂ → ℂ) * ((fun x : ℂ ↦ (Complex.Gamma x)⁻¹) ∘ (· + 1)) := by
        funext x
        exact Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one x
      have hc : MeromorphicAt ((fun x : ℂ ↦ (Complex.Gamma x)⁻¹) ∘ (· + 1)) y :=
        ((hg (y + 1)).comp (f := fun x : ℂ ↦ x + 1) (by fun_prop)).meromorphicAt
      calc meromorphicOrderAt (fun x : ℂ ↦ (Complex.Gamma x)⁻¹) y
          = meromorphicOrderAt ((id : ℂ → ℂ) *
              ((fun x : ℂ ↦ (Complex.Gamma x)⁻¹) ∘ (· + 1))) y := by rw [← heq]
        _ = _ := by
          rw [meromorphicOrderAt_mul analyticAt_id.meromorphicAt hc,
            meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
    have hzero {f : ℂ → ℂ} {y : ℂ} (hf : AnalyticAt ℂ f y) (hy : f y ≠ 0) :
        meromorphicOrderAt f y = 0 := by
      rw [hf.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr hy), ENat.map_zero,
        CharP.cast_eq_zero, WithTop.coe_zero]
    have h1 : meromorphicOrderAt (fun x : ℂ ↦ (Complex.Gamma x)⁻¹) (-(m : ℂ)) = 1 := by
      induction m with
      | zero =>
        rw [hstep, Nat.cast_zero, neg_zero, zero_add, meromorphicOrderAt_id,
          hzero (hg 1) (by simp [Complex.Gamma_one]), add_zero]
      | succ k ih =>
        rw [hstep]
        have hne : -((k + 1 : ℕ) : ℂ) ≠ 0 := by norm_cast
        have h0 : meromorphicOrderAt (id : ℂ → ℂ) (-((k + 1 : ℕ) : ℂ)) = 0 :=
          hzero analyticAt_id hne
        have hadd : -((k + 1 : ℕ) : ℂ) + 1 = -(k : ℂ) := by push_cast; ring
        rw [h0, zero_add, hadd, ih]
    rw [h1]
    decide

private theorem meromorphicOrderAt_gammaR_lt_zero_iff (u : ℂ) :
    meromorphicOrderAt (fun z : ℂ ↦ Complex.Gammaℝ (z + u)) 0 < 0 ↔
      ∃ m : ℕ, u = -(2 * (m : ℂ)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have heq : (fun z : ℂ ↦ Complex.Gammaℝ (z + u)) =
      (fun z : ℂ ↦ (Real.pi : ℂ) ^ (-(z + u) / 2)) * (fun z : ℂ ↦ Complex.Gamma ((z + u) / 2)) := by
    funext z
    rfl
  have he_an : AnalyticAt ℂ (fun z : ℂ ↦ (Real.pi : ℂ) ^ (-(z + u) / 2)) 0 := by
    have hdiff : Differentiable ℂ (fun z : ℂ ↦ (Real.pi : ℂ) ^ (-(z + u) / 2)) :=
      fun z ↦ (((differentiableAt_id.add (differentiableAt_const u)).neg.div_const 2).const_cpow
        (Or.inl hpi))
    exact hdiff.analyticAt 0
  have he_ne : (Real.pi : ℂ) ^ (-(0 + u) / 2) ≠ 0 := by
    by_cases h0 : -(0 + u) / 2 = 0
    · rw [h0, Complex.cpow_zero]; exact one_ne_zero
    · exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero h0).mpr hpi
  have he_ord : meromorphicOrderAt (fun z : ℂ ↦ (Real.pi : ℂ) ^ (-(z + u) / 2)) 0 = 0 := by
    have hord : analyticOrderAt (fun z : ℂ ↦ (Real.pi : ℂ) ^ (-(z + u) / 2)) 0 = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr he_ne)
    rw [he_an.meromorphicOrderAt_eq, hord, ENat.map_zero, CharP.cast_eq_zero, WithTop.coe_zero]
  have hG_mer : MeromorphicAt (fun z : ℂ ↦ Complex.Gamma ((z + u) / 2)) 0 := by
    have h1 : AnalyticAt ℂ (fun z : ℂ ↦ (Complex.Gamma ((z + u) / 2))⁻¹) 0 :=
      (Complex.differentiable_one_div_Gamma.analyticAt _).comp (by fun_prop)
    convert h1.meromorphicAt.inv using 1
    funext z; simp
  have hmul : meromorphicOrderAt (fun z : ℂ ↦ Complex.Gammaℝ (z + u)) 0 =
      meromorphicOrderAt (fun z : ℂ ↦ Complex.Gamma ((z + u) / 2)) 0 := by
    rw [heq, meromorphicOrderAt_mul he_an.meromorphicAt hG_mer, he_ord, zero_add]
  have hcomp : meromorphicOrderAt (fun z : ℂ ↦ Complex.Gamma ((z + u) / 2)) 0 =
      meromorphicOrderAt (fun z : ℂ ↦ Complex.Gamma (z + u / 2)) 0 := by
    have h1 : (fun z : ℂ ↦ Complex.Gamma ((z + u) / 2)) =
        (fun w : ℂ ↦ Complex.Gamma (w + u / 2)) ∘ (fun z : ℂ ↦ z / 2) := by
      funext z; simp [add_div]
    rw [h1]
    have hd : deriv (fun z : ℂ ↦ z / 2) 0 ≠ 0 := by
      have : HasDerivAt (fun z : ℂ ↦ z / 2) (1 / 2 : ℂ) 0 := (hasDerivAt_id 0).div_const 2
      rw [this.deriv]
      norm_num
    simpa using meromorphicOrderAt_comp_of_deriv_ne_zero (f := fun w : ℂ ↦ Complex.Gamma (w + u / 2))
      (g := fun z : ℂ ↦ z / 2) (by fun_prop) hd
  rw [hmul, hcomp, meromorphicOrderAt_gamma_lt_zero_iff]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by linear_combination 2 * hm⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m, by ring⟩

private theorem meromorphicOrderAt_gammaC_div_two_lt_zero_iff (u : ℂ) :
    meromorphicOrderAt (fun z : ℂ ↦ Complex.Gammaℂ (z + u) / 2) 0 < 0 ↔
      ∃ m : ℕ, u = -(m : ℂ) := by
  have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have heq : (fun z : ℂ ↦ Complex.Gammaℂ (z + u) / 2) =
      (fun z : ℂ ↦ (2 * (Real.pi : ℂ)) ^ (-(z + u))) * (fun z : ℂ ↦ Complex.Gamma (z + u)) := by
    funext z
    change (2 * (2 * (Real.pi : ℂ)) ^ (-(z + u)) * Complex.Gamma (z + u)) / 2 =
      (2 * (Real.pi : ℂ)) ^ (-(z + u)) * Complex.Gamma (z + u)
    ring
  have he_an : AnalyticAt ℂ (fun z : ℂ ↦ (2 * (Real.pi : ℂ)) ^ (-(z + u))) 0 := by
    have hdiff : Differentiable ℂ (fun z : ℂ ↦ (2 * (Real.pi : ℂ)) ^ (-(z + u))) :=
      fun z ↦ ((differentiableAt_id.add (differentiableAt_const u)).neg.const_cpow (Or.inl h2pi))
    exact hdiff.analyticAt 0
  have he_ne : (2 * (Real.pi : ℂ)) ^ (-(0 + u)) ≠ 0 := by
    by_cases h0 : -(0 + u) = 0
    · rw [h0, Complex.cpow_zero]; exact one_ne_zero
    · exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero h0).mpr h2pi
  have he_ord : meromorphicOrderAt (fun z : ℂ ↦ (2 * (Real.pi : ℂ)) ^ (-(z + u))) 0 = 0 := by
    have hord : analyticOrderAt (fun z : ℂ ↦ (2 * (Real.pi : ℂ)) ^ (-(z + u))) 0 = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr he_ne)
    rw [he_an.meromorphicOrderAt_eq, hord, ENat.map_zero, CharP.cast_eq_zero, WithTop.coe_zero]
  have hG_mer : MeromorphicAt (fun z : ℂ ↦ Complex.Gamma (z + u)) 0 := by
    have h1 : AnalyticAt ℂ (fun z : ℂ ↦ (Complex.Gamma (z + u))⁻¹) 0 :=
      (Complex.differentiable_one_div_Gamma.analyticAt _).comp (by fun_prop)
    convert h1.meromorphicAt.inv using 1
    funext z; simp
  rw [heq, meromorphicOrderAt_mul he_an.meromorphicAt hG_mer, he_ord, zero_add,
    meromorphicOrderAt_gamma_lt_zero_iff]

/-- The selected centers and orders form a finite index set. Along the norm-twist line of a
component each archimedean place has its poles in an arithmetic progression running to the
left, and a cutoff keeps finitely many of them. -/
private theorem sLocalGammaFiltration_coeff_independent_finite (ω : PontryaginDual J₁(S))
    (N : depths) :
    Finite (ΓIndex(ω, sLocalGammaPoleCutoff (F := F) (S := S) ω N)) := by
  let U := sLocalGammaPoleCutoff (F := F) (S := S) ω N
  have hU_fin : U.Finite := by
    by_cases hUne : U.Nonempty
    · obtain ⟨c₀, hc₀⟩ := hUne
      have hc₀_comp : onComponent(c₀, ω) := hc₀.1
      have htw (c : Xₛ) (a z : ℂ) : shift(shift(c, a), z) = shift(c, z + a) := by
        ext1 g
        change c g * _ ^ a * _ ^ z = c g * _ ^ (z + a)
        rw [add_comm, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
          (NNReal.coe_ne_zero.mpr (m(S) g).ne_zero)), mul_assoc]
      have hcomp_shift (c : Xₛ) (hc : onComponent(c, ω)) : ∃ s : ℂ, c = shift(c₀, s) := by
        obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
        let c₀inv := c₀.comp (ContinuousMonoidHom.inv J(S))
        let P : QuasiCharacter ℝ≥0ˣ := (c * c₀inv).comp σ
        obtain ⟨s, hs⟩ := (existsUnique_complexPower P).exists
        refine ⟨s, ?_⟩
        ext1 g
        let u : J(S) := g * (σ (m(S) g))⁻¹
        have hu_mem : u ∈ J₁(S) := by
          change m(S) (g * (σ (m(S) g))⁻¹) = 1
          rw [map_mul, map_inv, hσ, mul_inv_cancel]
        have hu_eq : c u = c₀ u := DFunLike.congr_fun (hc.trans hc₀_comp.symm) ⟨u, hu_mem⟩
        have hdecomp : g = u * σ (m(S) g) := by simp [u]
        have hcg : c g = c u * c (σ (m(S) g)) := by
          conv_lhs => rw [hdecomp]
          exact map_mul c _ _
        have hc₀g : c₀ g = c₀ u * c₀ (σ (m(S) g)) := by
          conv_lhs => rw [hdecomp]
          exact map_mul c₀ _ _
        have hP : c (σ (m(S) g)) * (c₀ (σ (m(S) g)))⁻¹ =
            (((m(S) g : ℝ≥0) : ℝ) : ℂ) ^ s := by
          have h1 := hs (m(S) g)
          change c (σ (m(S) g)) * c₀ (σ (m(S) g))⁻¹ = _ at h1
          rwa [map_inv] at h1
        have hc₀σ_ne : c₀ (σ (m(S) g)) ≠ 0 :=
          ((Group.isUnit _).map c₀).ne_zero
        change c g = c₀ g * (((m(S) g : ℝ≥0) : ℝ) : ℂ) ^ s
        rw [hcg, hc₀g, hu_eq, ← hP]
        field_simp [hc₀σ_ne]
      have hres_shift (w : InfinitePlace F) (z : ℂ) (g : w.Completionˣ) :
          sLocalInfiniteRestriction w (shift(c₀, z)) g =
            sLocalInfiniteRestriction w c₀ g *
              ((((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ) g : ℝ≥0) : ℝ) : ℂ) ^ z := by
        have h1 := sLocalInfiniteRestriction_normTwist (F := F) (S := S) w z g
        rw [← h1]
        change c₀ _ * _ = c₀ _ * (((1 : Circle) : ℂ) * _)
        rw [Circle.coe_one, one_mul]
        rfl
      have hplace_poles (w : InfinitePlace F) :
          ∃ (a : ℂ) (step : ℝ), 0 < step ∧
            ∀ s : ℂ, w ∈ arch(shift(c₀, s)) ↔
              ∃ m : ℕ, s = -(step * (m : ℝ) : ℂ) - a := by
        by_cases hw : w.IsReal
        · let p := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w c₀)).exists.choose
          have hp := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w c₀)).exists.choose_spec
          have hE (u : ℂ) :
              infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (shift(c₀, u))) =
                Complex.Gammaℝ (u + (p.1 + (p.2.val : ℂ))) := by
            let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
            have hshape : ∀ x : ℝˣ, sLocalInfiniteRestriction w (shift(c₀, u))
                (Units.map e.toMonoidHom x) =
                  (‖(x : ℝ)‖ : ℂ) ^ (p.1 + u) * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ p.2.val := by
              intro x
              have hn : ‖(e (x : ℝ) : w.Completion)‖ = ‖(x : ℝ)‖ :=
                (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
                  (map_zero e) (x : ℝ)
              have hm : (((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ)
                  (Units.map e.toMonoidHom x) : ℝ≥0) : ℝ) = ‖(x : ℝ)‖ := by
                simp [InfinitePlace.mult, hw, hn]
              rw [hres_shift, hp x, hm]
              have hne : (‖(x : ℝ)‖ : ℂ) ≠ 0 :=
                Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero)
              rw [Complex.cpow_add _ _ hne]
              ring
            have hq := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w (shift(c₀, u)))).unique
              (realLocalEulerParameters w hw (sLocalInfiniteRestriction w (shift(c₀, u)))).exists.choose_spec
              (y₂ := (p.1 + u, p.2)) hshape
            simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hq]
            congr 1; ring
          refine ⟨p.1 + (p.2.val : ℂ), 2, two_pos, fun s ↦ ?_⟩
          simp only [sLocalArchPolePlaces, Finset.mem_filter, Finset.mem_univ, true_and]
          have hfun : (fun z : ℂ ↦ infiniteLocalEulerFactor w
              (sLocalInfiniteRestriction w (shift(shift(c₀, s), z)))) =
              fun z : ℂ ↦ Complex.Gammaℝ (z + (s + (p.1 + (p.2.val : ℂ)))) := by
            funext z
            rw [htw, hE]
            congr 1; ring
          rw [hfun, meromorphicOrderAt_gammaR_lt_zero_iff]
          constructor <;> rintro ⟨m, hm⟩ <;> refine ⟨m, ?_⟩
          · push_cast at hm ⊢; linear_combination hm
          · push_cast at hm ⊢; linear_combination hm
        · have hwc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
          let p := (complexLocalEulerParameters w hwc (sLocalInfiniteRestriction w c₀)).exists.choose
          have hp := (complexLocalEulerParameters w hwc (sLocalInfiniteRestriction w c₀)).exists.choose_spec
          have hE (u : ℂ) :
              infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (shift(c₀, u))) =
                Complex.Gammaℂ (u + (p.1 + (p.2.natAbs : ℂ) / 2)) / 2 := by
            let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc).symm
            have hshape : ∀ x : ℂˣ, sLocalInfiniteRestriction w (shift(c₀, u))
                (Units.map e.toMonoidHom x) =
                  ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (p.1 + u) * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ p.2 := by
              intro x
              have hn : ‖(e (x : ℂ) : w.Completion)‖ = ‖(x : ℂ)‖ :=
                (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hwc).symm.isometry.norm_map_of_map_zero
                  (map_zero e) (x : ℂ)
              have hm : (((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ)
                  (Units.map e.toMonoidHom x) : ℝ≥0) : ℝ) = ‖(x : ℂ)‖ ^ 2 := by
                simp [InfinitePlace.mult, hw, hn]
              rw [hres_shift, hp x, hm]
              have hne : ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
                Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr x.ne_zero))
              rw [Complex.cpow_add _ _ hne]
              ring
            have hq := (complexLocalEulerParameters w hwc (sLocalInfiniteRestriction w (shift(c₀, u)))).unique
              (complexLocalEulerParameters w hwc (sLocalInfiniteRestriction w (shift(c₀, u)))).exists.choose_spec
              (y₂ := (p.1 + u, p.2)) hshape
            simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hq]
            congr 2; ring
          refine ⟨p.1 + (p.2.natAbs : ℂ) / 2, 1, one_pos, fun s ↦ ?_⟩
          simp only [sLocalArchPolePlaces, Finset.mem_filter, Finset.mem_univ, true_and]
          have hfun : (fun z : ℂ ↦ infiniteLocalEulerFactor w
              (sLocalInfiniteRestriction w (shift(shift(c₀, s), z)))) =
              fun z : ℂ ↦ Complex.Gammaℂ (z + (s + (p.1 + (p.2.natAbs : ℂ) / 2))) / 2 := by
            funext z
            rw [htw, hE]
            congr 2; ring
          rw [hfun, meromorphicOrderAt_gammaC_div_two_lt_zero_iff]
          constructor <;> rintro ⟨m, hm⟩ <;> refine ⟨m, ?_⟩
          · push_cast at hm ⊢; linear_combination hm
          · push_cast at hm ⊢; linear_combination hm
      have hsub : U ⊆ ⋃ w : InfinitePlace F,
          let h := hplace_poles w
          (fun m : Fin (N w + 1) ↦ shift(c₀, -(h.choose_spec.choose * (m.val : ℝ) : ℂ) - h.choose)) ''
            Set.univ := by
        intro c hc
        obtain ⟨s, rfl⟩ := hcomp_shift c hc.1
        obtain ⟨w, hw, hcard⟩ := hc.2
        refine Set.mem_iUnion.mpr ⟨w, ?_⟩
        have hstep' : 0 < (hplace_poles w).choose_spec.choose :=
          (hplace_poles w).choose_spec.choose_spec.1
        have hiff' := (hplace_poles w).choose_spec.choose_spec.2
        obtain ⟨m, rfl⟩ := (hiff' s).mp hw
        have hm_le : m ≤ N w := by
          let f : Fin m → ℝ := fun k ↦ (hplace_poles w).choose_spec.choose * ((k.val + 1 : ℕ) : ℝ)
          have hfinj : Function.Injective f := by
            intro k₁ k₂ hk
            have h1 : ((k₁.val + 1 : ℕ) : ℝ) = ((k₂.val + 1 : ℕ) : ℝ) :=
              mul_left_cancel₀ hstep'.ne' hk
            have h2 : k₁.val + 1 = k₂.val + 1 := by exact_mod_cast h1
            exact Fin.ext (by omega)
          have hfrange : Set.range f ⊆
              {t : ℝ | 0 < t ∧ w ∈ arch(shift(shift(c₀,
                -((hplace_poles w).choose_spec.choose * (m : ℝ) : ℂ) - (hplace_poles w).choose),
                (t : ℂ)))} := by
            rintro _ ⟨k, rfl⟩
            refine ⟨by positivity, ?_⟩
            rw [htw, hiff']
            refine ⟨m - (k.val + 1), ?_⟩
            have hle : k.val + 1 ≤ m := k.isLt
            dsimp only [f]
            push_cast [Nat.cast_sub hle]
            ring
          have hle_enc : (m : ℕ∞) ≤
              ({t : ℝ | 0 < t ∧ w ∈ arch(shift(shift(c₀,
                -((hplace_poles w).choose_spec.choose * (m : ℝ) : ℂ) - (hplace_poles w).choose),
                (t : ℂ)))} : Set ℝ).encard := by
            calc (m : ℕ∞) = (Set.range f).encard := by
                  rw [← Set.image_univ, hfinj.injOn.encard_image, Set.encard_univ,
                    ENat.card_eq_coe_fintype_card, Fintype.card_fin]
              _ ≤ _ := Set.encard_le_encard hfrange
          exact_mod_cast hle_enc.trans hcard
        exact ⟨⟨m, Nat.lt_succ_of_le hm_le⟩, Set.mem_univ _, rfl⟩
      exact (Set.finite_iUnion fun w ↦ (Set.finite_univ).image _).subset hsub
    · rw [Set.not_nonempty_iff_eq_empty.mp hUne]
      exact Set.finite_empty
  have hι_fin : Finite (ΓIndex(ω, U)) := by
    have : Finite U := hU_fin.to_subtype
    let f : ΓIndex(ω, U) → U × Fin (Fintype.card (InfinitePlace F) + 1) := fun j ↦
      ⟨⟨j.val.1, j.property.2.1⟩,
        ⟨j.val.2, Nat.lt_succ_of_le (j.property.2.2.2.trans (Finset.card_le_univ _))⟩⟩
    have hf : Function.Injective f := by
      intro j₁ j₂ h
      have h1 : j₁.val.1 = j₂.val.1 := congrArg (fun p ↦ p.1.val) h
      have h2 : j₁.val.2 = j₂.val.2 := congrArg (fun p ↦ p.2.val) h
      exact Subtype.ext (Prod.ext h1 h2)
    exact Finite.of_injective f hf
  exact hι_fin

/-- Paper: Theorem 7.3.4.1(2), pp. 364–365.
On each component some principal value attains the full archimedean pole order at every
center: its Laurent coefficient of the top admissible order does not vanish there.
This follows from `exists_sLocalIdelicZFunction_principalValue_attaining_poles` for one unitary
character on the component. Every center of the component is a norm twist of it, the pole
multiplicity at a twist is the number of archimedean pole places (the computation in
`gammaFiltration_principalValue_bound`), and `mem_sLocalThetaPoleBound_iff_leading` gives the
leading coefficient. -/
private theorem sLocalGammaFiltration_coeff_independent_attaining (ω : PontryaginDual J₁(S)) :
    ∃ g : B(S), ∀ c : Xₛ, onComponent(c, ω) → 0 < (arch(c)).card →
      sLocalPrincipalPartCoeff c (arch(c)).card
        (sAdelePrincipalValue F (Finset.Subset.refl S) g) ≠ 0 := by
  classical
  by_cases hne : ∃ c₀ : Xₛ, onComponent(c₀, ω)
  swap
  · exact ⟨0, fun c hc ↦ (hne ⟨c, hc⟩).elim⟩
  obtain ⟨c₀, hc₀⟩ := hne
  obtain ⟨χ, a, ha⟩ := exists_sLocalNormTwist (F := F) (S := S) c₀
  let d : Xₛ := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
  obtain ⟨f, hf⟩ := exists_sLocalIdelicZFunction_principalValue_attaining_poles (F := F) (S := S) χ
  refine ⟨f, fun c hc hpos ↦ ?_⟩
  have htw (b : Xₛ) (a z : ℂ) : shift(shift(b, a), z) = shift(b, z + a) := by
    ext1 g
    change b g * _ ^ a * _ ^ z = b g * _ ^ (z + a)
    rw [add_comm, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
      (NNReal.coe_ne_zero.mpr (m(S) g).ne_zero)), mul_assoc]
  -- Every quasi-character of the component is a norm twist of `c₀`.
  obtain ⟨s, hs⟩ : ∃ s : ℂ, c = shift(c₀, s) := by
    obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section (F := F) (S := S)
    let c₀inv := c₀.comp (ContinuousMonoidHom.inv J(S))
    let P : QuasiCharacter ℝ≥0ˣ := (c * c₀inv).comp σ
    obtain ⟨s, hs⟩ := (existsUnique_complexPower P).exists
    refine ⟨s, ?_⟩
    ext1 g
    let u : J(S) := g * (σ (m(S) g))⁻¹
    have hu_mem : u ∈ J₁(S) := by
      change m(S) (g * (σ (m(S) g))⁻¹) = 1
      rw [map_mul, map_inv, hσ, mul_inv_cancel]
    have hu_eq : c u = c₀ u := DFunLike.congr_fun (hc.trans hc₀.symm) ⟨u, hu_mem⟩
    have hdecomp : g = u * σ (m(S) g) := by simp [u]
    have hcg : c g = c u * c (σ (m(S) g)) := by
      conv_lhs => rw [hdecomp]
      exact map_mul c _ _
    have hc₀g : c₀ g = c₀ u * c₀ (σ (m(S) g)) := by
      conv_lhs => rw [hdecomp]
      exact map_mul c₀ _ _
    have hP : c (σ (m(S) g)) * (c₀ (σ (m(S) g)))⁻¹ = (((m(S) g : ℝ≥0) : ℝ) : ℂ) ^ s := by
      have h1 := hs (m(S) g)
      change c (σ (m(S) g)) * c₀ (σ (m(S) g))⁻¹ = _ at h1
      rwa [map_inv] at h1
    have hc₀σ_ne : c₀ (σ (m(S) g)) ≠ 0 := ((Group.isUnit _).map c₀).ne_zero
    change c g = c₀ g * (((m(S) g : ℝ≥0) : ℝ) : ℂ) ^ s
    rw [hcg, hc₀g, hu_eq, ← hP]
    field_simp [hc₀σ_ne]
  have hct : c = shift(d, s + a) := by rw [hs, ← ha, htw]
  subst hct
  have translate (H : Xₛ → ℂ) :
      meromorphicOrderAt (fun z : ℂ ↦ H (shift(shift(d, s + a), z))) 0 =
        meromorphicOrderAt (fun z : ℂ ↦ H (shift(d, z))) (s + a) := by
    have e : (fun z : ℂ ↦ H (shift(shift(d, s + a), z))) =
        (fun z : ℂ ↦ H (shift(d, z))) ∘ (· + (s + a)) := by
      funext z
      rw [htw]
      rfl
    rw [e, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt, zero_add]
  have places : (arch(shift(d, s + a))).card = sLocalArchimedeanPoleMultiplicity χ (s + a) := by
    unfold sLocalArchPolePlaces sLocalArchimedeanPoleMultiplicity
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro w _
    rw [translate (fun b ↦ infiniteLocalEulerFactor w (sLocalInfiniteRestriction w b))]
  let p := sAdelePrincipalValue F (Finset.Subset.refl S) f
  have hord : meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction p (shift(shift(d, s + a), z))) 0 =
      ((-((arch(shift(d, s + a))).card : ℤ) : ℤ) : WithTop ℤ) := by
    rw [translate (sLocalIdelicZFunction p), places]
    exact hf (s + a)
  have hZ := sLocalZ_centered p (shift(d, s + a))
  rw [sLocalPrincipalPartCoeff_apply]
  refine mem_sLocalThetaPoleBound_iff_leading hZ.1 hpos ?_
  change (-(meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction p
    (shift(shift(d, s + a), z))) 0).untop₀).toNat = _
  rw [hord]
  simp

/-- Paper: Theorem 7.3.4.1(2), pp. 364–365, and Theorem 7.2.1.1(2), p. 334.
The Laurent coefficients of the principal value of a translated test are an upper triangular
combination of those of the principal value of the test, with powers of the logarithm of the
norm of the translating idele.
This follows as `sLocalPrincipalPartCoeff_translate` does. By
`sLocalIdelicZFunction_principalValue`, applied to the test and to its translate, and
`sLocalPrincipalPartCoeff_translate_zeta`, the zeta function of the principal value of the
translate is the character value times that of the principal value, off a discrete set of each
norm-twist line. Residues only see such germs (`sLocalPrincipalPartCoeff_translate_congr`), and
`sLocalPrincipalPartCoeff_translate_laurent` applies with the pole bound of
`gammaFiltration_principalValue_bound`. -/
private theorem sLocalGammaFiltration_coeff_independent_translate (g : B(S))
    (u : (SAdeleRing F S)ˣ) (c : Xₛ) (k : ℕ) (hk : 0 < k) (hkc : k ≤ (arch(c)).card) :
    sLocalPrincipalPartCoeff c k (sAdelePrincipalValue F (Finset.Subset.refl S)
        (schwartzBruhatUnitTranslate u g)) =
      c (QuotientGroup.mk u : J(S)) * ∑ i ∈ Finset.range ((arch(c)).card - k + 1),
        sLocalPrincipalPartCoeff c (k + i) (sAdelePrincipalValue F (Finset.Subset.refl S) g) *
          ((Real.log (((m(S) (QuotientGroup.mk u : J(S)) : ℝ≥0) : ℝ)) : ℝ) : ℂ) ^ i /
            (i.factorial : ℂ) := by
  classical
  let P := sAdelePrincipalValue F (Finset.Subset.refl S)
  let gu : J(S) := QuotientGroup.mk u
  let L : ℂ := ((Real.log (((m(S) gu : ℝ≥0) : ℝ)) : ℝ) : ℂ)
  have hZ := sLocalZ_centered (P g) c
  have hbound := gammaFiltration_principalValue_bound g c
  have hord : ((-((arch(c)).card : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction (P g) (shift(c, z))) 0 := by
    change (-(meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction (P g) (shift(c, z))) 0).untop₀).toNat
      ≤ _ at hbound
    generalize meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction (P g) (shift(c, z))) 0 = o
      at hbound ⊢
    induction o using WithTop.recTopCoe with
    | top => exact le_top
    | coe n =>
      simp only [WithTop.untop₀_coe] at hbound
      exact WithTop.coe_le_coe.mpr (by omega)
  have hM : (((m(S) gu : ℝ≥0) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (Units.ne_zero _))
  have hval (b : Xₛ) (z : ℂ) : (shift(b, z)) gu = b gu * Complex.exp (L * z) := by
    change b gu * (((m(S) gu : ℝ≥0) : ℝ) : ℂ) ^ z = _
    rw [Complex.cpow_def_of_ne_zero hM, ← Complex.ofReal_log (NNReal.coe_nonneg _)]
  -- The zeta functions of the two principal values differ by the character value at `u`.
  have hgerm : (fun z ↦ sLocalIdelicZFunction (P (schwartzBruhatUnitTranslate u g)) (shift(c, z)))
      =ᶠ[𝓝[≠] (0 : ℂ)]
      fun z ↦ (shift(c, z)) gu * sLocalIdelicZFunction (P g) (shift(c, z)) := by
    obtain ⟨χ, a, hc⟩ := exists_sLocalNormTwist (F := F) (S := S) c
    let d : Xₛ := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
    have e (H : Xₛ → ℂ) (z : ℂ) : H (shift(c, z)) = H (shift(d, z + a)) := by
      rw [← hc, normTwist_normTwist]
    have hPV (h : B(S)) := sLocalIdelicZFunction_principalValue (F := F) (S := S) S
      (Finset.Subset.refl S) h χ
    have hcod : (fun s ↦ sLocalIdelicZFunction (P (schwartzBruhatUnitTranslate u g)) (shift(d, s)))
        =ᶠ[codiscrete ℂ] fun s ↦ (shift(d, s)) gu * sLocalIdelicZFunction (P g) (shift(d, s)) := by
      filter_upwards [hPV (schwartzBruhatUnitTranslate u g), hPV g] with s h1 h2
      dsimp only at h1 h2
      change sLocalIdelicZFunction (P (schwartzBruhatUnitTranslate u g)) (shift(d, s)) = _
      erw [h1, h2, sLocalPrincipalPartCoeff_translate_zeta, mul_div_assoc]
    have hT : Tendsto (fun z : ℂ ↦ z + a) (𝓝[≠] 0) (𝓝[≠] a) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_nhdsWithin_of_tendsto_nhds ?_, ?_⟩
      · simpa using (Continuous.tendsto (f := fun z : ℂ ↦ z + a) (by fun_prop) 0)
      · filter_upwards [self_mem_nhdsWithin] with z hz
        simpa using hz
    filter_upwards [(eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.mp hcod a).comp_tendsto hT]
      with z hz
    simp only [Function.comp_apply] at hz
    rw [e (sLocalIdelicZFunction (P (schwartzBruhatUnitTranslate u g))) z,
      e (sLocalIdelicZFunction (P g)) z, e (fun b ↦ b gu) z, hz]
  rw [sLocalPrincipalPartCoeff_apply]
  change complexResidue (fun z ↦ sLocalIdelicZFunction (P (schwartzBruhatUnitTranslate u g))
    (shift(c, z)) / z ^ (-(k : ℤ) + 1)) 0 = _
  rw [sLocalPrincipalPartCoeff_translate_congr (h := fun z ↦ c gu * (Complex.exp (L * z) *
    sLocalIdelicZFunction (P g) (shift(c, z)) / z ^ (-(k : ℤ) + 1))) ?_]
  · rw [sLocalPrincipalPartCoeff_translate_laurent hZ.1 hkc hord]
    rfl
  · filter_upwards [hgerm] with z hz
    rw [hz, hval]
    ring

/-- Paper: Theorem 7.3.4.1(2), pp. 364–365.
There is a family of S-ideles indexed by the logarithm of their norm on which every
quasi-character is an exponential, and the exponents separate the quasi-characters of one
component.
This follows from a continuous section of the norm (`sIdeleQuotientNorm_exists_section`),
lifted to S-ideles at the points `exp t`: a quasi-character composed with the section is a
complex power (`existsUnique_complexPower`), and two quasi-characters of one component which
agree on the section agree everywhere, since every class is a norm-one class times a value of
the section. -/
private theorem sLocalGammaFiltration_coeff_independent_section :
    ∃ (u : ℝ → (SAdeleRing F S)ˣ) (s : Xₛ → ℂ),
      (∀ t : ℝ, Real.log (((m(S) (QuotientGroup.mk (u t) : J(S)) : ℝ≥0) : ℝ)) = t) ∧
      (∀ (c : Xₛ) (t : ℝ), c (QuotientGroup.mk (u t) : J(S)) = Complex.exp (s c * t)) ∧
      ∀ (ω : PontryaginDual J₁(S)) (c c' : Xₛ), onComponent(c, ω) → onComponent(c', ω) →
        s c = s c' → c = c' := by
  classical
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section (F := F) (S := S)
  let E (t : ℝ) : ℝ≥0ˣ := Units.mk0 (Real.exp t).toNNReal (Real.toNNReal_pos.mpr (Real.exp_pos t)).ne'
  have hE (t : ℝ) : (((E t : ℝ≥0ˣ) : ℝ≥0) : ℝ) = Real.exp t := Real.coe_toNNReal _ (Real.exp_pos t).le
  choose u hu using fun t ↦ QuotientGroup.mk_surjective (σ (E t))
  let s (c : Xₛ) : ℂ := (existsUnique_complexPower (c.comp σ)).exists.choose
  have hs (c : Xₛ) (x : ℝ≥0ˣ) : c (σ x) = (((x : ℝ≥0) : ℝ) : ℂ) ^ s c :=
    (existsUnique_complexPower (c.comp σ)).exists.choose_spec x
  refine ⟨u, s, fun t ↦ ?_, fun c t ↦ ?_, fun ω c c' hc hc' hcc ↦ ?_⟩
  · rw [hu, hσ (E t), hE, Real.log_exp]
  · rw [hu, hs, hE, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'),
      ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp, mul_comm]
  · have hk (k : J(S)) (hk : k ∈ J₁(S)) : c k = c' k :=
      DFunLike.congr_fun (hc.trans hc'.symm) ⟨k, hk⟩
    have hsec (x : ℝ≥0ˣ) : c (σ x) = c' (σ x) := by rw [hs, hs, hcc]
    ext g
    have hg : g * (σ (m(S) g))⁻¹ ∈ J₁(S) := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, mul_inv_cancel]
    have hsplit : g = g * (σ (m(S) g))⁻¹ * σ (m(S) g) := by group
    calc c g = c (g * (σ (m(S) g))⁻¹) * c (σ (m(S) g)) := by rw [← map_mul, ← hsplit]
      _ = c' (g * (σ (m(S) g))⁻¹) * c' (σ (m(S) g)) := by rw [hk _ hg, hsec]
      _ = c' g := by rw [← map_mul, ← hsplit]

-- TODO(paper-gap): The test list (7.3.4.9) does not separate the two coefficients
-- of a double real pole at cutoff (0,0). See ERRATA I169. Finite interpolation can
-- use translations of a test attaining the full pole order.

/-- Paper: Theorem 7.3.4.1(2), pp. 364–365.
The Laurent coefficients at the selected centers form a finite linearly independent family. -/
theorem sLocalGammaFiltration_coeff_independent (ω : PontryaginDual J₁(S)) (N : depths) :
    let U := sLocalGammaPoleCutoff (F := F) (S := S) ω N
    Finite (ΓIndex(ω, U)) ∧ LinearIndependent ℂ (fun j : ΓIndex(ω, U) ↦ ΓCoeff(ω, j)) := by
  intro U
  have hfin : Finite (ΓIndex(ω, U)) := sLocalGammaFiltration_coeff_independent_finite ω N
  refine ⟨hfin, ?_⟩
  classical
  let := Fintype.ofFinite (ΓIndex(ω, U))
  obtain ⟨g₀, hg₀⟩ := sLocalGammaFiltration_coeff_independent_attaining (F := F) (S := S) ω
  obtain ⟨u, s, hnorm, hchar, hsinj⟩ :=
    sLocalGammaFiltration_coeff_independent_section (F := F) (S := S)
  rw [Fintype.linearIndependent_iff]
  intro a ha j₀
  let x (t : ℝ) : fullPV(ω) :=
    ⟨PV((Finset.Subset.refl S), ω) (q(S, ω) (schwartzBruhatUnitTranslate (u t) g₀)),
      LinearMap.mem_range_self _ _⟩
  refine expPolynomial_translate_coeff_eq_zero (Finset.univ : Finset (ΓIndex(ω, U)))
    (fun j ↦ j.val.1) (fun j ↦ j.val.2) s (fun c ↦ (arch(c)).card)
    (fun c m ↦ sLocalPrincipalPartCoeff c m (sAdelePrincipalValue F (Finset.Subset.refl S) g₀))
    a ?_ ?_ ?_ ?_ ?_ ?_ j₀ (Finset.mem_univ _)
  · intro j _ j' _ h1 h2
    exact Subtype.ext (Prod.ext h1 h2)
  · intro j _ j' _ h
    exact hsinj ω _ _ j.property.1 j'.property.1 h
  · intro j _
    exact j.property.2.2.2
  · intro j _
    exact hg₀ j.val.1 j.property.1 (lt_of_lt_of_le j.property.2.2.1 j.property.2.2.2)
  · intro c m hm
    by_contra hne
    have hle := (sLocalPrincipalPartCoeff_ne_zero_imp_pole c m (Nat.zero_lt_of_lt hm) _ hne).2
    exact absurd (hle.trans (gammaFiltration_principalValue_bound g₀ c)) (not_le.mpr hm)
  · intro t
    have hat := congrArg (fun φ : StrongDual ℂ (fullPV(ω)) ↦ φ (x t)) ha
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.zero_apply] at hat
    refine Eq.trans (Finset.sum_congr rfl fun j _ ↦ congrArg (a j * ·) ?_) hat
    have h2 := sLocalGammaFiltration_coeff_independent_translate (F := F) (S := S) g₀ (u t)
      j.val.1 j.val.2 j.property.2.2.1 j.property.2.2.2
    rw [hchar, hnorm] at h2
    exact h2.symm

private theorem dual_range_mkQL_eq_span_of_finite {E ι : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [Finite ι] (φ : ι → StrongDual ℂ E) :
    let stage : Submodule ℂ E := ⨅ j : ι, (φ j).ker
    Set.range (fun ℓ : StrongDual ℂ (E ⧸ stage) ↦ ℓ.comp stage.mkQL) =
      (Submodule.span ℂ (Set.range φ) : Set (StrongDual ℂ E)) := by
  intro stage
  classical
  let : Fintype ι := Fintype.ofFinite ι
  ext ψ
  constructor
  · rintro ⟨ℓ, rfl⟩
    let T : E →ₗ[ℂ] (ι → ℂ) := LinearMap.pi (fun j ↦ (φ j).toLinearMap)
    have hker : T.ker ≤ (ℓ.comp stage.mkQL).toLinearMap.ker := by
      intro x hx
      have hx' : x ∈ stage := by
        rw [Submodule.mem_iInf]
        intro j
        exact congrFun hx j
      change ℓ (stage.mkQ x) = 0
      rw [stage.mkQ_apply, (Submodule.Quotient.mk_eq_zero stage).mpr hx', map_zero]
    let f₀ : T.range →ₗ[ℂ] ℂ :=
      (Submodule.liftQ T.ker (ℓ.comp stage.mkQL).toLinearMap hker).comp
        T.quotKerEquivRange.symm.toLinearMap
    obtain ⟨g, hg⟩ := LinearMap.exists_extend f₀
    have hsum : ℓ.comp stage.mkQL = ∑ j : ι, g (Pi.single j 1) • φ j := by
      ext x
      have hTx : T x = ∑ j : ι, (φ j x) • Pi.single j (1 : ℂ) := by
        ext k
        simp [T, Finset.sum_apply, Pi.single_apply]
      have h1 : (ℓ.comp stage.mkQL) x = g (T x) := by
        have := congrArg (fun h : T.range →ₗ[ℂ] ℂ ↦ h ⟨T x, LinearMap.mem_range_self T x⟩) hg
        simpa [f₀, LinearEquiv.symm_apply_apply] using this.symm
      rw [h1, hTx, map_sum]
      simp [smul_eq_mul, mul_comm]
    change ℓ.comp stage.mkQL ∈ Submodule.span ℂ (Set.range φ)
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · intro hψ
    have hker : stage ≤ ψ.toLinearMap.ker := by
      refine Submodule.span_induction
        (p := fun (ψ' : StrongDual ℂ E) _ ↦ stage ≤ ψ'.toLinearMap.ker)
        ?_ ?_ ?_ ?_ hψ
      · rintro _ ⟨j, rfl⟩ x hx
        rw [Submodule.mem_iInf] at hx
        exact hx j
      · intro x _; simp
      · intro a b _ _ ha hb x hx
        have ha' : a x = 0 := ha hx
        have hb' : b x = 0 := hb hx
        change a x + b x = 0
        rw [ha', hb', add_zero]
      · intro c a _ ha x hx
        have ha' : a x = 0 := ha hx
        change c * a x = 0
        rw [ha', mul_zero]
    let ℓ_lin : (E ⧸ stage) →ₗ[ℂ] ℂ := stage.liftQ ψ.toLinearMap hker
    have hcont : Continuous ℓ_lin := by
      have hq : Topology.IsQuotientMap (stage.mkQ : E → E ⧸ stage) :=
        QuotientAddGroup.isQuotientMap_mk _
      rw [hq.continuous_iff]
      exact ψ.continuous
    refine ⟨⟨ℓ_lin, hcont⟩, ?_⟩
    ext x
    rfl

/-- Paper: Theorem 7.3.4.1(2), p. 365.
The transposes of the linear functionals on the filtered quotient are precisely the
span of the selected Laurent coefficients on the principal-value space.
Deviation: The displayed positive order k in (7.3.4.4) selects Laurent exponent −k. -/
theorem sLocalGammaFiltration_dual_span (ω : PontryaginDual J₁(S)) (N : depths) :
    let stage := sLocalGammaFiltration (F := F) (S := S) ω N
    Set.range (fun ℓ : StrongDual ℂ ((fullPV(ω)) ⧸ stage) ↦ ℓ.comp stage.mkQL) =
      (Submodule.span ℂ (Set.range (fun j : ΓIndex(ω, sLocalGammaPoleCutoff (F := F) (S := S) ω N) ↦
        ΓCoeff(ω, j))) : Set (StrongDual ℂ (fullPV(ω)))) := by
  let U := sLocalGammaPoleCutoff (F := F) (S := S) ω N
  have hι_fin : Finite (ΓIndex(ω, U)) := sLocalGammaFiltration_coeff_independent_finite ω N
  exact @dual_range_mkQL_eq_span_of_finite _ _ _ _ _ _ _ hι_fin
    (fun j : ΓIndex(ω, U) ↦ ΓCoeff(ω, j))

/-- Along the norm-twist line through a quasi-character, an archimedean place has its
poles at an arithmetic progression running to the left. -/
private theorem sLocalGammaFiltration_iInf_placePoles (c₀ : Xₛ) (w : InfinitePlace F) :
    ∃ (a : ℂ) (step : ℝ), 0 < step ∧
      ∀ s : ℂ, w ∈ arch(shift(c₀, s)) ↔ ∃ m : ℕ, s = -(step * (m : ℝ) : ℂ) - a := by
  have htw (c : Xₛ) (a z : ℂ) : shift(shift(c, a), z) = shift(c, z + a) := by
    ext1 g
    change c g * _ ^ a * _ ^ z = c g * _ ^ (z + a)
    rw [add_comm, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
      (NNReal.coe_ne_zero.mpr (m(S) g).ne_zero)), mul_assoc]
  have hres_shift (z : ℂ) (g : w.Completionˣ) :
      sLocalInfiniteRestriction w (shift(c₀, z)) g =
        sLocalInfiniteRestriction w c₀ g *
          ((((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ) g : ℝ≥0) : ℝ) : ℂ) ^ z := by
    have h1 := sLocalInfiniteRestriction_normTwist (F := F) (S := S) w z g
    rw [← h1]
    change c₀ _ * _ = c₀ _ * (((1 : Circle) : ℂ) * _)
    rw [Circle.coe_one, one_mul]
    rfl
  by_cases hw : w.IsReal
  · let p := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w c₀)).exists.choose
    have hp := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w c₀)).exists.choose_spec
    have hE (u : ℂ) :
        infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (shift(c₀, u))) =
          Complex.Gammaℝ (u + (p.1 + (p.2.val : ℂ))) := by
      let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
      have hshape : ∀ x : ℝˣ, sLocalInfiniteRestriction w (shift(c₀, u))
          (Units.map e.toMonoidHom x) =
            (‖(x : ℝ)‖ : ℂ) ^ (p.1 + u) * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ p.2.val := by
        intro x
        have hn : ‖(e (x : ℝ) : w.Completion)‖ = ‖(x : ℝ)‖ :=
          (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
            (map_zero e) (x : ℝ)
        have hm : (((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ)
            (Units.map e.toMonoidHom x) : ℝ≥0) : ℝ) = ‖(x : ℝ)‖ := by
          simp [InfinitePlace.mult, hw, hn]
        rw [hres_shift, hp x, hm]
        have hne : (‖(x : ℝ)‖ : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero)
        rw [Complex.cpow_add _ _ hne]
        ring
      have hq := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w (shift(c₀, u)))).unique
        (realLocalEulerParameters w hw (sLocalInfiniteRestriction w (shift(c₀, u)))).exists.choose_spec
        (y₂ := (p.1 + u, p.2)) hshape
      simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hq]
      congr 1; ring
    refine ⟨p.1 + (p.2.val : ℂ), 2, two_pos, fun s ↦ ?_⟩
    simp only [sLocalArchPolePlaces, Finset.mem_filter, Finset.mem_univ, true_and]
    have hfun : (fun z : ℂ ↦ infiniteLocalEulerFactor w
        (sLocalInfiniteRestriction w (shift(shift(c₀, s), z)))) =
        fun z : ℂ ↦ Complex.Gammaℝ (z + (s + (p.1 + (p.2.val : ℂ)))) := by
      funext z
      rw [htw, hE]
      congr 1; ring
    rw [hfun, meromorphicOrderAt_gammaR_lt_zero_iff]
    constructor <;> rintro ⟨m, hm⟩ <;> refine ⟨m, ?_⟩
    · push_cast at hm ⊢; linear_combination hm
    · push_cast at hm ⊢; linear_combination hm
  · have hwc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    let p := (complexLocalEulerParameters w hwc (sLocalInfiniteRestriction w c₀)).exists.choose
    have hp := (complexLocalEulerParameters w hwc (sLocalInfiniteRestriction w c₀)).exists.choose_spec
    have hE (u : ℂ) :
        infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (shift(c₀, u))) =
          Complex.Gammaℂ (u + (p.1 + (p.2.natAbs : ℂ) / 2)) / 2 := by
      let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc).symm
      have hshape : ∀ x : ℂˣ, sLocalInfiniteRestriction w (shift(c₀, u))
          (Units.map e.toMonoidHom x) =
            ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (p.1 + u) * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ p.2 := by
        intro x
        have hn : ‖(e (x : ℂ) : w.Completion)‖ = ‖(x : ℂ)‖ :=
          (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hwc).symm.isometry.norm_map_of_map_zero
            (map_zero e) (x : ℂ)
        have hm : (((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ)
            (Units.map e.toMonoidHom x) : ℝ≥0) : ℝ) = ‖(x : ℂ)‖ ^ 2 := by
          simp [InfinitePlace.mult, hw, hn]
        rw [hres_shift, hp x, hm]
        have hne : ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr x.ne_zero))
        rw [Complex.cpow_add _ _ hne]
        ring
      have hq := (complexLocalEulerParameters w hwc (sLocalInfiniteRestriction w (shift(c₀, u)))).unique
        (complexLocalEulerParameters w hwc (sLocalInfiniteRestriction w (shift(c₀, u)))).exists.choose_spec
        (y₂ := (p.1 + u, p.2)) hshape
      simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hq]
      congr 2; ring
    refine ⟨p.1 + (p.2.natAbs : ℂ) / 2, 1, one_pos, fun s ↦ ?_⟩
    simp only [sLocalArchPolePlaces, Finset.mem_filter, Finset.mem_univ, true_and]
    have hfun : (fun z : ℂ ↦ infiniteLocalEulerFactor w
        (sLocalInfiniteRestriction w (shift(shift(c₀, s), z)))) =
        fun z : ℂ ↦ Complex.Gammaℂ (z + (s + (p.1 + (p.2.natAbs : ℂ) / 2))) / 2 := by
      funext z
      rw [htw, hE]
      congr 2; ring
    rw [hfun, meromorphicOrderAt_gammaC_div_two_lt_zero_iff]
    constructor <;> rintro ⟨m, hm⟩ <;> refine ⟨m, ?_⟩
    · push_cast at hm ⊢; linear_combination hm
    · push_cast at hm ⊢; linear_combination hm

/-- An archimedean place has only finitely many poles to the right of a quasi-character
along its norm-twist line. -/
private theorem sLocalGammaFiltration_iInf_finite (c : Xₛ) (w : InfinitePlace F) :
    ({t : ℝ | 0 < t ∧ w ∈ arch(shift(c, (t : ℂ)))} : Set ℝ).Finite := by
  obtain ⟨a, step, hstep, hiff⟩ := sLocalGammaFiltration_iInf_placePoles c w
  obtain ⟨M, hM⟩ := exists_nat_gt (-a.re / step)
  refine ((Set.finite_lt_nat M).image fun m : ℕ ↦ -(step * (m : ℝ)) - a.re).subset ?_
  rintro t ⟨ht, hw⟩
  obtain ⟨m, hm⟩ := (hiff _).mp hw
  have hre : t = -(step * (m : ℝ)) - a.re := by
    have := congrArg Complex.re hm
    simpa using this
  refine ⟨m, ?_, hre.symm⟩
  have h1 : step * (m : ℝ) < -a.re := by linarith
  have h2 : (m : ℝ) < -a.re / step := by rwa [lt_div_iff₀ hstep, mul_comm]
  exact_mod_cast h2.trans hM

/-- Every quasi-character with an archimedean pole on the component lies in some cutoff. -/
private theorem sLocalGammaFiltration_iInf_mem_cutoff (ω : PontryaginDual J₁(S)) (c : Xₛ)
    (hc : onComponent(c, ω)) (hne : (arch(c)).Nonempty) :
    ∃ N : depths, c ∈ sLocalGammaPoleCutoff (F := F) (S := S) ω N := by
  obtain ⟨w, hw⟩ := hne
  refine ⟨fun w' ↦ (sLocalGammaFiltration_iInf_finite c w').toFinset.card, hc, w, hw, ?_⟩
  rw [Set.Finite.encard_eq_coe_toFinset_card (sLocalGammaFiltration_iInf_finite c w)]

/-- After the finite principal values, the pole order on a component is bounded by the
number of archimedean places with a pole there. -/
private theorem sLocalGammaFiltration_iInf_bound (g : B(S)) (c : Xₛ) :
    sLocalPolarMultiplicity (sAdelePrincipalValue F (Finset.Subset.refl S) g) c ≤
      (arch(c)).card := by
  obtain ⟨χ, s, rfl⟩ := exists_sLocalNormTwist (F := F) (S := S) c
  have hb := sLocalIdelicZFunction_principalValue_pole_bound (F := F) (S := S) g χ s
  let ch := quasiCharacterNormTwist (m(S)) (isProperMap_sIdeleQuotientNorm F S).continuous
    ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)
  have hcomp (G : Xₛ → ℂ) : meromorphicOrderAt (fun z ↦ G (shift(ch s, z))) 0 =
      meromorphicOrderAt (fun z ↦ G (ch z)) s := by
    have htw (z : ℂ) : shift(ch s, z) = ch (z + s) := normTwist_normTwist _ _ _ s z
    simp only [htw]
    rw [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt (f := fun z ↦ G (ch z)),
      zero_add]
  have hcard : (arch(ch s)).card = sLocalArchimedeanPoleMultiplicity χ s := by
    unfold sLocalArchPolePlaces sLocalArchimedeanPoleMultiplicity
    congr 1
    refine Finset.filter_congr fun w _ ↦ ?_
    rw [hcomp (fun c ↦ infiniteLocalEulerFactor w (sLocalInfiniteRestriction w c))]
  rw [hcard]
  unfold sLocalPolarMultiplicity
  rw [hcomp (sLocalIdelicZFunction (sAdelePrincipalValue F (Finset.Subset.refl S) g))]
  generalize meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction
    (sAdelePrincipalValue F (Finset.Subset.refl S) g) (ch z)) s = o at hb ⊢
  induction o using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    have hn : -(sLocalArchimedeanPoleMultiplicity χ s : ℤ) ≤ n := WithTop.coe_le_coe.mp hb
    simp only [WithTop.untop₀_coe]
    omega

/-- Paper: Theorem 7.3.4.1(3), p. 365.
The intersection of all stages is the entire-Mellin subspace. -/
theorem sLocalGammaFiltration_iInf (ω : PontryaginDual J₁(S)) :
    (⨅ N : depths, sLocalGammaFiltration ω N) = Γker(ω) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy⟩ := x.property
    obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective _ y
    let f := sAdelePrincipalValue F (Finset.Subset.refl S) g
    have hf : q(S, ω) f = x.val := hy
    rw [mem_sLocalGammaEntireSubmodule ω x f hf]
    intro c hc
    rw [← sLocalPolarMultiplicity_eq_zero_iff]
    by_contra hne
    have hN : 0 < sLocalPolarMultiplicity f c := Nat.pos_of_ne_zero hne
    have hbound : sLocalPolarMultiplicity f c ≤ (arch(c)).card :=
      sLocalGammaFiltration_iInf_bound g c
    obtain ⟨N, hcN⟩ := sLocalGammaFiltration_iInf_mem_cutoff ω c hc
      (Finset.card_pos.mp (hN.trans_le hbound))
    have hx' := (Submodule.mem_iInf _).mp hx N
    have h0 := (Submodule.mem_iInf _).mp hx'
      ⟨(c, sLocalPolarMultiplicity f c), hc, hcN, hN, hbound⟩
    change sLocalThetaPrincipalPartCoeff ω c hc (sLocalPolarMultiplicity f c) x.val = 0 at h0
    rw [← hf] at h0
    exact mem_sLocalThetaPoleBound_iff_leading (sLocalZ_centered f c).1 hN rfl h0
  · intro x hx
    obtain ⟨y, hy⟩ := x.property
    obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective _ y
    let f := sAdelePrincipalValue F (Finset.Subset.refl S) g
    have hf : q(S, ω) f = x.val := hy
    have hent := (mem_sLocalGammaEntireSubmodule ω x f hf).mp hx
    refine (Submodule.mem_iInf _).mpr fun N ↦ (Submodule.mem_iInf _).mpr fun j ↦ ?_
    change sLocalThetaPrincipalPartCoeff ω j.val.1 j.property.1 j.val.2 x.val = 0
    rw [← hf]
    change sLocalZLaurentCoeff f j.val.1 (-(j.val.2 : ℤ)) = 0
    have hZ := (sLocalZ_centered f j.val.1).1
    have ha := hZ.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.1
      (hent j.val.1 j.property.1)
    have he : (fun z ↦ sLocalIdelicZFunction f (shift(j.val.1, z)) /
        z ^ (-(j.val.2 : ℤ) + 1)) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun z ↦ z ^ j.val.2 * toMeromorphicNFAt
          (fun z ↦ sLocalIdelicZFunction f (shift(j.val.1, z))) 0 z / (z - 0)) := by
      filter_upwards [hZ.eq_nhdsNE_toMeromorphicNFAt, self_mem_nhdsWithin] with z hz hz0
      have hz0' : z ≠ 0 := hz0
      rw [hz, sub_zero, zpow_add₀ hz0', zpow_one, zpow_neg, zpow_natCast]
      field_simp
    change complexResidue (fun z ↦ sLocalIdelicZFunction f (shift(j.val.1, z)) /
        z ^ (-(j.val.2 : ℤ) + 1)) 0 = 0
    have hg : AnalyticAt ℂ (fun z ↦ z ^ j.val.2 * toMeromorphicNFAt
        (fun z ↦ sLocalIdelicZFunction f (shift(j.val.1, z))) 0 z) 0 :=
      (analyticAt_id.pow _).mul ha
    rw [mem_sLocalThetaPoleBound_iff_residue_congr he, complexResidue_div_sub hg]
    simp [zero_pow j.property.2.2.1.ne']

/-- Every unitary character of the norm-one group is the restriction of a quasi-character. -/
private theorem sLocalGammaOrbitalQuotient_coeff_exists (ω : PontryaginDual J₁(S)) :
    ∃ c₀ : Xₛ, onComponent(c₀, ω) := by
  let : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
  have hr := range_normOneRestriction (m(S)) (isProperMap_sIdeleQuotientNorm F S)
    ⟨σ t, (hσ t).trans_ne ht⟩
  obtain ⟨c₀, hc₀⟩ : (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ω ∈
      Set.range (normOneRestriction (m(S))) := hr ▸ ⟨ω, rfl⟩
  exact ⟨c₀, hc₀⟩

/-- A norm twist stays on the component of the quasi-character it twists. -/
private theorem sLocalGammaOrbitalQuotient_coeff_onComponent (ω : PontryaginDual J₁(S)) (c₀ : Xₛ)
    (h₀ : onComponent(c₀, ω)) (s : ℂ) : onComponent(shift(c₀, s), ω) := by
  refine Eq.trans ?_ h₀
  ext u
  change c₀ u.val * (((m(S) u.val : ℝ≥0) : ℝ) : ℂ) ^ s = c₀ u.val
  rw [u.prop]
  simp

/-- Two quasi-characters on one component differ by a norm twist. -/
private theorem sLocalGammaOrbitalQuotient_coeff_shift (ω : PontryaginDual J₁(S)) (c₀ c : Xₛ)
    (h₀ : onComponent(c₀, ω)) (hc : onComponent(c, ω)) : ∃ s : ℂ, c = shift(c₀, s) := by
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
  let c₀inv := c₀.comp (ContinuousMonoidHom.inv J(S))
  let P : QuasiCharacter ℝ≥0ˣ := (c * c₀inv).comp σ
  obtain ⟨s, hs⟩ := (existsUnique_complexPower P).exists
  refine ⟨s, ?_⟩
  ext1 g
  let u : J(S) := g * (σ (m(S) g))⁻¹
  have hu_mem : u ∈ J₁(S) := by
    change m(S) (g * (σ (m(S) g))⁻¹) = 1
    rw [map_mul, map_inv, hσ, mul_inv_cancel]
  have hu_eq : c u = c₀ u := DFunLike.congr_fun (hc.trans h₀.symm) ⟨u, hu_mem⟩
  have hdecomp : g = u * σ (m(S) g) := by simp [u]
  have hcg : c g = c u * c (σ (m(S) g)) := by
    conv_lhs => rw [hdecomp]
    exact map_mul c _ _
  have hc₀g : c₀ g = c₀ u * c₀ (σ (m(S) g)) := by
    conv_lhs => rw [hdecomp]
    exact map_mul c₀ _ _
  have hP : c (σ (m(S) g)) * (c₀ (σ (m(S) g)))⁻¹ =
      (((m(S) g : ℝ≥0) : ℝ) : ℂ) ^ s := by
    have h1 := hs (m(S) g)
    change c (σ (m(S) g)) * c₀ (σ (m(S) g))⁻¹ = _ at h1
    rwa [map_inv] at h1
  have hc₀σ_ne : c₀ (σ (m(S) g)) ≠ 0 :=
    ((Group.isUnit _).map c₀).ne_zero
  change c g = c₀ g * (((m(S) g : ℝ≥0) : ℝ) : ℂ) ^ s
  rw [hcg, hc₀g, hu_eq, ← hP]
  field_simp [hc₀σ_ne]

/-- The pairs of an archimedean center on the component and an admissible Laurent order
form a countable set. -/
private theorem sLocalGammaOrbitalQuotient_coeff_countable (ω : PontryaginDual J₁(S)) :
    Countable (ΓIndex(ω, (Set.univ : Set Xₛ))) := by
  obtain ⟨c₀, h₀⟩ := sLocalGammaOrbitalQuotient_coeff_exists ω
  let P (w : InfinitePlace F) := sLocalGammaFiltration_iInf_placePoles c₀ w
  let pole (w : InfinitePlace F) (m : ℕ) : Xₛ :=
    shift(c₀, -((P w).choose_spec.choose * (m : ℝ) : ℂ) - (P w).choose)
  let U := ⋃ w : InfinitePlace F, Set.range (pole w)
  have hU : U.Countable := Set.countable_iUnion fun w ↦ Set.countable_range _
  have hmem (j : ΓIndex(ω, (Set.univ : Set Xₛ))) : j.val.1 ∈ U := by
    obtain ⟨s, hs⟩ := sLocalGammaOrbitalQuotient_coeff_shift ω c₀ j.val.1 h₀ j.property.1
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (j.property.2.2.1.trans_le j.property.2.2.2)
    rw [hs] at hw
    obtain ⟨m, hm⟩ := ((P w).choose_spec.choose_spec.2 s).mp hw
    exact Set.mem_iUnion.mpr ⟨w, m, by rw [hs, hm]⟩
  have : Countable U := hU.to_subtype
  refine Function.Injective.countable
    (f := fun j : ΓIndex(ω, (Set.univ : Set Xₛ)) ↦ ((⟨j.val.1, hmem j⟩ : U), j.val.2)) ?_
  intro j₁ j₂ h
  have h1 : j₁.val.1 = j₂.val.1 := congrArg (fun p ↦ p.1.val) h
  have h2 : j₁.val.2 = j₂.val.2 := congrArg (fun p ↦ p.2) h
  exact Subtype.ext (Prod.ext h1 h2)

/-- There are infinitely many pairs of an archimedean center on the component and an
admissible Laurent order. -/
private theorem sLocalGammaOrbitalQuotient_coeff_infinite (ω : PontryaginDual J₁(S)) :
    Infinite (ΓIndex(ω, (Set.univ : Set Xₛ))) := by
  obtain ⟨c₀, h₀⟩ := sLocalGammaOrbitalQuotient_coeff_exists ω
  let P (w : InfinitePlace F) := sLocalGammaFiltration_iInf_placePoles c₀ w
  let pole (w : InfinitePlace F) (m : ℕ) : Xₛ :=
    shift(c₀, -((P w).choose_spec.choose * (m : ℝ) : ℂ) - (P w).choose)
  have hpole (w : InfinitePlace F) (m : ℕ) : w ∈ arch(pole w m) :=
    ((P w).choose_spec.choose_spec.2 _).mpr ⟨m, rfl⟩
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
  let t : ℝ≥0ˣ := Units.mk0 2 two_ne_zero
  let f : ℕ → ΓIndex(ω, (Set.univ : Set Xₛ)) := fun m ↦
    ⟨(pole w m, 1), sLocalGammaOrbitalQuotient_coeff_onComponent ω c₀ h₀ _, Set.mem_univ _,
      one_pos, Finset.card_pos.mpr ⟨w, hpole w m⟩⟩
  refine Infinite.of_injective f fun m₁ m₂ h ↦ ?_
  have hc : pole w m₁ = pole w m₂ := congrArg (fun j ↦ j.val.1) h
  have hg := DFunLike.congr_fun hc (σ t)
  change c₀ (σ t) * (((m(S) (σ t) : ℝ≥0) : ℝ) : ℂ) ^ (_ : ℂ) =
    c₀ (σ t) * (((m(S) (σ t) : ℝ≥0) : ℝ) : ℂ) ^ (_ : ℂ) at hg
  have hne : c₀ (σ t) ≠ 0 := ((Group.isUnit _).map c₀).ne_zero
  have hpow := congrArg norm (mul_left_cancel₀ hne hg)
  rw [hσ t] at hpow
  have h2 : (0 : ℝ) < ((t : ℝ≥0) : ℝ) := by norm_num [t]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos h2, Complex.norm_cpow_eq_rpow_re_of_pos h2] at hpow
  have hre := (Real.rpow_right_inj h2 (by norm_num [t])).mp hpow
  have hstep := (P w).choose_spec.choose_spec.1
  have hm : (P w).choose_spec.choose * (m₁ : ℝ) = (P w).choose_spec.choose * (m₂ : ℝ) := by
    simpa [Complex.mul_re] using hre
  exact_mod_cast mul_left_cancel₀ hstep.ne' hm

/-- A class lies in the entire-Mellin subspace exactly when all of its archimedean
Laurent coefficients on the component vanish. -/
private theorem sLocalGammaOrbitalQuotient_coeff_ker (ω : PontryaginDual J₁(S))
    (x : fullPV(ω)) :
    x ∈ Γker(ω) ↔ ∀ j : ΓIndex(ω, (Set.univ : Set Xₛ)), ΓCoeff(ω, j) x = 0 := by
  rw [← sLocalGammaFiltration_iInf, Submodule.mem_iInf]
  constructor
  · intro h j
    obtain ⟨N, hN⟩ := sLocalGammaFiltration_iInf_mem_cutoff ω j.val.1 j.property.1
      (Finset.card_pos.mp (j.property.2.2.1.trans_le j.property.2.2.2))
    exact (Submodule.mem_iInf _).mp (h N) ⟨j.val, j.property.1, hN, j.property.2.2⟩
  · intro h N
    exact (Submodule.mem_iInf _).mpr fun j ↦
      h ⟨j.val, j.property.1, Set.mem_univ _, j.property.2.2⟩

-- Repair the open-mapping gap (ERRATA I168) by a Borel–Mittag-Leffler lift.
-- Norm translations give exponentially small finite interpolants at far-left poles;
-- the closed full principal-value range is Fréchet, so the corrections converge.
section GammaInterpolationHelpers

private theorem finite_interpolant_small
    (E ι : Type*) [AddCommGroup E] [Module ℂ E] [Fintype ι]
    (q : Seminorm ℂ E) (v : ι → ℝ → E) (a : ι → ℝ → ℂ) (b : ι → ℝ → ℝ)
    (hv : ∀ i, ∀ᶠ t in atTop, q (v i t) ≤ b i t)
    (ha : ∀ i, Tendsto (fun t ↦ ‖a i t‖ * b i t) atTop (𝓝 0)) :
    Tendsto (fun t ↦ q (∑ i, a i t • v i t)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ apply_nonneg _ _)
    (g := fun t ↦ ∑ i, ‖a i t‖ * b i t)
  · have hall : ∀ᶠ t in atTop, ∀ i, q (v i t) ≤ b i t :=
      Filter.eventually_all.mpr hv
    filter_upwards [hall] with t ht
    refine (Finset.le_sum_of_subadditive q (map_zero q).le (map_add_le_add q) _ _).trans ?_
    apply Finset.sum_le_sum
    intro i hi
    rw [map_smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (ht i) (norm_nonneg _)
  · simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ ↦ ha i)
open Classical in
private theorem finite_level_small
    (E ι : Type*) [AddCommGroup E] [Module ℂ E] [Fintype ι]
    (P : Submodule ℂ E) (L : ι → E →ₗ[ℂ] ℂ)
    (ρ : ℝ → E →ₗ[ℂ] E)
    (hinv : ∀ t x, ρ t (ρ (-t) x) = x)
    (hP : ∀ t x, x ∈ P → ρ t x ∈ P)
    (hK : ∀ t x, x ∈ P → (∀ i, L i x = 0) → ∀ i, L i (ρ t x) = 0)
    (v : ι → E) (hvP : ∀ i, v i ∈ P)
    (hvL : ∀ i j, L i (v j) = if i = j then 1 else 0)
    (q q' : Seminorm ℂ E) (a : ℝ)
    (hbound : ∀ x, ∀ᶠ t in atTop, q (ρ t x) ≤ Real.exp (-a*t) * q' x)
    (hdecay : ∀ y ∈ P, ∀ i,
      Tendsto (fun t ↦ Real.exp (-a*t) * ‖L i (ρ (-t) y)‖) atTop (𝓝 0))
    (c : ι → ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ x ∈ P, (∀ i, L i x = c i) ∧ q x < ε := by
  classical
  let y := ∑ i, c i • v i
  have hyP : y ∈ P := P.sum_mem fun i _ ↦ P.smul_mem _ (hvP i)
  have hyL (i) : L i y = c i := by simp [y, map_sum, map_smul, hvL]
  let z (t : ℝ) := ∑ i, L i (ρ (-t) y) • v i
  have hzP (t) : z t ∈ P := P.sum_mem fun i _ ↦ P.smul_mem _ (hvP i)
  have hzL (t) (i) : L i (z t) = L i (ρ (-t) y) := by simp [z, map_sum, map_smul, hvL]
  have hcoef (t) (i) : L i (ρ t (z t)) = c i := by
    have hzero (j) : L j (z t - ρ (-t) y) = 0 := by rw [map_sub, hzL]; exact sub_self _
    have hh := hK t (z t - ρ (-t) y) (P.sub_mem (hzP t) (hP _ _ hyP)) hzero i
    rw [map_sub, hinv, map_sub, sub_eq_zero, hyL] at hh
    exact hh
  have hsmall : Tendsto (fun t ↦ q (ρ t (z t))) atTop (𝓝 0) := by
    have h := finite_interpolant_small E ι q (fun i t ↦ ρ t (v i))
      (fun i t ↦ L i (ρ (-t) y)) (fun i t ↦ Real.exp (-a*t) * q' (v i))
      (fun i ↦ hbound (v i)) (fun i ↦ ?_)
    · simpa only [z, map_sum, map_smul] using h
    · have hh := (hdecay y hyP i).mul_const (q' (v i))
      convert hh using 1 <;> try { simp }
      funext t
      ring
  obtain ⟨t,ht⟩ := (hsmall.eventually (gt_mem_nhds hε)).exists
  exact ⟨ρ t (z t), hP _ _ (hzP t), hcoef t, ht⟩
private theorem image_action_bound
    (E κ U : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (p : SeminormFamily ℂ E κ) (hp : WithSeminorms p) (r : κ → ℝ)
    (ρ : ℝ → U → U) (J : U → E)
    (he : ∀ i t x, p i (J (ρ t x)) = Real.exp (-r i*t) * p i (J x))
    (q : Seminorm ℂ E) (hq : Continuous q) :
    ∃ a : ℝ, ∃ q' : Seminorm ℂ E,
      ∀ x, ∀ᶠ t in atTop, q (J (ρ t x)) ≤ Real.exp (-a*t) * q' (J x) := by
  classical
  obtain ⟨s,C,hC,hb⟩ := Seminorm.bound_sum_of_continuous hp q hq
  let a := -∑ i ∈ s, |r i|
  let q' : Seminorm ℂ E := C • ∑ i ∈ s, p i
  refine ⟨a,q',fun x ↦ ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have hr (i) (hi : i ∈ s) : a ≤ r i := by
    have h := Finset.single_le_sum (fun i _ ↦ abs_nonneg (r i)) hi
    have h' := neg_abs_le (r i)
    dsimp [a]
    linarith
  have hsum : (∑ i ∈ s, p i (J (ρ t x))) ≤ Real.exp (-a*t) * ∑ i ∈ s, p i (J x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [he]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [hr i hi])) (apply_nonneg _ _)
  have hh := hb (J (ρ t x))
  simp only [smul_apply, sum_apply, NNReal.smul_def, smul_eq_mul] at hh
  change q (J (ρ t x)) ≤ _ at hh
  calc
    q (J (ρ t x)) ≤ (C : ℝ) * ∑ i ∈ s, p i (J (ρ t x)) := hh
    _ ≤ (C : ℝ) * (Real.exp (-a*t) * ∑ i ∈ s, p i (J x)) := mul_le_mul_of_nonneg_left hsum C.coe_nonneg
    _ = Real.exp (-a*t) * q' (J x) := by
      simp only [q', smul_apply, sum_apply, NNReal.smul_def, smul_eq_mul]
      ring
private theorem exponential_polynomial_decay (s : ℂ) (a : ℝ) (hsa : s.re < a)
    (n : ℕ) (b : ℕ → ℂ) :
    Tendsto (fun t : ℝ ↦ Real.exp (-a*t) *
      ‖Complex.exp (s*(t : ℂ)) * ∑ k ∈ Finset.range n, b k * (t : ℂ)^k‖) atTop (𝓝 0) := by
  have hlim (k : ℕ) : Tendsto (fun t : ℝ ↦ t^k * Real.exp (-(a-s.re)*t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) (a-s.re) (sub_pos.mpr hsa)
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    (g := fun t : ℝ ↦ ∑ k ∈ Finset.range n, ‖b k‖ * (t^k * Real.exp (-(a-s.re)*t)))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hS : ‖∑ k ∈ Finset.range n, b k * (t : ℂ)^k‖ ≤ ∑ k ∈ Finset.range n, ‖b k‖ * t^k := by
      simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht] using
        norm_sum_le (Finset.range n) (fun k ↦ b k * (t : ℂ)^k)
    have he : Real.exp (-a*t) * ‖Complex.exp (s*(t : ℂ))‖ = Real.exp (-(a-s.re)*t) := by
      rw [Complex.norm_exp, ← Real.exp_add]
      congr 1
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      ring
    rw [norm_mul, ← mul_assoc, he]
    calc
      _ ≤ Real.exp (-(a-s.re)*t) * ∑ k ∈ Finset.range n, ‖b k‖ * t^k :=
        mul_le_mul_of_nonneg_left hS (Real.exp_pos _).le
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
  · have h := tendsto_finsetSum (Finset.range n) (fun k _ ↦ (hlim k).const_mul ‖b k‖)
    simpa only [mul_zero, Finset.sum_const_zero] using h
open MeasureTheory in
private theorem bergman_trace_multiplier_norm
    (I : Set ℝ) (a : I) (N : ℕ) (f g : schwartzBergmanSubmodule I) (t : ℝ)
    (he : ∀ z ∈ Complex.re ⁻¹' I, g.val z = Complex.exp (-(t : ℂ)*z) * f.val z) :
    lpNorm (weightedVerticalTrace a N g.val) 2 volume =
      Real.exp (-t*(a : ℝ)) * lpNorm (weightedVerticalTrace a N f.val) 2 volume := by
  have hg := schwartzBergman_trace_memLp I a 2 (by norm_num) (by norm_num) N g
  have hf := schwartzBergman_trace_memLp I a 2 (by norm_num) (by norm_num) N f
  have hn (y : ℝ) : ‖weightedVerticalTrace a N g.val y‖ =
      ‖((Real.exp (-t*(a : ℝ))) • weightedVerticalTrace a N f.val) y‖ := by
    have hz : (a : ℂ) + (y : ℂ)*Complex.I ∈ Complex.re ⁻¹' I := by
      change ((a : ℂ) + (y : ℂ)*Complex.I).re ∈ I
      simpa using a.property
    simp only [weightedVerticalTrace]
    rw [he _ hz]
    simp only [weightedVerticalTrace, norm_mul, Complex.norm_exp, Pi.smul_apply, norm_smul,
      Real.norm_of_nonneg (Real.exp_pos _).le, Complex.mul_re, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, neg_zero,
      add_zero, zero_add, sub_zero, mul_one]
    ring
  unfold lpNorm
  rw [eLpNorm_congr_norm_ae hg.aestronglyMeasurable
    (hf.const_smul (Real.exp (-t*(a : ℝ)))).aestronglyMeasurable (Eventually.of_forall hn)]
  change lpNorm ((Real.exp (-t*(a : ℝ))) • weightedVerticalTrace a N f.val) 2 volume = _
  rw [lpNorm_const_smul]
  change |Real.exp (-t*(a : ℝ))| * lpNorm (weightedVerticalTrace a N f.val) 2 volume = _
  rw [abs_of_pos (Real.exp_pos _)]
  rfl
private theorem finite_interpolation
    (E ι : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [Fintype ι]
    (L : ι → E →L[ℂ] ℂ) (hL : LinearIndependent ℂ L) :
    Surjective (fun x : E ↦ fun i ↦ L i x) := by
  classical
  let T : E →ₗ[ℂ] (ι → ℂ) := LinearMap.pi (fun i ↦ (L i).toLinearMap)
  change Surjective T
  apply LinearMap.dualMap_injective_iff.mp
  apply (injective_iff_map_eq_zero _).mpr
  intro f hf
  have hsum : ∑ i, f (Pi.single i 1) • L i = 0 := by
    ext x
    have hTx : T x = ∑ i, L i x • Pi.single i (1 : ℂ) := by
      ext j
      simp [T, Pi.single_apply]
    have hh := congrArg (fun ℓ : Module.Dual ℂ E ↦ ℓ x) hf
    change f (T x) = 0 at hh
    rw [hTx, map_sum] at hh
    simpa only [sum_apply, smul_apply, map_smul, smul_eq_mul, mul_comm, zero_apply] using hh
  have hc := (Fintype.linearIndependent_iff.mp hL) (fun i ↦ f (Pi.single i 1)) hsum
  apply LinearMap.ext
  intro u
  have hu : u = ∑ i, u i • Pi.single i (1 : ℂ) := by
    ext j
    simp [Pi.single_apply]
  change f u = 0
  rw [hu,map_sum]
  simp only [map_smul, hc, smul_zero, Finset.sum_const_zero]
private theorem gamma_frechet_embed
    {X Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (i : X →L[ℂ] Y) (hi : IsClosedEmbedding i) (hY : IsFrechetTVS Y) : IsFrechetTVS X := by
  obtain ⟨hadd,hpoly,hmet,hcomplete⟩ := hY
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  let : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace Y := hcomplete
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  let : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  have hu := AddMonoidHom.isUniformInducing_of_isInducing (f := i.toLinearMap.toAddMonoidHom) hi.isInducing
  exact ⟨inferInstance, hi.eq_induced ▸ PolynormableSpace.induced i.toLinearMap,
    hi.isEmbedding.metrizableSpace, hu.completeSpace hi.isClosed_range.isComplete⟩
private theorem gamma_range_frechet (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ω : PontryaginDual (sIdeleQuotientNorm F S).ker) :
    IsFrechetTVS ↥((sLocalHomogeneousThetaPrincipalValue (F := F) (Finset.Subset.refl S) ω).range) := by
  let D := (sLocalHomogeneousThetaPrincipalValue (F := F) (Finset.Subset.refl S) ω).range
  have hD : IsClosed (D : Set (SLocalHomogeneousThetaSpace F S ω)) :=
    (sLocalHomogeneousThetaPrincipalValue_isClosedEmbedding (F := F) (Finset.Subset.refl S) ω).isClosed_range
  exact gamma_frechet_embed D.subtypeL (D.isClosedEmbedding_subtypeL hD)
    (sLocalHomogeneousThetaSpace_frechet (F := F) (S := S) ω)
private theorem action_on_range
    (G E : Type*) [Monoid G] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (A : G →* (E →L[ℂ] E)) (P : E →ₗ[ℂ] E)
    (hcomm : ∀ g x, A g (P x) = P (A g x)) :
    ∃ ρ : G →* (P.range →L[ℂ] P.range), ∀ g x, (ρ g x).val = A g x.val := by
  have hpres (g) : ∀ x ∈ P.range, A g x ∈ P.range := by
    rintro x ⟨y,rfl⟩
    exact ⟨A g y,(hcomm g y).symm⟩
  let ρ (g : G) : P.range →L[ℂ] P.range := (A g).restrict (hpres g)
  refine ⟨{ toFun := ρ, map_one' := ?_, map_mul' := ?_ },fun g x ↦ rfl⟩
  · ext x
    change A 1 x.val = x.val
    rw [A.map_one]
    rfl
  · intro g h
    ext x
    change A (g*h) x.val = A g (A h x.val)
    rw [A.map_mul]
    rfl
private theorem product_action_bound
    (E X Y κ ιY : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (p : SeminormFamily ℂ X κ) (hp : WithSeminorms p)
    (q : SeminormFamily ℂ Y ιY) (hq : WithSeminorms q)
    (r : κ → ℝ) (s : ιY → ℝ)
    (ρ : ℝ → E →ₗ[ℂ] E) (J : E →ₗ[ℂ] X × Y) (hJ : IsInducing J)
    (hx : ∀ i t x, p i (J (ρ t x)).1 = Real.exp (-r i*t) * p i (J x).1)
    (hy : ∀ i t x, q i (J (ρ t x)).2 = Real.exp (-s i*t) * q i (J x).2)
    (Q : Seminorm ℂ E) (hQ : Continuous Q) :
    ∃ a : ℝ, ∃ Q' : Seminorm ℂ E,
      ∀ x, ∀ᶠ t in atTop, Q (ρ t x) ≤ Real.exp (-a*t) * Q' x := by
  let : PolynormableSpace ℂ X := hp.toPolynormableSpace
  let : PolynormableSpace ℂ Y := hq.toPolynormableSpace
  obtain ⟨B,hB,hQB⟩ := Seminorm.exists_le_comp_of_isInducing hQ hJ
  let Bx := B.comp (LinearMap.inl ℂ X Y)
  let By := B.comp (LinearMap.inr ℂ X Y)
  have hBx : Continuous Bx := hB.comp (continuous_id.prodMk continuous_const)
  have hBy : Continuous By := hB.comp (continuous_const.prodMk continuous_id)
  obtain ⟨ax,Bx',hx'⟩ := image_action_bound X κ E p hp r (fun t ↦ ρ t) (fun x ↦ (J x).1) hx Bx hBx
  obtain ⟨ay,By',hy'⟩ := image_action_bound Y ιY E q hq s (fun t ↦ ρ t) (fun x ↦ (J x).2) hy By hBy
  let a := min ax ay
  let Q' := (Bx'.comp ((LinearMap.fst ℂ X Y).comp J)) + (By'.comp ((LinearMap.snd ℂ X Y).comp J))
  refine ⟨a,Q',fun x ↦ ?_⟩
  filter_upwards [hx' x,hy' x,eventually_ge_atTop (0 : ℝ)] with t htX htY ht
  have heX : Real.exp (-ax*t) ≤ Real.exp (-a*t) := Real.exp_le_exp.mpr (by have := min_le_left ax ay; dsimp [a]; nlinarith)
  have heY : Real.exp (-ay*t) ≤ Real.exp (-a*t) := Real.exp_le_exp.mpr (by have := min_le_right ax ay; dsimp [a]; nlinarith)
  calc
    Q (ρ t x) ≤ B (J (ρ t x)) := hQB _
    _ ≤ Bx (J (ρ t x)).1 + By (J (ρ t x)).2 := by
      have hb := map_add_le_add B ((J (ρ t x)).1,0) (0,(J (ρ t x)).2)
      change B ((J (ρ t x)).1,(J (ρ t x)).2) ≤
        B ((J (ρ t x)).1,0) + B (0,(J (ρ t x)).2)
      simpa only [Prod.mk_add_mk,add_zero,zero_add] using hb
    _ ≤ Real.exp (-ax*t) * Bx' (J x).1 + Real.exp (-ay*t) * By' (J x).2 := add_le_add htX htY
    _ ≤ Real.exp (-a*t) * (Bx' (J x).1 + By' (J x).2) := by
      rw [mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right heX (apply_nonneg _ _))
        (mul_le_mul_of_nonneg_right heY (apply_nonneg _ _))
    _ = Real.exp (-a*t) * Q' x := rfl
private theorem finite_code_prefix (ι : Type*) (code : ι → ℕ)
    (hf : ∀ n, Finite {i : ι // code i = n}) (k : ℕ) :
    Finite {i : ι // code i ≤ k} := by
  letI (n : Fin (k+1)) : Finite {i : ι // code i = n.val} := hf n.val
  let f : {i : ι // code i ≤ k} → (n : Fin (k+1)) × {i : ι // code i = n.val} :=
    fun i ↦ ⟨⟨code i.val,Nat.lt_succ_of_le i.property⟩,⟨i.val,rfl⟩⟩
  apply Finite.of_injective f
  intro i j h
  apply Subtype.ext
  exact congrArg (fun x : (n : Fin (k+1)) × {i : ι // code i = n.val} ↦ x.2.val) h
open Classical in
private theorem surjective_of_translated_coefficients
    (E ι : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsFrechetTVS E) (L : ι → E →L[ℂ] ℂ) (code : ι → ℕ)
    (hf : ∀ k, Finite {i : ι // code i = k})
    (hv : ∀ k, ∃ v : {i : ι // code i = k} → E,
      (∀ i j, code j < k → L j (v i) = 0) ∧
      ∀ i j, (i = j → L j.val (v i) = 1) ∧ (i ≠ j → L j.val (v i) = 0))
    (ρ : ℝ → E →ₗ[ℂ] E) (hinv : ∀ t x, ρ t (ρ (-t) x) = x)
    (hker : ∀ (p : ℕ → Prop) t x, (∀ i, p (code i) → L i x = 0) →
      ∀ i, p (code i) → L i (ρ t x) = 0)
    (hbound : ∀ q : Seminorm ℂ E, Continuous q → ∃ a : ℝ, ∃ q' : Seminorm ℂ E,
      ∀ x, ∀ᶠ t in atTop, q (ρ t x) ≤ Real.exp (-a*t) * q' x)
    (htail : ∀ a : ℝ, ∃ K : ℕ, ∀ i, K ≤ code i → ∀ y,
      Tendsto (fun t ↦ Real.exp (-a*t) * ‖L i (ρ (-t) y)‖) atTop (𝓝 0)) :
    Surjective (fun x : E ↦ fun i ↦ L i x) := by
  obtain ⟨hadd,hpoly,hmet,hcomplete⟩ := hE
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace E := hcomplete
  letI (k : ℕ) : Fintype {i : ι // code i = k} := Fintype.ofFinite _
  have hs : Surjective (fun x : E ↦ fun k (i : {i : ι // code i = k}) ↦ L i.val x) := by
    apply surjective_coeff_of_eventually_small
    · intro k c
      obtain ⟨v,hv0,hvraw⟩ := hv k
      have hv1 (i j) : L j.val (v i) = if i = j then 1 else 0 := by
        by_cases h : i = j
        · rw [if_pos h]; exact (hvraw i j).1 h
        · rw [if_neg h]; exact (hvraw i j).2 h
      let y := ∑ i, c i • v i
      refine ⟨y,?_,?_⟩
      · intro j hj i
        simp [y,map_sum,map_smul,hv0 _ _ (by rw [i.property]; exact hj)]
      · intro i
        simp [y,map_sum,map_smul,hv1,eq_comm]
    · intro q hq
      obtain ⟨a,q',hb⟩ := hbound q hq
      obtain ⟨K,hK⟩ := htail a
      refine ⟨K,fun k hk c ε hε ↦ ?_⟩
      let P : Submodule ℂ E := ⨅ i : {i : ι // code i < k}, (L i.val).ker
      have hP (x : E) : x ∈ P ↔ ∀ i, code i < k → L i x = 0 := by simp [P]
      obtain ⟨v,hv0,hv1⟩ := hv k
      obtain ⟨x,hx,hL,hsmall⟩ := finite_level_small E {i : ι // code i = k} P
        (fun i ↦ (L i.val).toLinearMap) ρ hinv
        (fun t x hx ↦ (hP _).mpr (hker (fun n ↦ n < k) t x ((hP _).mp hx)))
        (fun t x hx hz i ↦ hker (fun n ↦ n ≤ k) t x (fun j hj ↦ by
          rcases lt_or_eq_of_le hj with hj | hj
          · exact (hP _).mp hx j hj
          · exact hz ⟨j,hj⟩) i.val (by rw [i.property]))
        v (fun i ↦ (hP _).mpr (hv0 i)) (fun i j ↦ by
          by_cases h : i = j
          · subst j
            rw [if_pos rfl]
            exact (hv1 i i).1 rfl
          · rw [if_neg h]
            exact (hv1 j i).2 (Ne.symm h)) q q' a hb
        (fun y hy i ↦ hK i.val (by rw [i.property]; exact hk) y) c ε hε
      · refine ⟨x,fun j hj i ↦ (hP x).mp hx i.val ?_,hL,hsmall⟩
        rw [i.property]
        exact hj
  intro c
  obtain ⟨x,hx⟩ := hs (fun k i ↦ c i.val)
  refine ⟨x,funext fun i ↦ ?_⟩
  exact congrFun (congrFun hx (code i)) ⟨i,rfl⟩
private theorem real_action_inverse (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (B : Multiplicative ℝ →* (E →L[ℂ] E)) (t : ℝ) (x : E) :
    B (Multiplicative.ofAdd (-t)) (B (Multiplicative.ofAdd (-(-t))) x) = x := by
  have hh : (Multiplicative.ofAdd (-t) : Multiplicative ℝ) * Multiplicative.ofAdd (-(-t)) = 1 := by
    change -t + -(-t) = 0
    ring
  have hB : B (Multiplicative.ofAdd (-t)) * B (Multiplicative.ofAdd (-(-t))) = 1 := by
    rw [← B.map_mul,hh,B.map_one]
  exact congrArg (fun f : E →L[ℂ] E ↦ f x) hB

private theorem gamma_full_action (ω : PontryaginDual J₁(S)) :
    ∃ ρ : J(S) →* (fullPV(ω) →L[ℂ] fullPV(ω)),
      ∀ g x, (ρ g x).val = A(S, ω) g x.val := by
  exact action_on_range J(S) Θ(S, ω) A(S, ω) PV((Finset.Subset.refl S), ω)
    (fun g x ↦ (sLocalPW_principalValue_diagram_comm (F := F) (Finset.Subset.refl S) ω g x).symm)

private theorem gamma_action_laurent (ω : PontryaginDual J₁(S)) (x : Θ(S, ω))
    (c : Xₛ) (hc : onComponent(c, ω)) (k : ℕ) (hk : k ≤ sLocalRhoPoleOrder c)
    (u : (SAdeleRing F S)ˣ) :
    sLocalThetaPrincipalPartCoeff ω c hc k (A(S, ω) (QuotientGroup.mk u) x) =
      c (QuotientGroup.mk u) * ∑ j ∈ Finset.range (sLocalRhoPoleOrder c-k+1),
        sLocalThetaPrincipalPartCoeff ω c hc (k+j) x *
          (Real.log (((m(S) (QuotientGroup.mk u)).val : ℝ)) : ℂ)^j / (j.factorial : ℂ) := by
  obtain ⟨f,rfl⟩ := Submodule.mkQ_surjective (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ω)) x
  rw [(existsUnique_sLocalHomogeneousThetaAction (F := F) (S := S) ω).exists.choose_spec.2 u f]
  change sLocalPrincipalPartCoeff c k (schwartzBruhatUnitTranslate u f) =
    c (QuotientGroup.mk u) * ∑ j ∈ Finset.range (sLocalRhoPoleOrder c-k+1),
      sLocalPrincipalPartCoeff c (k+j) f *
        (Real.log (((m(S) (QuotientGroup.mk u)).val : ℝ)) : ℂ)^j / (j.factorial : ℂ)
  exact sLocalPrincipalPartCoeff_translate c k hk u f

private theorem gamma_high_coeff_zero (ω : PontryaginDual J₁(S)) (x : fullPV(ω))
    (c : Xₛ) (hc : onComponent(c, ω)) (k : ℕ) (hk : (arch(c)).card < k) :
    sLocalThetaPrincipalPartCoeff ω c hc k x.val = 0 := by
  obtain ⟨y,hy⟩ := x.property
  obtain ⟨f,rfl⟩ := Submodule.mkQ_surjective (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ω)) y
  let g := sAdelePrincipalValue F (Finset.Subset.refl S) f
  have hg : q(S, ω) g = x.val := hy
  rw [← hg]
  change sLocalPrincipalPartCoeff c k g = 0
  by_contra hne
  have hpos : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hk
  have hpole := (sLocalPrincipalPartCoeff_ne_zero_imp_pole c k hpos g hne).2
  have hb := gammaFiltration_principalValue_bound f c
  dsimp [g] at hpole
  omega

private theorem gamma_zeta_translate (χ : PontryaginDual J(S)) (g : J(S)) :
    let ω := χ.comp (⟨(m(S)).ker.subtype, continuous_subtype_val⟩ : J₁(S) →ₜ* J(S))
    let Z := sLocalZetaPair (F := F) (S := S) χ
    ∀ x : Θ(S, ω),
      EqOn (Z (A(S, ω) g x)).1.val
        (fun z ↦ shift((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ, z) g * (Z x).1.val z)
        (Complex.re ⁻¹' Ioi (0 : ℝ)) ∧
      EqOn (Z (A(S, ω) g x)).2.val
        (fun z ↦ shift((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ, z) g * (Z x).2.val z)
        (Complex.re ⁻¹' Iio (1 : ℝ)) := by
  intro ω Z x
  obtain ⟨u,rfl⟩ := QuotientGroup.mk_surjective g
  refine Quotient.inductionOn' x ?_
  intro f
  have ha := (existsUnique_sLocalHomogeneousThetaAction (F := F) (S := S) ω).exists.choose_spec.2 u f
  have ht := sLocalZetaPair_translate (F := F) (S := S) χ u f
  constructor
  · intro z hz
    have he := congrArg (fun y : Θ(S, ω) ↦ (Z y).1.val z) ha
    exact he.trans (ht.1 hz)
  · intro z hz
    have he := congrArg (fun y : Θ(S, ω) ↦ (Z y).2.val z) ha
    exact he.trans (ht.2 hz)

open MeasureTheory in
private theorem gamma_action_bound (χ : PontryaginDual J(S)) (g : ℝ → J(S))
    (hnorm : ∀ t, (((m(S) (g t)).val : ℝ)) = Real.exp (-t))
    (hχ : ∀ t, χ (g t) = 1) :
    let ω := χ.comp (⟨(m(S)).ker.subtype, continuous_subtype_val⟩ : J₁(S) →ₜ* J(S))
    ∀ (ρ : J(S) →* (fullPV(ω) →L[ℂ] fullPV(ω))),
      (∀ h x, (ρ h x).val = A(S, ω) h x.val) →
    ∀ Q : Seminorm ℂ (fullPV(ω)), Continuous Q →
      ∃ a : ℝ, ∃ Q' : Seminorm ℂ (fullPV(ω)),
        ∀ x, ∀ᶠ t in atTop, Q (ρ (g t) x) ≤ Real.exp (-a*t) * Q' x := by
  intro ω ρ hρ Q hQ
  let X := SchwartzBergman (Ioi (0 : ℝ))
  let Y := SchwartzBergman (Iio (1 : ℝ))
  let Z := sLocalZetaPair (F := F) (S := S) χ
  let J : fullPV(ω) →ₗ[ℂ] X × Y := Z.comp (fullPV(ω)).subtype
  have hJ : IsInducing J := (sLocalZetaPair_isClosedEmbedding (F := F) (S := S) χ).isInducing.comp
    Topology.IsInducing.subtypeVal
  let p (I : Set ℝ) : I × ℕ → Seminorm ℂ (SchwartzBergman I) := fun i ↦ Seminorm.of
    (fun f : schwartzBergmanSubmodule I ↦ (eLpNorm (weightedVerticalTrace i.1 i.2 f.val) 2 volume).toReal)
    (schwartzBergman_l2_seminorm I i).1 (schwartzBergman_l2_seminorm I i).2
  have hp (I : Set ℝ) : WithSeminorms (p I) := withGeneratingSeminorms_spec _ _
  have hfactor (t : ℝ) (z : ℂ) :
      shift((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ, z) (g t) =
        Complex.exp (-(t : ℂ)*z) := by
    change (χ (g t) : ℂ) * ((((m(S) (g t)).val : ℝ) : ℂ)^z) = _
    rw [hχ t, Circle.coe_one, one_mul, hnorm t]
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
      ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, Complex.ofReal_neg]
  apply product_action_bound (fullPV(ω)) X Y ((Ioi (0 : ℝ)) × ℕ) ((Iio (1 : ℝ)) × ℕ)
    (p _) (hp _) (p _) (hp _) (fun i ↦ (i.1 : ℝ)) (fun i ↦ (i.1 : ℝ))
    (fun t ↦ (ρ (g t)).toLinearMap) J hJ ?_ ?_ Q hQ
  · intro i t x
    have he : ∀ z ∈ Complex.re ⁻¹' Ioi (0 : ℝ),
        (J (ρ (g t) x)).1.val z = Complex.exp (-(t : ℂ)*z) * (J x).1.val z := by
      intro z hz
      have hmap := congrArg (fun y : Θ(S, ω) ↦ (Z y).1.val z) (hρ (g t) x)
      have ht := (gamma_zeta_translate χ (g t) x.val).1 hz
      exact hmap.trans (ht.trans (congrArg (fun w : ℂ ↦ w * (J x).1.val z) (hfactor t z)))
    have h := bergman_trace_multiplier_norm (Ioi (0 : ℝ)) i.1 i.2 (J x).1 (J (ρ (g t) x)).1 t he
    change lpNorm (weightedVerticalTrace i.1 i.2 (J (ρ (g t) x)).1.val) 2 volume =
      Real.exp (-(i.1 : ℝ)*t) * lpNorm (weightedVerticalTrace i.1 i.2 (J x).1.val) 2 volume
    rw [show -(i.1 : ℝ)*t = -t*(i.1 : ℝ) by ring]
    exact h
  · intro i t x
    have he : ∀ z ∈ Complex.re ⁻¹' Iio (1 : ℝ),
        (J (ρ (g t) x)).2.val z = Complex.exp (-(t : ℂ)*z) * (J x).2.val z := by
      intro z hz
      have hmap := congrArg (fun y : Θ(S, ω) ↦ (Z y).2.val z) (hρ (g t) x)
      have ht := (gamma_zeta_translate χ (g t) x.val).2 hz
      exact hmap.trans (ht.trans (congrArg (fun w : ℂ ↦ w * (J x).2.val z) (hfactor t z)))
    have h := bergman_trace_multiplier_norm (Iio (1 : ℝ)) i.1 i.2 (J x).2 (J (ρ (g t) x)).2 t he
    change lpNorm (weightedVerticalTrace i.1 i.2 (J (ρ (g t) x)).2.val) 2 volume =
      Real.exp (-(i.1 : ℝ)*t) * lpNorm (weightedVerticalTrace i.1 i.2 (J x).2.val) 2 volume
    rw [show -(i.1 : ℝ)*t = -t*(i.1 : ℝ) by ring]
    exact h

private theorem gamma_weight_shift (τ : ℝ≥0ˣ →ₜ* J(S)) (hτ : RightInverse τ (m(S)))
    (c : Xₛ) (z : ℂ) :
    let u : ℝ≥0ˣ := Units.mk0 2 two_ne_zero
    Real.log ‖shift(c,z) (τ u)‖ / Real.log 2 = Real.log ‖c (τ u)‖ / Real.log 2 + z.re := by
  intro u
  have hu : (((u : ℝ≥0ˣ).val : ℝ)) = 2 := by norm_num [u]
  have hn : ‖shift(c,z) (τ u)‖ = ‖c (τ u)‖ * (2 : ℝ)^z.re := by
    change ‖c (τ u) * ((((m(S) (τ u)).val : ℝ) : ℂ)^z)‖ = _
    rw [norm_mul,hτ u,hu,Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
  have hc : ‖c (τ u)‖ ≠ 0 := norm_ne_zero_iff.mpr (((Group.isUnit (τ u)).map c).ne_zero)
  rw [hn,Real.log_mul hc (Real.rpow_pos_of_pos (by norm_num) _).ne',Real.log_rpow (by norm_num)]
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  field_simp

private theorem gamma_finite_centers_above (ω : PontryaginDual J₁(S))
    (τ : ℝ≥0ˣ →ₜ* J(S)) (hτ : RightInverse τ (m(S))) (A : ℝ) :
    let u : ℝ≥0ˣ := Units.mk0 2 two_ne_zero
    Set.Finite {c : Xₛ | onComponent(c,ω) ∧ (arch(c)).Nonempty ∧
      A ≤ Real.log ‖c (τ u)‖ / Real.log 2} := by
  intro u
  classical
  obtain ⟨c₀,h₀⟩ := sLocalGammaOrbitalQuotient_coeff_exists ω
  let P (w : InfinitePlace F) := sLocalGammaFiltration_iInf_placePoles c₀ w
  let b := Real.log ‖c₀ (τ u)‖ / Real.log 2
  let pole (w : InfinitePlace F) (n : ℕ) : Xₛ :=
    shift(c₀, -((P w).choose_spec.choose * (n : ℝ) : ℂ) - (P w).choose)
  choose N hN using fun w : InfinitePlace F ↦
    exists_nat_gt ((b - (P w).choose.re - A) / (P w).choose_spec.choose)
  let U := ⋃ w : InfinitePlace F, Set.range (fun n : Fin (N w) ↦ pole w n.val)
  have hU : U.Finite := Set.finite_iUnion fun w ↦ Set.finite_range _
  apply hU.subset
  rintro c ⟨hc,hw,hA⟩
  obtain ⟨s,hs⟩ := sLocalGammaOrbitalQuotient_coeff_shift ω c₀ c h₀ hc
  obtain ⟨w,hw⟩ := hw
  rw [hs] at hw
  obtain ⟨n,hn⟩ := ((P w).choose_spec.choose_spec.2 s).mp hw
  have he : c = pole w n := by rw [hs,hn]
  have hwgt : Real.log ‖c (τ u)‖ / Real.log 2 =
      b - (P w).choose_spec.choose * (n : ℝ) - (P w).choose.re := by
    rw [he]
    have h := gamma_weight_shift τ hτ c₀
      (-((P w).choose_spec.choose * (n : ℝ) : ℂ) - (P w).choose)
    change Real.log ‖(pole w n) (τ u)‖ / Real.log 2 = b + _ at h
    rw [h]
    simp only [Complex.sub_re,Complex.neg_re,Complex.ofReal_re,Complex.mul_re,
      Complex.ofReal_im,mul_zero,sub_zero]
    ring
  have hstep := (P w).choose_spec.choose_spec.1
  have hnr : (n : ℝ) < N w := lt_of_le_of_lt
    ((le_div_iff₀ hstep).mpr (by rw [hwgt] at hA; linarith)) (hN w)
  have hnn : n < N w := by exact_mod_cast hnr
  exact Set.mem_iUnion.mpr ⟨w,⟨⟨n,hnn⟩,he.symm⟩⟩

private theorem gamma_finite_indices_above (ω : PontryaginDual J₁(S))
    (τ : ℝ≥0ˣ →ₜ* J(S)) (hτ : RightInverse τ (m(S))) (A : ℝ) :
    let u : ℝ≥0ˣ := Units.mk0 2 two_ne_zero
    Set.Finite {j : ΓIndex(ω,(Set.univ : Set Xₛ)) |
      A ≤ Real.log ‖j.val.1 (τ u)‖ / Real.log 2} := by
  intro u
  have hC := gamma_finite_centers_above ω τ hτ A
  apply Set.Finite.of_injOn (f := fun j : ΓIndex(ω,(Set.univ : Set Xₛ)) ↦ j.val) ?_
    Subtype.val_injective.injOn (hC.prod (Set.finite_Iic (Fintype.card (InfinitePlace F))))
  intro j hj
  exact ⟨⟨j.property.1,Finset.card_pos.mp (j.property.2.2.1.trans_le j.property.2.2.2),hj⟩,
    j.property.2.2.2.trans (Finset.card_le_univ _)⟩

private theorem gamma_block_code (ω : PontryaginDual J₁(S)) :
    ∃ code : ΓIndex(ω,(Set.univ : Set Xₛ)) → ℕ,
      (∀ i j, code i = code j ↔ i.val.1 = j.val.1) ∧
      ∀ k, Finite {j : ΓIndex(ω,(Set.univ : Set Xₛ)) // code j = k} := by
  classical
  let C := {c : Xₛ // onComponent(c,ω) ∧ (arch(c)).Nonempty}
  let center (j : ΓIndex(ω,(Set.univ : Set Xₛ))) : C :=
    ⟨j.val.1,j.property.1,Finset.card_pos.mp (j.property.2.2.1.trans_le j.property.2.2.2)⟩
  have : Countable (ΓIndex(ω,(Set.univ : Set Xₛ))) := sLocalGammaOrbitalQuotient_coeff_countable ω
  have : Countable C := Function.Injective.countable
    (f := fun c : C ↦ (⟨(c.val,1),c.property.1,Set.mem_univ _,one_pos,Finset.card_pos.mpr c.property.2⟩ : ΓIndex(ω,(Set.univ : Set Xₛ))))
    (fun i j h ↦ Subtype.ext (congrArg (fun j : ΓIndex(ω,(Set.univ : Set Xₛ)) ↦ j.val.1) h))
  let : Encodable C := Encodable.ofCountable C
  let code (j : ΓIndex(ω,(Set.univ : Set Xₛ))) := Encodable.encode (center j)
  have he (i j) : code i = code j ↔ i.val.1 = j.val.1 := by
    constructor
    · intro h
      exact congrArg Subtype.val (Encodable.encode_injective h)
    · intro h
      exact congrArg Encodable.encode (Subtype.ext h)
  refine ⟨code,he,fun k ↦ ?_⟩
  let f : {j : ΓIndex(ω,(Set.univ : Set Xₛ)) // code j = k} → Fin (Fintype.card (InfinitePlace F)+1) :=
    fun j ↦ ⟨j.val.val.2,Nat.lt_succ_of_le (j.val.property.2.2.2.trans (Finset.card_le_univ _))⟩
  apply Finite.of_injective f
  intro i j h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact (he i.val j.val).mp (i.property.trans j.property.symm)
  · exact congrArg Fin.val h

private theorem gamma_positive_flow :
    ∃ ν : Multiplicative ℝ →* ℝ≥0ˣ,
      ∀ t : ℝ, ((ν (Multiplicative.ofAdd t)).val : ℝ) = Real.exp t := by
  let ν : Multiplicative ℝ →* ℝ≥0ˣ :=
    { toFun := fun t ↦ Units.mk0 (Real.exp t.toAdd).toNNReal (by positivity)
      map_one' := by apply Units.ext; apply NNReal.coe_injective; simp
      map_mul' := by
        intro t u
        apply Units.ext
        apply NNReal.coe_injective
        simp [Real.exp_add,max_eq_left (Real.exp_pos t.toAdd).le,
          max_eq_left (Real.exp_pos u.toAdd).le,
          max_eq_left (mul_nonneg (Real.exp_pos t.toAdd).le (Real.exp_pos u.toAdd).le)] }
  exact ⟨ν,fun t ↦ Real.coe_toNNReal _ (Real.exp_pos t).le⟩

private theorem gamma_character_exponent (τ : ℝ≥0ˣ →ₜ* J(S))
    (ν : Multiplicative ℝ →* ℝ≥0ˣ)
    (hν : ∀ t : ℝ, ((ν (Multiplicative.ofAdd t)).val : ℝ) = Real.exp t) (c : Xₛ) :
    ∃ s : ℂ,
      (∀ t : ℝ, c (τ (ν (Multiplicative.ofAdd t))) = Complex.exp (s*(t : ℂ))) ∧
      (let u : ℝ≥0ˣ := Units.mk0 2 two_ne_zero
       Real.log ‖c (τ u)‖ / Real.log 2 = s.re) := by
  obtain ⟨s,hs,_⟩ := existsUnique_complexPower (c.comp τ)
  refine ⟨s,fun t ↦ ?_,?_⟩
  · have h := hs (ν (Multiplicative.ofAdd t))
    change c (τ (ν (Multiplicative.ofAdd t))) =
      ((((ν (Multiplicative.ofAdd t)).val : ℝ) : ℂ)^s) at h
    rw [hν t] at h
    rw [h,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
      ← Complex.ofReal_log (Real.exp_pos _).le,Real.log_exp]
    congr 1
    ring
  · intro u
    have h := congrArg norm (hs u)
    change ‖c (τ u)‖ = ‖(((u.val : ℝ) : ℂ)^s)‖ at h
    have hu : ((u.val : ℝ)) = 2 := by norm_num [u]
    rw [hu,Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)] at h
    rw [h,Real.log_rpow (by norm_num)]
    exact mul_div_cancel_right₀ _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'

private theorem gamma_action_laurent_class (ω : PontryaginDual J₁(S)) (x : Θ(S, ω))
    (c : Xₛ) (hc : onComponent(c, ω)) (k : ℕ) (hk : k ≤ sLocalRhoPoleOrder c)
    (g : J(S)) :
    sLocalThetaPrincipalPartCoeff ω c hc k (A(S, ω) g x) =
      c g * ∑ j ∈ Finset.range (sLocalRhoPoleOrder c-k+1),
        sLocalThetaPrincipalPartCoeff ω c hc (k+j) x *
          (Real.log (((m(S) g).val : ℝ)) : ℂ)^j / (j.factorial : ℂ) := by
  refine Quotient.inductionOn' g ?_
  intro u
  exact gamma_action_laurent ω x c hc k hk u

private theorem gamma_coefficient_decay (ω : PontryaginDual J₁(S))
    (τ : ℝ≥0ˣ →ₜ* J(S)) (hτ : RightInverse τ (m(S)))
    (ν : Multiplicative ℝ →* ℝ≥0ˣ)
    (hν : ∀ t : ℝ, ((ν (Multiplicative.ofAdd t)).val : ℝ) = Real.exp t)
    (ρ : J(S) →* (fullPV(ω) →L[ℂ] fullPV(ω)))
    (hρ : ∀ g x, (ρ g x).val = A(S, ω) g x.val)
    (c : Xₛ) (hc : onComponent(c, ω)) (k : ℕ) (hk : k ≤ sLocalRhoPoleOrder c)
    (a : ℝ) (ha : Real.log ‖c (τ (Units.mk0 2 two_ne_zero))‖ / Real.log 2 < a)
    (y : fullPV(ω)) :
    Tendsto (fun t : ℝ ↦ Real.exp (-a*t) *
      ‖sLocalThetaPrincipalPartCoeff ω c hc k (ρ (τ (ν (Multiplicative.ofAdd t))) y).val‖)
      atTop (𝓝 0) := by
  obtain ⟨s,hs,hw⟩ := gamma_character_exponent τ ν hν c
  let N := sLocalRhoPoleOrder c-k+1
  let b (j : ℕ) := sLocalThetaPrincipalPartCoeff ω c hc (k+j) y.val / (j.factorial : ℂ)
  have he (t : ℝ) :
      sLocalThetaPrincipalPartCoeff ω c hc k (ρ (τ (ν (Multiplicative.ofAdd t))) y).val =
        Complex.exp (s*(t : ℂ)) * ∑ j ∈ Finset.range N, b j * (t : ℂ)^j := by
    let g := τ (ν (Multiplicative.ofAdd t))
    have hlog : Real.log (((m(S) g).val : ℝ)) = t := by
      change Real.log (((m(S) (τ (ν (Multiplicative.ofAdd t)))).val : ℝ)) = t
      rw [hτ,hν,Real.log_exp]
    calc
      _ = sLocalThetaPrincipalPartCoeff ω c hc k (A(S, ω) g y.val) :=
        congrArg (sLocalThetaPrincipalPartCoeff ω c hc k) (hρ g y)
      _ = c g * ∑ j ∈ Finset.range N,
          sLocalThetaPrincipalPartCoeff ω c hc (k+j) y.val *
            (Real.log (((m(S) g).val : ℝ)) : ℂ)^j / (j.factorial : ℂ) :=
        gamma_action_laurent_class ω y.val c hc k hk g
      _ = _ := by
        apply congrArg₂ (fun u v : ℂ ↦ u*v) (hs t)
        apply Finset.sum_congr rfl
        intro j hj
        calc
          _ = sLocalThetaPrincipalPartCoeff ω c hc (k+j) y.val * (t : ℂ)^j / (j.factorial : ℂ) :=
            congrArg (fun w : ℂ ↦ sLocalThetaPrincipalPartCoeff ω c hc (k+j) y.val * w^j / (j.factorial : ℂ))
              (congrArg Complex.ofReal hlog)
          _ = b j * (t : ℂ)^j := by dsimp [b]; ring
  have hsa : s.re < a := by rw [← hw]; exact ha
  exact (exponential_polynomial_decay s a hsa N b).congr'
    (Eventually.of_forall fun t ↦ (congrArg (fun w : ℂ ↦ Real.exp (-a*t)*‖w‖) (he t)).symm)

private theorem gamma_finite_coeff_independent (ω : PontryaginDual J₁(S))
    (ι : Type*) [Finite ι] (j : ι → ΓIndex(ω,(Set.univ : Set Xₛ))) (hj : Injective j) :
    LinearIndependent ℂ (fun i ↦ ΓCoeff(ω,j i)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose N hN using fun i ↦ sLocalGammaFiltration_iInf_mem_cutoff ω (j i).val.1
    (j i).property.1 (Finset.card_pos.mp ((j i).property.2.2.1.trans_le (j i).property.2.2.2))
  let M : depths := Finset.univ.sup N
  have hM (i : ι) : (j i).val.1 ∈ sLocalGammaPoleCutoff (F := F) (S := S) ω M := by
    obtain ⟨hc,w,hw,hcard⟩ := hN i
    refine ⟨hc,w,hw,hcard.trans ?_⟩
    have hle : N i ≤ M := Finset.le_sup (Finset.mem_univ i)
    exact_mod_cast hle w
  let e (i : ι) : ΓIndex(ω,sLocalGammaPoleCutoff (F := F) (S := S) ω M) :=
    ⟨(j i).val,(j i).property.1,hM i,(j i).property.2.2⟩
  have he : Injective e := by
    intro i k h
    apply hj
    exact Subtype.ext (congrArg (fun a : ΓIndex(ω,sLocalGammaPoleCutoff (F := F) (S := S) ω M) ↦ a.val) h)
  exact (sLocalGammaFiltration_coeff_independent ω M).2.comp e he

open Classical in
private theorem gamma_prefix_biorthogonal (ω : PontryaginDual J₁(S))
    (code : ΓIndex(ω,(Set.univ : Set Xₛ)) → ℕ)
    (hf : ∀ n, Finite {j : ΓIndex(ω,(Set.univ : Set Xₛ)) // code j = n}) (k : ℕ) :
    ∃ v : {j : ΓIndex(ω,(Set.univ : Set Xₛ)) // code j = k} → fullPV(ω),
      (∀ i j, code j < k → ΓCoeff(ω,j) (v i) = 0) ∧
      ∀ i j, (i = j → ΓCoeff(ω,j.val) (v i) = 1) ∧ (i ≠ j → ΓCoeff(ω,j.val) (v i) = 0) := by
  classical
  let I := {j : ΓIndex(ω,(Set.univ : Set Xₛ)) // code j ≤ k}
  let B := {j : ΓIndex(ω,(Set.univ : Set Xₛ)) // code j = k}
  letI : Finite I := finite_code_prefix _ code hf k
  letI : Fintype I := Fintype.ofFinite I
  have hli := gamma_finite_coeff_independent ω I Subtype.val Subtype.val_injective
  have hs := finite_interpolation (fullPV(ω)) I (fun j ↦ ΓCoeff(ω,j.val)) hli
  choose v hv using fun i : B ↦ hs (fun j : I ↦ if j.val = i.val then 1 else 0)
  refine ⟨v,?_,?_⟩
  · intro i j hj
    have hne : j ≠ i.val := by
      intro h
      have hi := i.property
      rw [← h] at hi
      omega
    exact (congrFun (hv i) ⟨j,le_of_lt hj⟩).trans (if_neg hne)
  · intro i j
    have h := congrFun (hv i) (⟨j.val,le_of_eq j.property⟩ : I)
    constructor
    · intro hij
      exact h.trans (if_pos (congrArg Subtype.val hij).symm)
    · intro hij
      exact h.trans (if_neg (fun he ↦ hij (Subtype.ext he.symm)))

private theorem gamma_coeff_kernel_invariant (ω : PontryaginDual J₁(S))
    (ρ : J(S) →* (fullPV(ω) →L[ℂ] fullPV(ω)))
    (hρ : ∀ g x, (ρ g x).val = A(S, ω) g x.val)
    (U : Xₛ → Prop) (x : fullPV(ω))
    (hx : ∀ j : ΓIndex(ω,(Set.univ : Set Xₛ)), U j.val.1 → ΓCoeff(ω,j) x = 0)
    (g : J(S)) (j : ΓIndex(ω,(Set.univ : Set Xₛ))) (hj : U j.val.1) :
    ΓCoeff(ω,j) (ρ g x) = 0 := by
  have hk : j.val.2 ≤ sLocalRhoPoleOrder j.val.1 := by
    rw [sLocalRhoPoleOrder_eq_card_polePlaces]
    exact j.property.2.2.2.trans (Nat.le_add_right _ _)
  change sLocalThetaPrincipalPartCoeff ω j.val.1 j.property.1 j.val.2 (ρ g x).val = 0
  calc
    _ = sLocalThetaPrincipalPartCoeff ω j.val.1 j.property.1 j.val.2 (A(S, ω) g x.val) :=
      congrArg (sLocalThetaPrincipalPartCoeff ω j.val.1 j.property.1 j.val.2) (hρ g x)
    _ = j.val.1 g * ∑ r ∈ Finset.range (sLocalRhoPoleOrder j.val.1-j.val.2+1),
        sLocalThetaPrincipalPartCoeff ω j.val.1 j.property.1 (j.val.2+r) x.val *
          (Real.log (((m(S) g).val : ℝ)) : ℂ)^r / (r.factorial : ℂ) :=
      gamma_action_laurent_class ω x.val j.val.1 j.property.1 j.val.2 hk g
    _ = 0 := by
      have hz (r : ℕ) : sLocalThetaPrincipalPartCoeff ω j.val.1 j.property.1 (j.val.2+r) x.val = 0 := by
        by_cases hr : j.val.2+r ≤ (arch(j.val.1)).card
        · let j' : ΓIndex(ω,(Set.univ : Set Xₛ)) :=
            ⟨(j.val.1,j.val.2+r),j.property.1,Set.mem_univ _,by have := j.property.2.2.1; omega,hr⟩
          exact hx j' hj
        · exact gamma_high_coeff_zero ω x j.val.1 j.property.1 _ (Nat.lt_of_not_ge hr)
      rw [Finset.sum_eq_zero (fun r hr ↦ by rw [hz,zero_mul,zero_div]),mul_zero]

private theorem gamma_coded_kernel (ω : PontryaginDual J₁(S))
    (ρ : J(S) →* (fullPV(ω) →L[ℂ] fullPV(ω)))
    (hρ : ∀ g x, (ρ g x).val = A(S, ω) g x.val)
    (code : ΓIndex(ω,(Set.univ : Set Xₛ)) → ℕ)
    (he : ∀ i j, code i = code j ↔ i.val.1 = j.val.1)
    (p : ℕ → Prop) (g : J(S)) (x : fullPV(ω))
    (hx : ∀ j, p (code j) → ΓCoeff(ω,j) x = 0)
    (j : ΓIndex(ω,(Set.univ : Set Xₛ))) (hj : p (code j)) : ΓCoeff(ω,j) (ρ g x) = 0 := by
  apply gamma_coeff_kernel_invariant ω ρ hρ
    (fun c ↦ ∃ i, i.val.1 = c ∧ p (code i)) x ?_ g j ⟨j,rfl,hj⟩
  intro i ⟨l,hli,hl⟩
  have hcode := (he l i).mpr hli
  exact hx i (hcode ▸ hl)

private theorem gamma_unitary_interpolation (τ : ℝ≥0ˣ →ₜ* J(S)) (hτ : RightInverse τ (m(S)))
    (χ : PontryaginDual J(S)) (hχ : ∀ u, χ (τ u) = 1) :
    let ω := χ.comp (⟨(m(S)).ker.subtype, continuous_subtype_val⟩ : J₁(S) →ₜ* J(S))
    Surjective (fun (x : fullPV(ω)) (j : ΓIndex(ω,(Set.univ : Set Xₛ))) ↦ ΓCoeff(ω,j) x) := by
  classical
  intro ω
  obtain ⟨ν,hν⟩ := gamma_positive_flow
  obtain ⟨ρ,hρ⟩ := gamma_full_action ω
  obtain ⟨code,he,hf⟩ := gamma_block_code ω
  let g : Multiplicative ℝ →* J(S) := τ.toMonoidHom.comp ν
  let R (t : ℝ) := (ρ (g (Multiplicative.ofAdd (-t)))).toLinearMap
  have hV := gamma_prefix_biorthogonal ω code hf
  have hinv : ∀ t x, R t (R (-t) x) = x := by
    intro t x
    exact real_action_inverse _ (ρ.comp g) t x
  have hF := gamma_range_frechet F S ω
  apply surjective_of_translated_coefficients (fullPV(ω)) (ΓIndex(ω,(Set.univ : Set Xₛ))) hF
    (fun j ↦ ΓCoeff(ω,j)) code hf hV R hinv ?_ ?_ ?_
  · intro p t x hx j hj
    exact gamma_coded_kernel ω ρ hρ code he p (g (Multiplicative.ofAdd (-t))) x hx j hj
  · intro q hq
    apply gamma_action_bound χ (fun t ↦ g (Multiplicative.ofAdd (-t))) ?_ ?_ ρ hρ q hq
    · intro t
      change (((m(S) (τ (ν (Multiplicative.ofAdd (-t))))).val : ℝ)) = _
      rw [hτ,hν]
    · intro t
      exact hχ _
  · intro a
    let weight (j : ΓIndex(ω,(Set.univ : Set Xₛ))) :=
      Real.log ‖j.val.1 (τ (Units.mk0 2 two_ne_zero))‖ / Real.log 2
    have hbad : Set.Finite {j : ΓIndex(ω,(Set.univ : Set Xₛ)) | a ≤ weight j} :=
      gamma_finite_indices_above ω τ hτ a
    let K := hbad.toFinset.sup code + 1
    refine ⟨K,fun j hj y ↦ ?_⟩
    have hweight : weight j < a := by
      by_contra h
      have hmem : j ∈ hbad.toFinset := hbad.mem_toFinset.mpr (le_of_not_gt h)
      have hb : code j ≤ hbad.toFinset.sup code := Finset.le_sup hmem
      dsimp [K] at hj
      omega
    have hk : j.val.2 ≤ sLocalRhoPoleOrder j.val.1 := by
      rw [sLocalRhoPoleOrder_eq_card_polePlaces]
      exact j.property.2.2.2.trans (Nat.le_add_right _ _)
    have h := gamma_coefficient_decay ω τ hτ ν hν ρ hρ j.val.1 j.property.1 j.val.2 hk a hweight y
    change Tendsto (fun t : ℝ ↦ Real.exp (-a*t) *
      ‖sLocalThetaPrincipalPartCoeff ω j.val.1 j.property.1 j.val.2
        (ρ (τ (ν (Multiplicative.ofAdd (-(-t))))) y).val‖) atTop (𝓝 0)
    simpa only [neg_neg] using h

end GammaInterpolationHelpers

/-- Paper: Theorem 7.3.4.1(4), p. 365.
Every array of archimedean principal parts on the component is realized by one
class in the full finite principal-value range.
Deviation: States explicitly the interpolation needed for the canonical product model. -/
theorem sLocalGamma_all_coeff_surjective (ω : PontryaginDual J₁(S)) :
    Function.Surjective (fun (x : fullPV(ω)) (j : ΓIndex(ω, (Set.univ : Set Xₛ))) ↦
      ΓCoeff(ω, j) x) := by
  obtain ⟨τ,hτ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨χ,⟨hω,hχ⟩,_⟩ := existsUnique_sLocalNormSectionCharacter τ hτ ω
  subst ω
  exact gamma_unitary_interpolation τ hτ χ hχ



/-- A surjective continuous linear map from a Fréchet space onto a countable product of
complex lines is open. -/
private theorem sLocalGammaOrbitalQuotient_coeff_isOpenMap {Q ι : Type*} [AddCommGroup Q]
    [Module ℂ Q] [TopologicalSpace Q] [IsTopologicalAddGroup Q] [ContinuousSMul ℂ Q]
    [Countable ι] (hQ : IsFrechetTVS Q) (L : Q →L[ℂ] (ι → ℂ))
    (hL : Function.Surjective L) : IsOpenMap L := by
  obtain ⟨_, _, hmet, hcomplete⟩ := hQ
  let : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
  have : IsUniformAddGroup Q := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace Q := hcomplete
  have := hmet
  refine isOpenMap_of_not_isMeagre_range L ?_
  rw [hL.range_eq]
  exact not_isMeagre_of_isOpen isOpen_univ Set.univ_nonempty

/-- The archimedean Laurent coefficients identify the archimedean polar quotient with the
product of complex lines indexed by centers and orders. -/
private theorem sLocalGammaOrbitalQuotient_coeff_equiv (ω : PontryaginDual J₁(S)) :
    ∃ Ψ : (fullPV(ω) ⧸ Γker(ω)) ≃L[ℂ] (ΓIndex(ω, (Set.univ : Set Xₛ)) → ℂ),
      ∀ (x : fullPV(ω)) (j : ΓIndex(ω, (Set.univ : Set Xₛ))),
        Ψ ((Γker(ω)).mkQ x) j = ΓCoeff(ω, j) x := by
  have := sLocalGammaOrbitalQuotient_coeff_countable ω
  let Φ : fullPV(ω) →L[ℂ] (ΓIndex(ω, (Set.univ : Set Xₛ)) → ℂ) :=
    ContinuousLinearMap.pi fun j ↦ ΓCoeff(ω, j)
  have hker : Γker(ω) ≤ LinearMap.ker Φ.toLinearMap := fun x hx ↦
    funext fun j ↦ (sLocalGammaOrbitalQuotient_coeff_ker ω x).mp hx j
  let L := (Γker(ω)).liftQ Φ.toLinearMap hker
  have hcont : Continuous L :=
    (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr Φ.continuous
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot]
    refine Submodule.ker_liftQ_eq_bot _ _ _ fun x hx ↦ ?_
    exact (sLocalGammaOrbitalQuotient_coeff_ker ω x).mpr fun j ↦ congrFun hx j
  have hsurj : Function.Surjective L := fun v ↦ by
    obtain ⟨x, hx⟩ := sLocalGamma_all_coeff_surjective ω v
    exact ⟨(Γker(ω)).mkQ x, hx⟩
  let e := LinearEquiv.ofBijective L ⟨hinj, hsurj⟩
  have hopen : IsOpenMap L :=
    sLocalGammaOrbitalQuotient_coeff_isOpenMap (sLocalGammaOrbitalQuotient_frechet ω)
      ⟨L, hcont⟩ hsurj
  let h := e.toEquiv.toHomeomorphOfContinuousOpen hcont hopen
  exact ⟨{ e with continuous_toFun := hcont, continuous_invFun := h.symm.continuous },
    fun x j ↦ rfl⟩

/-- If a product of lines is identified with a quotient by coefficient functionals, each of
which already vanishes on one of a family of larger subspaces, then the maps to the quotients by
that family induce the topology of the quotient. -/
private theorem sLocalGammaOrbitalQuotient_projectiveTopology_inducing {E ι κ : Type*}
    {_ : AddCommGroup E} {_ : Module ℂ E} {_ : TopologicalSpace E}
    (P : Submodule ℂ E) (stage : κ → Submodule ℂ E) (hle : ∀ N, P ≤ stage N)
    (φ : ι → StrongDual ℂ E) (Ψ : E ⧸ P → ι → ℂ) (hΨi : IsInducing Ψ)
    (hΨ : ∀ (x : E) (j : ι), Ψ (P.mkQ x) j = φ j x)
    (hN : ∀ j, ∃ N, ∀ x ∈ stage N, φ j x = 0) :
    IsInducing (fun (x : E ⧸ P) (N : κ) ↦ P.mapQ (stage N) LinearMap.id (hle N) x) := by
  let ℓ (j : ι) : (E ⧸ stage (hN j).choose) →ₗ[ℂ] ℂ :=
    (stage (hN j).choose).liftQ (φ j).toLinearMap fun x hx ↦ (hN j).choose_spec x hx
  have hℓ (j : ι) : Continuous (ℓ j) :=
    (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr (φ j).continuous
  let H : ((N : κ) → E ⧸ stage N) → (ι → ℂ) := fun y j ↦ ℓ j (y (hN j).choose)
  have hH : Continuous H := continuous_pi fun j ↦ (hℓ j).comp (continuous_apply _)
  have hF : Continuous (fun (x : E ⧸ P) (N : κ) ↦ P.mapQ (stage N) LinearMap.id (hle N) x) :=
    continuous_pi fun N ↦ (QuotientAddGroup.isQuotientMap_mk P.toAddSubgroup).continuous_iff.mpr
      (QuotientAddGroup.isQuotientMap_mk (stage N).toAddSubgroup).continuous
  have hcomp : H ∘ (fun (x : E ⧸ P) (N : κ) ↦ P.mapQ (stage N) LinearMap.id (hle N) x) =
      fun x ↦ Ψ x := by
    funext x j
    obtain ⟨x, rfl⟩ := P.mkQ_surjective x
    exact (hΨ x j).symm
  refine IsInducing.of_comp hF hH ?_
  rw [hcomp]
  exact hΨi

/-- Each archimedean Laurent coefficient vanishes on some stage of the filtration. -/
private theorem sLocalGammaOrbitalQuotient_projectiveTopology_cutoff (ω : PontryaginDual J₁(S))
    (j : ΓIndex(ω, (Set.univ : Set Xₛ))) : ∃ N : depths,
      ∀ x ∈ sLocalGammaFiltration (F := F) (S := S) ω N, ΓCoeff(ω, j) x = 0 := by
  obtain ⟨N, hN⟩ := sLocalGammaFiltration_iInf_mem_cutoff ω j.val.1 j.property.1
    (Finset.card_pos.mp (j.property.2.2.1.trans_le j.property.2.2.2))
  exact ⟨N, fun x hx ↦
    (Submodule.mem_iInf _).mp hx ⟨j.val, j.property.1, hN, j.property.2.2⟩⟩

/-- The statement of `sLocalGammaOrbitalQuotient_projectiveTopology` with its abbreviations
expanded. -/
private theorem sLocalGammaOrbitalQuotient_projectiveTopology_aux (ω : PontryaginDual J₁(S)) :
    ∃ qN : (N : depths) → (fullPV(ω) ⧸ Γker(ω)) →ₗ[ℂ]
        (fullPV(ω) ⧸ sLocalGammaFiltration (F := F) (S := S) ω N),
      (∀ N (x : fullPV(ω)), qN N ((Γker(ω)).mkQ x) = (sLocalGammaFiltration ω N).mkQ x) ∧
      IsInducing (fun (x : fullPV(ω) ⧸ Γker(ω)) (N : depths) ↦ qN N x) := by
  have hle (N : depths) : Γker(ω) ≤ sLocalGammaFiltration (F := F) (S := S) ω N := by
    rw [← sLocalGammaFiltration_iInf]
    exact iInf_le _ N
  have h := sLocalGammaOrbitalQuotient_coeff_equiv ω
  have k := sLocalGammaOrbitalQuotient_projectiveTopology_inducing (Γker(ω))
      (sLocalGammaFiltration (F := F) (S := S) ω) hle (fun j ↦ ΓCoeff(ω, j)) h.choose
      h.choose.toHomeomorph.isInducing (fun x j ↦ by
        have := h.choose_spec x j
        rw [this])
      (fun j ↦ by
        obtain ⟨N, hN⟩ := sLocalGammaOrbitalQuotient_projectiveTopology_cutoff ω j
        refine ⟨N, fun x hx ↦ ?_⟩
        have := hN x hx
        rw [this])
  exact ⟨fun N ↦ (Γker(ω)).mapQ (sLocalGammaFiltration (F := F) (S := S) ω N) LinearMap.id (hle N),
    fun N x ↦ rfl, k⟩

/-- Paper: Theorem 7.3.4.1(4), p. 365.
The quotient topology is induced by the family of canonical finite-cutoff quotient maps. -/
theorem sLocalGammaOrbitalQuotient_projectiveTopology (ω : PontryaginDual J₁(S)) :
    let E := ↥(fullPV(ω))
    let P := Γker(ω)
    let stage := sLocalGammaFiltration (F := F) (S := S) ω
    ∃ qN : (N : depths) → (E ⧸ P) →ₗ[ℂ] (E ⧸ stage N),
      (∀ N (x : E), qN N (P.mkQ x) = (stage N).mkQ x) ∧
      IsInducing (fun (x : E ⧸ P) (N : depths) ↦ qN N x) := by
  exact sLocalGammaOrbitalQuotient_projectiveTopology_aux ω

/-- Paper: Theorem 7.3.4.1(4), p. 365.
The quotient is topologically linearly isomorphic to the product of complex
lines indexed by cutoff tuples. -/
theorem sLocalGammaOrbitalQuotient_product (ω : PontryaginDual J₁(S)) :
    let E := ↥(fullPV(ω))
    let P := Γker(ω)
    Nonempty ((E ⧸ P) ≃L[ℂ] (depths → ℂ)) := by
  intro E P
  obtain ⟨Ψ, -⟩ := sLocalGammaOrbitalQuotient_coeff_equiv ω
  have := sLocalGammaOrbitalQuotient_coeff_countable ω
  have := sLocalGammaOrbitalQuotient_coeff_infinite ω
  let := Encodable.ofCountable (ΓIndex(ω, (Set.univ : Set Xₛ)))
  let := Denumerable.ofEncodableOfInfinite (ΓIndex(ω, (Set.univ : Set Xₛ)))
  let := Encodable.ofCountable depths
  let := Denumerable.ofEncodableOfInfinite depths
  let e : ΓIndex(ω, (Set.univ : Set Xₛ)) ≃ depths :=
    (Denumerable.eqv _).trans (Denumerable.eqv depths).symm
  exact ⟨Ψ.trans (ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : depths ↦ ℂ) e)⟩

/-- The strong dual of a space identified with a countably infinite product of complex lines is
the direct sum of complex lines over the same index with its finest locally convex topology. The
product is identified with formal power series, whose strong dual is the space of polynomials. -/
private theorem sLocalGammaOrbitalQuotient_dual_directSum_of_equiv {Q ι : Type*}
    [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q]
    (Ψ : Q ≃L[ℂ] (ι → ℂ)) (σ : ℕ ≃ ι) :
    Nonempty (StrongDual ℂ Q ≃L[ℂ] FinestLocallyConvex (ι →₀ ℂ)) := by
  obtain ⟨t, _⟩ := realSchwartzTaylor_equiv
  obtain ⟨p, _⟩ := realDiracDerivatives_polynomialEquiv
  let : TopologicalSpace (PowerSeries ℂ) := inferInstanceAs (TopologicalSpace ((Unit →₀ ℕ) → ℂ))
  let idx := (Finsupp.uniqueLinearEquiv ℕ ℕ ()).symm.toEquiv
  let series := ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Unit →₀ ℕ ↦ ℂ) idx
  let q : Q ≃L[ℂ] (ℕ → ℂ) :=
    Ψ.trans (ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : ℕ ↦ ℂ) σ.symm)
  let e := (q.trans series).trans t.symm
  let d : FinestLocallyConvex (Polynomial ℂ) ≃L[ℂ] StrongDual ℂ Q :=
    p.trans (e.symm.arrowCongr (ContinuousLinearEquiv.refl ℂ ℂ))
  let l : FinestLocallyConvex (Polynomial ℂ) ≃ₗ[ℂ] FinestLocallyConvex (ι →₀ ℂ) :=
    (AddMonoidAlgebra.coeffLinearEquiv ℂ).trans (Finsupp.domLCongr σ)
  let := finestLocallyConvex_t2 (Polynomial ℂ)
  let := finestLocallyConvex_t2 (ι →₀ ℂ)
  have h := continuous_of_finestLocallyConvex (Polynomial ℂ) l.toLinearMap
  have h' := continuous_of_finestLocallyConvex (ι →₀ ℂ) l.symm.toLinearMap
  exact ⟨d.symm.trans ⟨l, h, h'⟩⟩

/-- Paper: Theorem 7.3.4.1(4), p. 365.
The strong dual of the quotient is topologically linearly isomorphic to the
direct sum of complex lines with its finest locally convex topology.
The quotient dual represents the annihilator via pullback along the quotient map. -/
theorem sLocalGammaOrbitalQuotient_dual_directSum (ω : PontryaginDual J₁(S)) :
    let E := ↥(fullPV(ω))
    let P := Γker(ω)
    Nonempty (StrongDual ℂ (E ⧸ P) ≃L[ℂ] FinestLocallyConvex (depths →₀ ℂ)) := by
  intro E P
  obtain ⟨Ψ⟩ := sLocalGammaOrbitalQuotient_product ω
  let := Encodable.ofCountable depths
  let := Denumerable.ofEncodableOfInfinite depths
  exact sLocalGammaOrbitalQuotient_dual_directSum_of_equiv Ψ (Denumerable.eqv depths).symm

/-- Paper: Theorem 7.3.4.1(5), pp. 365–366.
The set of archimedean centers with their admissible Laurent orders admits an enumeration. -/
theorem sLocalGammaIndex_enumerable (ω : PontryaginDual J₁(S)) :
    Nonempty (ℕ ≃ ΓIndex(ω, (Set.univ : Set Xₛ))) := by
  have := sLocalGammaOrbitalQuotient_coeff_countable ω
  have := sLocalGammaOrbitalQuotient_coeff_infinite ω
  let := Encodable.ofCountable (ΓIndex(ω, (Set.univ : Set Xₛ)))
  let := Denumerable.ofEncodableOfInfinite (ΓIndex(ω, (Set.univ : Set Xₛ)))
  exact ⟨(Denumerable.eqv _).symm⟩

/-- A continuous linear functional on a product of complex lines vanishes on every vector
whose coordinates vanish on some finite set of indices. -/
private theorem sLocalGammaOrbitalQuotient_dual_basis_finite {ι : Type*}
    (L : (ι → ℂ) →L[ℂ] ℂ) : ∃ T : Finset ι, ∀ y : ι → ℂ, (∀ i ∈ T, y i = 0) → L y = 0 := by
  have hU : L ⁻¹' Metric.ball 0 1 ∈ 𝓝 (0 : ι → ℂ) :=
    L.continuous.continuousAt.preimage_mem_nhds (by
      rw [map_zero]
      exact Metric.ball_mem_nhds 0 one_pos)
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨T, t, ht, hsub⟩ := hU
  refine ⟨T, fun y hy ↦ ?_⟩
  by_contra hne
  have h2 : L ((2 / L y) • y) = 2 := by
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne]
  have hmem : (2 / L y) • y ∈ Set.pi (↑T) t := fun i hi ↦ by
    rw [Pi.smul_apply, hy i hi, smul_zero]
    exact mem_of_mem_nhds (ht i)
  have h1 := hsub hmem
  rw [Set.mem_preimage, h2, Metric.mem_ball, dist_zero_right] at h1
  norm_num at h1

/-- On a space identified with a product of complex lines indexed by an enumerated set, the
coordinate functionals form a Schauder basis of the strong dual, with evaluation at the
dual vectors as coefficient functionals. -/
private theorem sLocalGammaOrbitalQuotient_dual_basis_pi {Q ι : Type*} [AddCommGroup Q]
    [Module ℂ Q] [TopologicalSpace Q] [IsTopologicalAddGroup Q] [ContinuousSMul ℂ Q]
    [DecidableEq ι] (Ψ : Q ≃L[ℂ] (ι → ℂ)) (σ : ℕ ≃ ι) :
    IsSchauderBasis
      (fun n ↦ (ContinuousLinearMap.proj (σ n) : (ι → ℂ) →L[ℂ] ℂ).comp (Ψ : Q →L[ℂ] (ι → ℂ)))
      (fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (Ψ.symm (Pi.single (σ n) 1))) := by
  refine ⟨fun m n ↦ ?_, fun ℓ ↦ ?_⟩
  · change Ψ (Ψ.symm (Pi.single (σ m) 1)) (σ n) = if m = n then 1 else 0
    rw [Ψ.apply_symm_apply, Pi.single_apply]
    by_cases hmn : m = n
    · subst hmn
      simp
    · have hne : σ n ≠ σ m := fun e ↦ hmn (σ.injective e).symm
      simp [hmn, hne]
  · obtain ⟨T, hT⟩ := sLocalGammaOrbitalQuotient_dual_basis_finite
      (ℓ.comp (Ψ.symm : (ι → ℂ) →L[ℂ] Q))
    have hzero (m : ℕ) (hm : σ m ∉ T) : ℓ (Ψ.symm (Pi.single (σ m) 1)) = 0 :=
      hT _ fun i hi ↦ by
        simp [show i ≠ σ m from fun e ↦ hm (e ▸ hi)]
    have hrep : ℓ = ∑ i ∈ T, ℓ (Ψ.symm (Pi.single i 1)) •
        (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).comp (Ψ : Q →L[ℂ] (ι → ℂ)) := by
      ext q
      have hy := hT (Ψ q - ∑ i ∈ T, Ψ q i • Pi.single i (1 : ℂ)) fun i hi ↦ by
        simp [Finset.sum_apply, Pi.single_apply, hi]
      simp only [ContinuousLinearMap.comp_apply, map_sub, map_sum, map_smul,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
        sub_eq_zero] at hy
      rw [hy]
      simp [mul_comm]
    let K := (T.image σ.symm).sup id + 1
    unfold HasSum
    rw [SummationFilter.conditional_filter_eq_map_range, Filter.tendsto_map'_iff]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop K] with k hk
    have hsub : T.map σ.symm.toEmbedding ⊆ Finset.range k := by
      intro m hm
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hm
      have hle : σ.symm i ≤ (T.image σ.symm).sup id :=
        Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hi)
      change σ.symm i ∈ Finset.range k
      exact Finset.mem_range.mpr (by omega)
    symm
    change ∑ m ∈ Finset.range k, ℓ (Ψ.symm (Pi.single (σ m) 1)) •
        (ContinuousLinearMap.proj (σ m) : (ι → ℂ) →L[ℂ] ℂ).comp (Ψ : Q →L[ℂ] (ι → ℂ)) = ℓ
    rw [← Finset.sum_subset hsub fun m _ hm ↦ ?_, Finset.sum_map]
    · conv_rhs => rw [hrep]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp
    · have hσ : σ m ∉ T := fun h ↦ hm (Finset.mem_map.mpr ⟨σ m, h, by simp⟩)
      rw [hzero m hσ, zero_smul]

/-- On a quotient identified with a product of complex lines through coefficient
functionals, the descended coefficients in any enumeration form a Schauder basis of the
strong dual. -/
private theorem sLocalGammaOrbitalQuotient_dual_basis_quot {E ι : Type*} {_ : AddCommGroup E}
    {_ : Module ℂ E} {_ : TopologicalSpace E} (P : Submodule ℂ E)
    [IsTopologicalAddGroup (E ⧸ P)] [ContinuousSMul ℂ (E ⧸ P)] [DecidableEq ι]
    (φ : ι → StrongDual ℂ E) (Ψ : (E ⧸ P) ≃L[ℂ] (ι → ℂ))
    (hΨ : ∀ (x : E) (j : ι), Ψ (P.mkQ x) j = φ j x) (σ : ℕ ≃ ι) :
    ∃ (a : ℕ → StrongDual ℂ (E ⧸ P)) (d : ℕ → StrongDual ℂ (StrongDual ℂ (E ⧸ P))),
      (∀ n (x : E), a n (P.mkQ x) = φ (σ n) x) ∧ IsSchauderBasis a d :=
  ⟨_, _, fun n x ↦ hΨ x (σ n), sLocalGammaOrbitalQuotient_dual_basis_pi Ψ σ⟩

/-- The statement of `sLocalGammaOrbitalQuotient_dual_basis` with its abbreviations
expanded. -/
private theorem sLocalGammaOrbitalQuotient_dual_basis_aux (ω : PontryaginDual J₁(S))
    (σ : ℕ ≃ ΓIndex(ω, (Set.univ : Set Xₛ))) :
    ∃ (a : ℕ → StrongDual ℂ (fullPV(ω) ⧸ Γker(ω)))
      (d : ℕ → StrongDual ℂ (StrongDual ℂ (fullPV(ω) ⧸ Γker(ω)))),
      (∀ n (x : fullPV(ω)), a n ((Γker(ω)).mkQ x) = ΓCoeff(ω, (σ n)) x) ∧
      IsSchauderBasis a d := by
  classical
  have h := sLocalGammaOrbitalQuotient_coeff_equiv ω
  exact sLocalGammaOrbitalQuotient_dual_basis_quot (ι := ΓIndex(ω, (Set.univ : Set Xₛ)))
    (Γker(ω)) (fun j ↦ ΓCoeff(ω, j)) h.choose (fun x j ↦ by
      have := h.choose_spec x j
      rw [this]) σ

/-- Paper: Theorem 7.3.4.1(5), p. 365.
In every enumeration, the archimedean Laurent coefficients descend to a
Schauder basis of the strong dual of the archimedean polar quotient.
Deviation: Uses the coefficient of exponent −k for order k in (7.3.4.8). -/
theorem sLocalGammaOrbitalQuotient_dual_basis (ω : PontryaginDual J₁(S))
    (σ : ℕ ≃ ΓIndex(ω, (Set.univ : Set Xₛ))) :
    let E := ↥(fullPV(ω))
    let P := Γker(ω)
    ∃ (a : ℕ → StrongDual ℂ (E ⧸ P)) (d : ℕ → StrongDual ℂ (StrongDual ℂ (E ⧸ P))),
      (∀ n (x : E), a n (P.mkQ x) = ΓCoeff(ω, (σ n)) x) ∧
      IsSchauderBasis a d := by
  exact sLocalGammaOrbitalQuotient_dual_basis_aux ω σ

end ArchimedeanPoles

end RiemannMasullo
