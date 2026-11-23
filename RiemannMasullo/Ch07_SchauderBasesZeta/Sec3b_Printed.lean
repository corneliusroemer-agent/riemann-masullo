module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3b

/-! # False printed PW-level claims in §7.3.2–7.3.3 -/

@[expose] public noncomputable section

open Classical Filter Function IsDedekindDomain NumberField Set Topology
open scoped BigOperators NNReal NumberField.AdeleRing TensorProduct

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 600000
set_option Elab.async false

local notation "V(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "m(" F ", " T ")" => sIdeleQuotientNorm F T
local notation "J₁(" F ", " T ")" => (m(F, T)).ker
local notation "Θ(" F ", " T ", " χ ")" => SLocalHomogeneousThetaSpace F T χ
local notation "q(" F ", " T ", " χ ")" =>
  (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F T χ)).mkQ
local notation "size(" P ")" => (∏ v ∈ P, (v.asIdeal.absNorm : ℝ))
local notation "count(" F ", " S ")" => (Fintype.card (InfinitePlace F) + Finset.card S)
local notation "unitTests(" F ", " S ", " T ", " h ", " K ")" =>
  (sLocalPWTests h K).map (sAdelePrincipalValue F (Finset.sdiff_subset : T \ S ⊆ T))
local notation "unitLevel(" F ", " S ", " T ", " h ", " K ", " D ", " χ ")" =>
  ((unitTests(F, S, T, h, K) ⊓ D).map (q(F, T, χ))).topologicalClosure
local notation "zeroMoments(" F ", " T ")" => sAdelePolarSubspace F T

local notation "B(" F ", " S ")" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "unitPV(" F ", " S ", " T ")" =>
  sAdelePrincipalValue F (Finset.sdiff_subset : T \ S ⊆ T)

/-- Paper: Equations (7.3.2.2) and (7.3.2.13), pp. 351, 355.
On a test at either level the cited transition is asserted to insert unit indicators. -/
def Printed.sLocalPWTransition_eq_units : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S S₀ T : Finset (V(F))),
    T = S ∪ S₀ → Disjoint S S₀ → IsSaturatedPlaceSet (F := F) S₀ →
    Subsingleton (CommRing.Pic ((S : Set (V(F))).integer F)) →
    ∀ (hST : S ⊆ T) (X : ℝ), 0 < X →
      ∀ K ∈ ({sLocalPWBox S X, sLocalPWProductRegion S X} : Set (Set (SAdeleRing F S))),
        ∀ f : B(F, S), HasCompactSupport (sAdeleSchwartzFourier f).val →
          tsupport (sAdeleSchwartzFourier f).val ⊆ Multiplicative.toAdd ⁻¹' K →
          sAdeleSchwartzTransition F hST f = unitPV(F, S, T) (sAdeleSchwartzTransition F hST f)

open MeasureTheory in
/-- The local principal value of a test vanishes at zero. -/
private theorem sec3bP_localPV_zero {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (g : SchwartzBruhat (Multiplicative (v.adicCompletion F))) :
    finitePlacePrincipalValue v g (Multiplicative.ofAdd 0) = 0 := by
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let π' := Units.mk0 (π : v.adicCompletion F) hπ.ne_zero
  rw [finitePlacePrincipalValue_spec v π' hπ g]
  have hm := (finitePlacePrincipalValue_integrable v π' g (Multiplicative.ofAdd 0)).1
  unfold finitePlacePrincipalValueFun
  simp only [toAdd_ofAdd, mul_zero]
  rw [setIntegral_const, Complex.real_smul, ← mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hm.ne'), one_mul, sub_self]

/-- The S-local principal value vanishes at every point whose coordinate at a selected
place is zero. -/
private theorem sec3bP_sPV_zero {F : Type*} [Field F] [NumberField F]
    {S S₀ : Finset (HeightOneSpectrum (𝓞 F))} (h₀ : S₀ ⊆ S) {p : HeightOneSpectrum (𝓞 F)}
    (hp : p ∈ S₀) (x : SAdeleRing F S) (hx : x.2 ⟨p, h₀ hp⟩ = 0)
    (h : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    sAdelePrincipalValue F h₀ h (Multiplicative.ofAdd x) = 0 := by
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  have he := (sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec
  let A := SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))
  let P := ⨂[ℂ] w : S, SchwartzBruhat (Multiplicative (w.val.adicCompletion F))
  let evL : SchwartzBruhat (Multiplicative (SAdeleRing F S)) →ₗ[ℂ] ℂ :=
    { toFun := fun k ↦ k (Multiplicative.ofAdd x)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let Φ : A ⊗[ℂ] FinestLocallyConvex P →ₗ[ℂ] ℂ :=
    (evL.comp (sAdelePrincipalValue F h₀)).comp e.toLinearMap
  have hpure (a : A) (g : ∀ w : S, SchwartzBruhat (Multiplicative (w.val.adicCompletion F))) :
      Φ (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w)) = 0 := by
    change sAdelePrincipalValue F h₀ (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) (Multiplicative.ofAdd x) = 0
    rw [sAdelePrincipalValue_tmul h₀ a g, he]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ⟨p, h₀ hp⟩) ?_)
    simp only [hp, if_true, hx]
    exact sec3bP_localPV_zero p (g ⟨p, h₀ hp⟩)
  have hΦ (t : A ⊗[ℂ] FinestLocallyConvex P) : Φ t = 0 := by
    induction t using TensorProduct.induction_on with
    | zero => exact map_zero Φ
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
    | tmul a w =>
      let Ψ : P →ₗ[ℂ] ℂ := Φ.comp (TensorProduct.mk ℂ A (FinestLocallyConvex P) a)
      change Ψ w = 0
      induction w using PiTensorProduct.induction_on with
      | smul_tprod r g =>
        rw [map_smul, smul_eq_mul]
        exact mul_eq_zero_of_right _ (hpure a g)
      | add x y hx hy => rw [map_add, hx, hy, add_zero]
  have := hΦ (e.symm h)
  change sAdelePrincipalValue F h₀ (e (e.symm h)) (Multiplicative.ofAdd x) = 0 at this
  rwa [e.apply_symm_apply] at this

/-- Over the rationals with no finite places the S-integers have trivial Picard group. -/
private theorem sec3bP_pic :
    Subsingleton (CommRing.Pic (((∅ : Finset Vℚ) : Set Vℚ).integer ℚ)) := by
  rw [Finset.coe_empty, integer_empty]
  let e := (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)).toRingEquiv
  let i := Rat.ringOfIntegersEquiv.symm.trans e.symm
  let := IsPrincipalIdealRing.of_surjective i i.surjective
  infer_instance

/-- Over the rationals a single finite place is a saturated set. -/
private theorem sec3bP_saturated (p : Vℚ) : IsSaturatedPlaceSet (F := ℚ) {p} := by
  intro v w hv hw
  rw [Finset.mem_singleton] at hv ⊢
  subst hv
  apply HeightOneSpectrum.ext
  have h := congrArg HeightOneSpectrum.asIdeal hw
  change Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 ℚ)) w.asIdeal =
    Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 ℚ)) v.asIdeal at h
  rwa [Algebra.algebraMap_self, Ideal.comap_id, Ideal.comap_id] at h

/-- Paper: Equations (7.3.2.2) and (7.3.2.13), pp. 351, 355.
Over the rationals add one prime and choose an inverse Fourier bump with positive
integral. At the zero tuple integer insertion gives its nonzero value at zero,
while unit insertion gives zero. -/
theorem Printed.sLocalPWTransition_eq_units_false : ¬ Printed.sLocalPWTransition_eq_units := by
  intro h
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 ℚ)
  let p : Vℚ := ⟨m, hm.isPrime, NeZero.ne m⟩
  let S : Finset Vℚ := ∅
  let T : Finset Vℚ := {p}
  let A := SAdeleRing ℚ S
  let G := Multiplicative A
  let : T2Space G := inferInstanceAs (T2Space
    (((w : InfinitePlace ℚ) → w.Completion) × ((v : S) → v.val.adicCompletion ℚ)))
  let : LocallyCompactSpace G := inferInstanceAs (LocallyCompactSpace
    (((w : InfinitePlace ℚ) → w.Completion) × ((v : S) → v.val.adicCompletion ℚ)))
  -- A bump equal to one near zero, supported where every archimedean coordinate is small.
  let U : Set G := {x | ∀ w : InfinitePlace ℚ, ‖x.toAdd.1 w‖ < 1 / 2}
  have hU : IsOpen U := by
    simp only [U, setOf_forall]
    exact isOpen_iInter_of_finite fun w ↦ isOpen_lt
      ((continuous_apply w).comp (continuous_fst.comp continuous_toAdd)).norm continuous_const
  have h1U : (1 : G) ∈ U := fun w ↦ by
    change ‖(0 : A).1 w‖ < 1 / 2
    rw [show (0 : A).1 w = 0 from rfl, norm_zero]
    norm_num
  obtain ⟨g, hgc, hgs, hg1⟩ := schwartzBruhat_exists_local_unit hU h1U
  let f := sAdeleSchwartzFourier g
  have hFf (y : G) : sAdeleSchwartzFourier f y = g y⁻¹ := by
    have := sLocal_fourier_inversion g y.toAdd
    simpa [f] using this
  have hFf' : (sAdeleSchwartzFourier f).val = g.val ∘ (Homeomorph.inv G) := funext hFf
  have hcs : HasCompactSupport (sAdeleSchwartzFourier f).val := by
    rw [hFf']
    exact hgc.comp_homeomorph _
  have hts : tsupport (sAdeleSchwartzFourier f).val ⊆
      Multiplicative.toAdd ⁻¹' sLocalPWBox S 1 := by
    rw [hFf', tsupport_comp_eq_preimage]
    intro y hy
    refine ⟨fun w ↦ ?_, fun v ↦ absurd v.property (Finset.notMem_empty v.val)⟩
    have hw : ‖(Multiplicative.toAdd y⁻¹).1 w‖ < 1 / 2 := hgs hy w
    rw [show (Multiplicative.toAdd y⁻¹).1 w = -((Multiplicative.toAdd y).1 w) from rfl,
      norm_neg] at hw
    exact pow_le_one₀ (norm_nonneg _) (by linarith)
  -- The test is not identically zero, since its Fourier transform is one at the origin.
  obtain ⟨y, hy⟩ : ∃ y : A, f (Multiplicative.ofAdd y) ≠ 0 := by
    by_contra hall
    push Not at hall
    have h0 : sAdeleSchwartzFourier f 1 = 0 := by
      let : MeasurableSpace A := instMeasurableSpaceSAdeleRing ℚ S
      change tamagawaFourier _ _ (fun x ↦ f (Multiplicative.ofAdd x)) _ = 0
      simp [hall, tamagawaFourier]
    rw [hFf, inv_one, hg1.eq_of_nhds] at h0
    exact one_ne_zero h0
  -- Apply the printed identity at the point with the same archimedean part and zero at p.
  have hsub : S ⊆ T := Finset.empty_subset _
  have hpT : p ∈ T \ S := by simp [S, T]
  have hEq := h ℚ S T T (by simp [S, T]) (Finset.disjoint_empty_left _) (sec3bP_saturated p)
    sec3bP_pic hsub 1 one_pos (sLocalPWBox S 1) (by simp) f hcs hts
  let z : SAdeleRing ℚ T := (y.1, 0)
  have hval := congrArg (fun k : B(ℚ, T) ↦ k (Multiplicative.ofAdd z)) hEq
  simp only at hval
  rw [sec3bP_sPV_zero Finset.sdiff_subset hpT z rfl] at hval
  rw [sAdeleSchwartzTransition_apply, if_pos (fun w _ ↦ (w.val.adicCompletionIntegers ℚ).zero_mem)]
    at hval
  apply hy
  have hyz : (z.1, fun w : S ↦ z.2 ⟨w.val, hsub w.property⟩) = y :=
    Prod.ext rfl (funext fun w ↦ absurd w.property (Finset.notMem_empty w.val))
  rwa [hyz] at hval

/-- Paper: Definitions 7.3.2.1(1) and 7.3.2.3(1), pp. 351, 355.
Inside each printed test level the common kernel of the two evaluations has codimension two. -/
def Printed.sLocalPWTests_twoMoments : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S S₀ T : Finset (V(F))),
    T = S ∪ S₀ → Disjoint S S₀ → IsSaturatedPlaceSet (F := F) S₀ →
    Subsingleton (CommRing.Pic ((S : Set (V(F))).integer F)) →
    ∀ (hST : S ⊆ T) (X : ℝ), 0 < X →
      ∀ K ∈ ({sLocalPWBox S X, sLocalPWProductRegion S X} : Set (Set (SAdeleRing F S))),
        let E := unitTests(F, S, T, hST, K)
        Module.finrank ℂ (E ⧸ (zeroMoments(F, T)).comap E.subtype) = 2

/-- Paper: Definitions 7.3.2.1(1) and 7.3.2.3(1), pp. 351, 355.
For one added rational prime every inserted test vanishes at zero, so at most
one independent moment remains on the test space. -/
theorem Printed.sLocalPWTests_twoMoments_false : ¬ Printed.sLocalPWTests_twoMoments := by
  intro h
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 ℚ)
  let p : Vℚ := ⟨m, hm.isPrime, NeZero.ne m⟩
  let S : Finset Vℚ := ∅
  let T : Finset Vℚ := {p}
  have hsub : S ⊆ T := Finset.empty_subset _
  have hpT : p ∈ T \ S := by simp [S, T]
  let E := unitTests(ℚ, S, T, hsub, sLocalPWBox S 1)
  let Q := (zeroMoments(ℚ, T)).comap E.subtype
  have h2 : Module.finrank ℂ (E ⧸ Q) = 2 :=
    h ℚ S T T (by simp [S, T]) (Finset.disjoint_empty_left _) (sec3bP_saturated p)
      sec3bP_pic hsub 1 one_pos (sLocalPWBox S 1) (by simp)
  -- The Fourier transform at zero, restricted to the inserted tests.
  let M := (sAdelePolarValues_isLinear (F := ℚ) (S := T)).mk' _
  let L : E →ₗ[ℂ] ℂ := (LinearMap.snd ℂ ℂ ℂ).comp (M.comp E.subtype)
  -- Every inserted test is a unit principal value, so it vanishes at zero, and the
  -- zero-moment condition reduces to the kernel of the Fourier moment.
  have hker : LinearMap.ker L ≤ Q := by
    intro e he
    rw [Submodule.mem_comap, mem_sAdelePolarSubspace]
    refine ⟨?_, LinearMap.mem_ker.mp he⟩
    obtain ⟨t, -, hte⟩ := Submodule.mem_map.mp e.property
    rw [Submodule.subtype_apply, ← hte]
    exact sec3bP_sPV_zero Finset.sdiff_subset hpT 0 rfl t
  have hle : Module.finrank ℂ (E ⧸ LinearMap.ker L) ≤ 1 := by
    rw [L.quotKerEquivRange.finrank_eq]
    exact (Submodule.finrank_le _).trans (by simp)
  have : FiniteDimensional ℂ (E ⧸ LinearMap.ker L) :=
    L.quotKerEquivRange.symm.finiteDimensional
  let φ := Submodule.mapQ (LinearMap.ker L) Q LinearMap.id hker
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨e, rfl⟩ := Submodule.mkQ_surjective Q q
    exact ⟨Submodule.mkQ _ e, rfl⟩
  have hrange : Module.finrank ℂ (E ⧸ Q) ≤ Module.finrank ℂ (E ⧸ LinearMap.ker L) := by
    rw [← finrank_top ℂ (E ⧸ Q), ← LinearMap.range_eq_top.mpr hφ]
    exact LinearMap.finrank_range_le φ
  omega

/-- Paper: Proposition 7.3.2.2(1), p. 352, with Definition 7.3.2.1, p. 351.
The absolute levels formed with the printed unit factors exhaust the homogeneous
theta space sequentially, both for unrestricted and for zero-moment tests. Applying
principal value to the inserted integer indicators realizes the printed unit factors. -/
def Printed.sLocalAbsolutePW_seqDense : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S S₀ T : Finset (V(F))),
    T = S ∪ S₀ →
    Disjoint S S₀ → IsSaturatedPlaceSet (F := F) S₀ →
    Subsingleton (CommRing.Pic ((S : Set (V(F))).integer F)) →
    ∀ (ω : PontryaginDual (ideleClassNorm F).ker)
      (hu : NormOneCharacterUnramifiedOutside ω S),
      ∀ (hST : S ⊆ T) (χ : PontryaginDual J₁(F, T)),
        χ = sLocalNormOneCharacter (F := F) T ω (hu.mono hST) →
      ∀ (D : Submodule ℂ (SchwartzBruhat (Multiplicative (SAdeleRing F T)))),
        (D = ⊤ ∨ D = zeroMoments(F, T)) →
        ∀ x : Θ(F, T, χ), x ∈ D.map (q(F, T, χ)) →
          ∃ u : ℕ → Θ(F, T, χ),
            (∀ n, ∃ X > 0, u n ∈ unitLevel(F, S, T, hST, sLocalPWBox S X, D, χ)) ∧
            Tendsto u atTop (𝓝 x)

open MeasureTheory in
/-- A test in the kernel of global homogeneous theta for the trivial character vanishes at
zero: after the polar term the homogeneous theta function is small at small norm. -/
private theorem sec3bP_globalHom_zero {F : Type*} [Field F] [NumberField F]
    (f : SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F)))
    (hf : homogeneousAdelicTheta (1 : PontryaginDual (ideleClassNorm F).ker) f = 0) :
    f (Multiplicative.ofAdd 0) = 0 := by
  let : MeasurableSpace (IdeleClassGroup (𝓞 F) F) := borel _
  let : BorelSpace (IdeleClassGroup (𝓞 F) F) := ⟨rfl⟩
  let : CompactSpace (ideleClassNorm F).ker := (ideleClassGroup_finiteness F).2.1
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  obtain ⟨C, T, hC, hT, hsmall⟩ :=
    homogeneousAdelicTheta_decay_small (1 : PontryaginDual (ideleClassNorm F).ker) f 1
  set V := (normOneIdeleClassTamagawaMeasure F univ).toReal
  have hV : 0 < V := ENNReal.toReal_pos (isOpen_univ.measure_ne_zero _ univ_nonempty)
    isCompact_univ.measure_lt_top.ne
  set a := adeleSchwartzFourier f (Multiplicative.ofAdd 0)
  set b := f (Multiplicative.ofAdd 0)
  -- Every positive real below `T` is the norm of an idele class.
  have key (t : ℝ) (ht : 0 < t) (htT : t < T) : ‖V • (t⁻¹ • a - b)‖ ≤ C * t := by
    let u : ℝ≥0ˣ := Units.mk0 ⟨t, ht.le⟩ fun h0 ↦ ht.ne' (congrArg Subtype.val h0)
    let g : IdeleClassGroup (𝓞 F) F := QuotientGroup.mk (canonicalIdeleNormSection F u)
    have hg : ((ideleClassNorm F g : ℝ≥0) : ℝ) = t := by
      change ((ideleNorm F (canonicalIdeleNormSection F u) : ℝ≥0) : ℝ) = t
      rw [canonicalIdeleNormSection_rightInverse F u]
      rfl
    have h := hsmall g (by beta_reduce; rw [hg]; exact htT)
    beta_reduce at h
    simp only [homogeneousAdelicTheta_polarTerm, ite_true] at h
    rw [hf, hg, pow_one] at h
    rw [norm_smul, Real.norm_of_nonneg hV.le]
    simpa [V, a, b] using h
  have hlim0 : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0) :=
    (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
  -- Multiplying by `t` shows that the Fourier value vanishes.
  have ha : a = 0 := by
    have hb : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖a‖ ≤ t * ‖b‖ + C * t ^ 2 / V := by
      filter_upwards [Ioo_mem_nhdsGT hT] with t ht
      have h := key t ht.1 ht.2
      have he : a = (t / V) • (V • (t⁻¹ • a - b)) + t • b := by
        rw [smul_smul, div_mul_cancel₀ _ hV.ne', smul_sub, smul_smul,
          mul_inv_cancel₀ ht.1.ne', one_smul, sub_add_cancel]
      rw [he]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul (t / V), norm_smul t, Real.norm_of_nonneg (div_nonneg ht.1.le hV.le),
        Real.norm_of_nonneg ht.1.le]
      have h2 : t / V * ‖V • (t⁻¹ • a - b)‖ ≤ t / V * (C * t) :=
        mul_le_mul_of_nonneg_left h (div_nonneg ht.1.le hV.le)
      have h3 : t / V * (C * t) = C * t ^ 2 / V := by ring
      linarith
    have hl : Tendsto (fun t : ℝ ↦ t * ‖b‖ + C * t ^ 2 / V) (𝓝[>] 0) (𝓝 0) := by
      have := ((hlim0.mul_const ‖b‖).add ((hlim0.pow 2).const_mul C |>.div_const V))
      simpa using this
    exact norm_le_zero_iff.mp (ge_of_tendsto hl hb)
  have hb : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖b‖ ≤ C * t / V := by
    filter_upwards [Ioo_mem_nhdsGT hT] with t ht
    have h := key t ht.1 ht.2
    rw [ha, smul_zero, zero_sub, smul_neg, norm_neg, norm_smul, Real.norm_of_nonneg hV.le] at h
    rw [le_div_iff₀ hV]
    linarith
  have hl : Tendsto (fun t : ℝ ↦ C * t / V) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hlim0.const_mul C).div_const V
  exact norm_le_zero_iff.mp (ge_of_tendsto hl hb)

/-- Evaluation at zero descends to the homogeneous theta space at a stage `T` for an
unramified norm-one character, through the insertion into the global homogeneous space. -/
private theorem sec3bP_evalZero_ker {F : Type*} [Field F] [NumberField F]
    {T : Finset (V(F))} (hω : NormOneCharacterUnramifiedOutside
      (1 : PontryaginDual (ideleClassNorm F).ker) T)
    (f : B(F, T))
    (hf : f ∈ LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F T
      (sLocalNormOneCharacter T 1 hω))) :
    f (Multiplicative.ofAdd 0) = 0 := by
  have hg := sLocalHomogeneousThetaToGlobal_preserves_kernel (F := F) (S := T) hω hf
  rw [Submodule.mem_comap, LinearMap.mem_ker] at hg
  have h0 := sec3bP_globalHom_zero _ hg
  rw [sAdeleSchwartzToGlobal_apply, if_pos (fun w _ ↦ (w.adicCompletionIntegers F).zero_mem),
    map_zero] at h0
  exact h0

/-- Over the rationals with S = ∅ and one added prime, the unit levels for every family of
cutoff regions miss a class: evaluation at zero is continuous on the theta space, vanishes on
every inserted unit test, and is nonzero on some class. -/
private theorem sec3bP_seqDense_false (p : Vℚ) (hsub : (∅ : Finset Vℚ) ⊆ {p})
    (hu : NormOneCharacterUnramifiedOutside (1 : PontryaginDual (ideleClassNorm ℚ).ker) ∅)
    (K : ℝ → Set (SAdeleRing ℚ ∅)) :
    ¬ ∀ x : Θ(ℚ, {p}, sLocalNormOneCharacter {p} 1 (hu.mono hsub)),
      x ∈ (⊤ : Submodule ℂ (B(ℚ, {p}))).map (q(ℚ, {p}, sLocalNormOneCharacter {p} 1 (hu.mono hsub))) →
        ∃ u : ℕ → Θ(ℚ, {p}, sLocalNormOneCharacter {p} 1 (hu.mono hsub)),
          (∀ n, ∃ X > 0, u n ∈ unitLevel(ℚ, (∅ : Finset Vℚ), {p}, hsub, K X, ⊤,
            sLocalNormOneCharacter {p} 1 (hu.mono hsub))) ∧
          Tendsto u atTop (𝓝 x) := by
  intro h
  set χ := sLocalNormOneCharacter {p} 1 (hu.mono hsub) with hχ
  set Kθ := LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap ℚ ({p} : Finset Vℚ) χ) with hKθ
  have hpT : p ∈ ({p} : Finset Vℚ) \ (∅ : Finset Vℚ) := by simp
  -- Evaluation at zero as a continuous functional on tests and on the theta space.
  let ℓ : B(ℚ, ({p} : Finset Vℚ)) →L[ℂ] ℂ :=
    ⟨(LinearMap.fst ℂ ℂ ℂ).comp ((adelePolarValues (F := ℚ)).comp (sAdeleSchwartzToGlobal ℚ ({p} : Finset Vℚ))),
      continuous_fst.comp ((adelePolarValues_continuous (F := ℚ)).comp
        (sAdeleSchwartzToGlobal_isEmbedding ℚ ({p} : Finset Vℚ)).continuous)⟩
  have hℓ (f : B(ℚ, ({p} : Finset Vℚ))) : ℓ f = f (Multiplicative.ofAdd 0) := by
    change sAdeleSchwartzToGlobal ℚ ({p} : Finset Vℚ) f (Multiplicative.ofAdd 0) = _
    rw [sAdeleSchwartzToGlobal_apply, if_pos (fun w _ ↦ (w.adicCompletionIntegers ℚ).zero_mem),
      map_zero]
  have hker : Kθ ≤ LinearMap.ker (ℓ : B(ℚ, ({p} : Finset Vℚ)) →ₗ[ℂ] ℂ) := fun f hf ↦ by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hℓ]
    exact sec3bP_evalZero_ker (hu.mono hsub) f hf
  let L : Θ(ℚ, ({p} : Finset Vℚ), χ) →L[ℂ] ℂ := Kθ.liftQL ℓ hker
  have hL (f : B(ℚ, ({p} : Finset Vℚ))) : L (Kθ.mkQ f) = f (Multiplicative.ofAdd 0) := hℓ f
  -- The insertion of a test that is one near zero.
  let G := Multiplicative (SAdeleRing ℚ ∅)
  let : T2Space G := inferInstanceAs (T2Space
    (((w : InfinitePlace ℚ) → w.Completion) × ((v : (∅ : Finset Vℚ)) → v.val.adicCompletion ℚ)))
  let : LocallyCompactSpace G := inferInstanceAs (LocallyCompactSpace
    (((w : InfinitePlace ℚ) → w.Completion) × ((v : (∅ : Finset Vℚ)) → v.val.adicCompletion ℚ)))
  obtain ⟨g, -, -, hg⟩ := schwartzBruhat_exists_local_unit (G := G) isOpen_univ (mem_univ 1)
  let f₀ := sAdeleSchwartzTransition ℚ hsub g
  have hf₀0 : f₀ (Multiplicative.ofAdd 0) = 1 := by
    rw [sAdeleSchwartzTransition_apply,
      if_pos (fun w _ ↦ (w.val.adicCompletionIntegers ℚ).zero_mem)]
    have h0 : ((0 : SAdeleRing ℚ ({p} : Finset Vℚ)).1, fun w : (∅ : Finset Vℚ) ↦
        (0 : SAdeleRing ℚ ({p} : Finset Vℚ)).2 ⟨w.val, hsub w.property⟩) = (0 : SAdeleRing ℚ ∅) :=
      Prod.ext rfl (funext fun w ↦ absurd w.property (Finset.notMem_empty w.val))
    rw [h0]
    exact hg.eq_of_nhds
  obtain ⟨u, hun, hlim⟩ := h _ (Submodule.mem_map_of_mem (p := ⊤) (Submodule.mem_top (x := f₀)))
  have hE (t : B(ℚ, ({p} : Finset Vℚ))) :
      L (Kθ.mkQ (sAdelePrincipalValue ℚ (Finset.sdiff_subset : ({p} : Finset Vℚ) \ (∅ : Finset Vℚ) ⊆ ({p} : Finset Vℚ)) t)) = 0 :=
    (hL _).trans (sec3bP_sPV_zero Finset.sdiff_subset hpT 0 rfl t)
  have hzero (n : ℕ) : L (u n) = 0 := by
    obtain ⟨X, -, hX⟩ := hun n
    have hX' := (Submodule.topologicalClosure_coe _).subst (motive := fun A ↦ u n ∈ A) hX
    refine closure_minimal (t := {x | L x = 0}) ?_ (isClosed_eq L.continuous continuous_const) hX'
    intro y hy
    obtain ⟨e, he, rfl⟩ := Submodule.mem_map.mp hy
    obtain ⟨t, -, rfl⟩ := Submodule.mem_map.mp he.1
    exact hE t
  have hx : L (Kθ.mkQ f₀) = 0 :=
    tendsto_nhds_unique ((L.continuous.tendsto _).comp hlim)
      (by rw [show (⇑L ∘ u) = fun _ ↦ 0 from funext hzero]; exact tendsto_const_nhds)
  rw [hL, hf₀0] at hx
  exact one_ne_zero hx

/-- Paper: Proposition 7.3.2.2(1), p. 352, with Definition 7.3.2.1, p. 351.
Take F = ℚ, S = {∞}, S₀ = {p}, and the trivial character. All inserted tests
vanish near 0 at p, so their Mellin transforms have no pole at 2πi/log p.
The residue there is continuous and is nonzero on the Gaussian tensored with
the integer-ring indicator, whose Mellin transform contains (1 − p^(-s))⁻¹. -/
theorem Printed.sLocalAbsolutePW_seqDense_false : ¬ Printed.sLocalAbsolutePW_seqDense := by
  intro h
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 ℚ)
  let p : Vℚ := ⟨m, hm.isPrime, NeZero.ne m⟩
  have hsub : (∅ : Finset Vℚ) ⊆ {p} := Finset.empty_subset _
  have hu : NormOneCharacterUnramifiedOutside (1 : PontryaginDual (ideleClassNorm ℚ).ker) ∅ :=
    ⟨⟨1, (mem_unramifiedOutside_iff ℚ ∅ 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ rfl⟩
  exact sec3bP_seqDense_false p hsub hu (sLocalPWBox ∅)
    (h ℚ ∅ {p} {p} (by simp) (Finset.disjoint_empty_left _) (sec3bP_saturated p) sec3bP_pic
      1 hu hsub _ rfl ⊤ (Or.inl rfl))

/-- Paper: Proposition 7.3.2.4(1), pp. 355–356, with Definition 7.3.2.3, p. 355.
The invariant levels formed with the printed unit factors exhaust the homogeneous
theta space sequentially, both for unrestricted and for zero-moment tests. Applying
principal value to the inserted integer indicators realizes the printed unit factors. -/
def Printed.sLocalInvariantPW_seqDense : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S S₀ T : Finset (V(F))),
    T = S ∪ S₀ →
    Disjoint S S₀ → IsSaturatedPlaceSet (F := F) S₀ →
    Subsingleton (CommRing.Pic ((S : Set (V(F))).integer F)) →
    ∀ (ω : PontryaginDual (ideleClassNorm F).ker)
      (hu : NormOneCharacterUnramifiedOutside ω S),
      ∀ (hST : S ⊆ T) (χ : PontryaginDual J₁(F, T)),
        χ = sLocalNormOneCharacter (F := F) T ω (hu.mono hST) →
      ∀ (D : Submodule ℂ (SchwartzBruhat (Multiplicative (SAdeleRing F T)))),
        (D = ⊤ ∨ D = zeroMoments(F, T)) →
        ∀ x : Θ(F, T, χ), x ∈ D.map (q(F, T, χ)) →
          ∃ u : ℕ → Θ(F, T, χ),
            (∀ n, ∃ X > 0, u n ∈ unitLevel(F, S, T, hST, sLocalPWProductRegion S X, D, χ)) ∧
            Tendsto u atTop (𝓝 x)

/-- Paper: Proposition 7.3.2.4(1), pp. 355–356, with Definition 7.3.2.3, p. 355.
Take F = ℚ, S = {∞}, S₀ = {p}, and the trivial character. All inserted tests
vanish near 0 at p, so their Mellin transforms have no pole at 2πi/log p.
The residue there is continuous and is nonzero on the Gaussian tensored with
the integer-ring indicator, whose Mellin transform contains (1 − p^(-s))⁻¹. -/
theorem Printed.sLocalInvariantPW_seqDense_false : ¬ Printed.sLocalInvariantPW_seqDense := by
  intro h
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 ℚ)
  let p : Vℚ := ⟨m, hm.isPrime, NeZero.ne m⟩
  have hsub : (∅ : Finset Vℚ) ⊆ {p} := Finset.empty_subset _
  have hu : NormOneCharacterUnramifiedOutside (1 : PontryaginDual (ideleClassNorm ℚ).ker) ∅ :=
    ⟨⟨1, (mem_unramifiedOutside_iff ℚ ∅ 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ rfl⟩
  exact sec3bP_seqDense_false p hsub hu (sLocalPWProductRegion ∅)
    (h ℚ ∅ {p} {p} (by simp) (Finset.disjoint_empty_left _) (sec3bP_saturated p) sec3bP_pic
      1 hu hsub _ rfl ⊤ (Or.inl rfl))

/-- Paper: Discussion after Proposition 7.3.2.2(4), p. 354.
The closed zero-moment absolute level is said to have codimension two in the full level. -/
def Printed.sLocalAbsolutePW_zeroMoment_codim : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S S₀ T : Finset (V(F))),
    T = S ∪ S₀ → Disjoint S S₀ → IsSaturatedPlaceSet (F := F) S₀ →
    Subsingleton (CommRing.Pic ((S : Set (V(F))).integer F)) →
    ∀ (ω : PontryaginDual (ideleClassNorm F).ker) (hu : NormOneCharacterUnramifiedOutside ω S)
      (hST : S ⊆ T) (χ : PontryaginDual J₁(F, T)),
      χ = sLocalNormOneCharacter (F := F) T ω (hu.mono hST) →
      ∀ X > (0 : ℝ),
        let K := sLocalPWBox S X
        let W := unitLevel(F, S, T, hST, K, ⊤, χ)
        let W₀ := unitLevel(F, S, T, hST, K, zeroMoments(F, T), χ)
        Module.finrank ℂ (W ⧸ W₀.comap W.subtype) = 2

/-- Paper: Discussion after Proposition 7.3.2.2(4), p. 354.
Take the quadratic character modulo five over the rationals at the stage with infinity and
five, with no added places. Translation by the local unit two preserves the test band and
the moments and acts by minus one on the theta quotient. Half the difference from the
translate represents the same class and has both moments zero. The two levels coincide. -/
theorem Printed.sLocalAbsolutePW_zeroMoment_codim_false :
    ¬ Printed.sLocalAbsolutePW_zeroMoment_codim := by
  intro h
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 ℚ)
  let p : Vℚ := ⟨m, hm.isPrime, NeZero.ne m⟩
  let S : Finset Vℚ := ∅
  let T : Finset Vℚ := {p}
  have hsub : S ⊆ T := Finset.empty_subset _
  have hpT : p ∈ T \ S := by simp [S, T]
  have hu : NormOneCharacterUnramifiedOutside (1 : PontryaginDual (ideleClassNorm ℚ).ker) S :=
    ⟨⟨1, (mem_unramifiedOutside_iff ℚ S 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ rfl⟩
  let χ := sLocalNormOneCharacter (F := ℚ) T 1 (hu.mono hsub)
  let K := sLocalPWBox S 1
  let E := unitTests(ℚ, S, T, hsub, K)
  let q := q(ℚ, T, χ)
  let W := unitLevel(ℚ, S, T, hsub, K, ⊤, χ)
  let W₀ := unitLevel(ℚ, S, T, hsub, K, zeroMoments(ℚ, T), χ)
  have h2 : Module.finrank ℂ (W ⧸ W₀.comap W.subtype) = 2 :=
    h ℚ S T T (by simp [S, T]) (Finset.disjoint_empty_left _) (sec3bP_saturated p) sec3bP_pic
      1 hu hsub χ rfl 1 one_pos
  -- Every inserted test vanishes at zero, so only the Fourier moment separates the levels.
  let M := (sAdelePolarValues_isLinear (F := ℚ) (S := T)).mk' _
  let L : B(ℚ, T) →ₗ[ℂ] ℂ := (LinearMap.snd ℂ ℂ ℂ).comp M
  have hE0 (e : B(ℚ, T)) (he : e ∈ E) : e (Multiplicative.ofAdd 0) = 0 := by
    obtain ⟨t, -, rfl⟩ := Submodule.mem_map.mp he
    exact sec3bP_sPV_zero Finset.sdiff_subset hpT 0 rfl t
  have hpol (e : B(ℚ, T)) (he : e ∈ E) (hL : L e = 0) : e ∈ zeroMoments(ℚ, T) :=
    (mem_sAdelePolarSubspace _).mpr ⟨hE0 e he, hL⟩
  obtain ⟨R, hRE, hR1, hRfd, hsplit⟩ : ∃ R : Submodule ℂ (B(ℚ, T)), R ≤ E ∧
      Module.finrank ℂ R ≤ 1 ∧ FiniteDimensional ℂ R ∧ E ≤ (E ⊓ zeroMoments(ℚ, T)) ⊔ R := by
    by_cases hex : ∃ e₀ ∈ E, L e₀ ≠ 0
    · obtain ⟨e₀, he₀, hL₀⟩ := hex
      refine ⟨ℂ ∙ e₀, (Submodule.span_singleton_le_iff_mem _ _).mpr he₀,
        (finrank_span_le_card ({e₀} : Set (B(ℚ, T)))).trans (by simp), inferInstance,
        fun e he ↦ ?_⟩
      have hm : e - (L e / L e₀) • e₀ ∈ E := E.sub_mem he (E.smul_mem _ he₀)
      have hd : e - (L e / L e₀) • e₀ ∈ E ⊓ zeroMoments(ℚ, T) := by
        refine ⟨hm, hpol _ hm ?_⟩
        rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hL₀, sub_self]
      have he' : e = (e - (L e / L e₀) • e₀) + (L e / L e₀) • e₀ := by abel
      rw [he']
      exact Submodule.add_mem_sup hd (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e₀))
    · push Not at hex
      exact ⟨⊥, bot_le, by simp, inferInstance,
        fun e he ↦ Submodule.mem_sup_left ⟨he, hpol e he (hex e he)⟩⟩
  -- The closure of the inserted tests lies in the closed zero-moment level plus one line.
  let Rq := R.map q
  have : FiniteDimensional ℂ Rq := inferInstance
  have hcl : IsClosed ((W₀ ⊔ Rq : Submodule ℂ (Θ(ℚ, T, χ))) : Set (Θ(ℚ, T, χ))) :=
    Submodule.isClosed_sup_finiteDimensional W₀ Rq (Submodule.isClosed_topologicalClosure _)
  have hWle : W ≤ W₀ ⊔ Rq := by
    refine Submodule.topologicalClosure_minimal _ ?_ hcl
    intro x hx
    obtain ⟨e, ⟨he, -⟩, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨a, ha, r, hr, rfl⟩ := Submodule.mem_sup.mp (hsplit he)
    rw [map_add]
    exact Submodule.add_mem_sup (Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem ha))
      (Submodule.mem_map_of_mem hr)
  have hRW : Rq ≤ W := (Submodule.map_mono (le_inf hRE le_top)).trans
    (Submodule.le_topologicalClosure _)
  -- Hence that line maps onto the quotient, which has dimension at most one.
  let ψ : Rq →ₗ[ℂ] W ⧸ W₀.comap W.subtype :=
    (W₀.comap W.subtype).mkQ ∘ₗ Submodule.inclusion hRW
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨a, ha, r, hr, hw⟩ := Submodule.mem_sup.mp (hWle w.property)
    refine ⟨⟨r, hr⟩, ?_⟩
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    have hrw : (r : _) - w = -a := by rw [← hw]; abel
    change (r : _) - (w : _) ∈ W₀
    rw [hrw]
    exact W₀.neg_mem ha
  have hle : Module.finrank ℂ (W ⧸ W₀.comap W.subtype) ≤ Module.finrank ℂ Rq :=
    LinearMap.finrank_le_finrank_of_surjective hψ
  have hRq : Module.finrank ℂ Rq ≤ Module.finrank ℂ R := Submodule.finrank_map_le q R
  omega

/-- Paper: Proposition 7.3.3.2, pp. 357–358.
The diagram of inclusions and restrictions of the continuous ambient PV operator
commutes at the printed cutoffs and is equivariant for the large-norm semigroup.
The containments define the restrictions, so both paths have the same ambient value. -/
def Printed.sLocalPW_principalValue_diagram : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S S₀ T R : Finset (V(F))),
    T = S ∪ S₀ →
    Disjoint S S₀ → IsSaturatedPlaceSet (F := F) S₀ → R ⊆ S₀ → IsSaturatedPlaceSet (F := F) R →
    Subsingleton (CommRing.Pic ((S : Set (V(F))).integer F)) →
    ∀ (ω : PontryaginDual (ideleClassNorm F).ker)
      (hu : NormOneCharacterUnramifiedOutside ω S) (X Y : ℝ),
      0 < X → 0 < Y → X ^ count(F, S) ≤ Y →
      ∀ (hST : S ⊆ T) (χ : PontryaginDual J₁(F, T)),
        χ = sLocalNormOneCharacter (F := F) T ω (hu.mono hST) →
      ∀ hRT : R ⊆ T,
        let D := zeroMoments(F, T)
        let H₀ := D.map (q(F, T, χ))
        let a := unitLevel(F, S, T, hST, sLocalPWBox S X, D, χ)
        let b := unitLevel(F, S, T, hST, sLocalPWProductRegion S Y, D, χ)
        let a' := unitLevel(F, S, T, hST, sLocalPWBox S (size(R) * X), D, χ)
        let b' := unitLevel(F, S, T, hST, sLocalPWProductRegion S (size(R) * Y), D, χ)
        let P := sLocalHomogeneousThetaPrincipalValue (F := F) hRT χ
        let A := (existsUnique_sLocalHomogeneousThetaAction (F := F) (S := T) χ).exists.choose
        a ≤ b ∧ b ≤ H₀ ∧ a' ≤ b' ∧ b' ≤ H₀ ∧
        a.map P ≤ a' ∧ b.map P ≤ b' ∧ H₀.map P ≤ H₀ ∧
        ∀ g : SIdeleQuotient F T, 1 ≤ ((m(F, T) g).val : ℝ) →
          (∀ E ∈ ({a, b, a', b', H₀} : Set (Submodule ℂ (Θ(F, T, χ)))),
            ∀ x ∈ E, A g x ∈ E) ∧ ∀ x ∈ H₀, P (A g x) = A g (P x)

/-- Paper: Proposition 7.3.3.2, pp. 357–358.
Take F = ℚ, S = {∞, 2, 3}, S₀ = R = {5}, trivial character, X = 4 and Y = 64.
At the bottom absolute level 20 use a Fourier test supported at finite norms 16 and 9
and in a small even real neighborhood of ±19, with zero integral and nonzero value at 19.
Its inserted Fourier theta is nonzero at the idele (19, 1/16, 1/9, 1), of norm 2736,
whereas the bottom invariant level has Fourier theta supported in norms at most
5 · 320 = 1600, since the Fourier transform of the 5-unit indicator is supported in
5⁻¹ℤ₅. At the stated idele the only contributing S'-units are ±1. -/
theorem Printed.sLocalPW_principalValue_diagram_false :
    ¬ Printed.sLocalPW_principalValue_diagram := by sorry

local notation "primary(" F ", " T ", " p ")" => sLocalPrimaryPlaces (F := F) T p

/-- Paper: Definition 7.3.3.3(1)–(2), p. 359.
Both printed quotients require the primary principal-value image of the given
zero-moment level to lie inside the level divided by the product of residue sizes. -/
def Printed.sLocalPWOrbitalQuotients_defined : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S S₀ T : Finset (V(F))),
    T = S ∪ S₀ →
    IsSaturatedPlaceSet (F := F) S → Disjoint S S₀ → IsSaturatedPlaceSet (F := F) S₀ →
    Subsingleton (CommRing.Pic ((S : Set (V(F))).integer F)) →
    ∀ (p : Vℚ) (ω : PontryaginDual (ideleClassNorm F).ker)
      (hu : NormOneCharacterUnramifiedOutside ω S) (X Y : ℝ),
      0 < X → 0 < Y →
      ∀ (hST : S ⊆ T) (χ : PontryaginDual J₁(F, T)),
        χ = sLocalNormOneCharacter (F := F) T ω (hu.mono hST) →
      let P := primary(F, T, p)
      P.Nonempty → P ⊆ S₀ →
        let PV := sLocalHomogeneousThetaPrincipalValue (sLocalPrimaryPlaces_subset (F := F) T p) χ
        let D := zeroMoments(F, T)
        (unitLevel(F, S, T, hST, sLocalPWBox S X, D, χ)).map PV ≤
          unitLevel(F, S, T, hST, sLocalPWBox S (X / size(P)), D, χ) ∧
        (unitLevel(F, S, T, hST, sLocalPWProductRegion S Y, D, χ)).map PV ≤
          unitLevel(F, S, T, hST, sLocalPWProductRegion S (Y / size(P)), D, χ)

/-- Paper: Definition 7.3.3.3(1)–(2), p. 359.
Take F = ℚ, S = {∞}, S₀ = {p}, and the trivial character. Take an even smooth Fourier
test h supported near ±ξ with X/p < ξ < X, h(ξ) ≠ 0 and integral zero.
The principal value replaces the base test f by f(x) − f(px). Its Fourier transform
is h(t) − h(t/p)/p. At the idele with real coordinate pξ and finite coordinate 1
the Fourier theta of the resulting unit-indicator tensor is nonzero, while any member
of the printed target level has Fourier theta supported in norms at most X. -/
theorem Printed.sLocalPWOrbitalQuotients_defined_false :
    ¬ Printed.sLocalPWOrbitalQuotients_defined := by sorry

local notation "Rₚ(" F ", " T ", " p ", " χ ")" =>
  sLocalPrimaryOrbitalSubmodule (F := F) (S := T) p χ
local notation "Iₚ(" F ", " T ", " p ", " χ ")" =>
  SLocalOrbitalIndex (F := F) (S := T) (primary(F, T, p)) χ

/-- Paper: Theorem 7.3.3.4(1)–(2), pp. 360–361.
The restricted dual basis and the lifts of its ambient biorthogonals share this enumeration. -/
def Printed.HasPWOrbitalBases {H : Type*} [AddCommGroup H] [Module ℂ H]
    [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℂ H]
    (R W : Submodule ℂ H) (K : Submodule ℂ W)
    (L : ℕ → StrongDual ℂ H) : Prop :=
  ∃ (e : ℕ → (H ⧸ R)) (d : ℕ → StrongDual ℂ (H ⧸ R))
    (eW : ℕ → (W ⧸ K)) (dW : ℕ → StrongDual ℂ (W ⧸ K))
    (ev : ℕ → StrongDual ℂ (StrongDual ℂ (W ⧸ K))),
    (∀ n (x : H), d n (R.mkQ x) = L n x) ∧ IsSchauderBasis e d ∧
    (∀ n (x : W), dW n (K.mkQ x) = L n x.val) ∧
    (∀ n, ∃ x : W, K.mkQ x = eW n ∧ R.mkQ x.val = e n) ∧
    (∀ n ℓ, ev n ℓ = ℓ (eW n)) ∧
    IsSchauderBasis dW ev ∧ SchauderBasis.IsUnconditional dW ev ∧
    IsSchauderBasis eW dW ∧ SchauderBasis.IsAbsolute eW dW

/-- Paper: Theorem 7.3.3.4(1)–(2), pp. 360–361.
For both printed quotient levels every enumeration of either restricted family gives an
unconditional strong-dual basis, and the ambient biorthogonals lift to an absolute basis.
The containment expresses existence of the quotients in (7.3.3.5)–(6). In (7.3.3.7)
the small-stage multiplicity counts contributing places in S, and the Laurent subscript
is the signed exponent of Definition 7.1.2.1. -/
def Printed.sLocalPWOrbital_bases : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S S₀ T : Finset (V(F))),
    T = S ∪ S₀ → Disjoint S S₀ → IsSaturatedPlaceSet (F := F) S₀ →
    Subsingleton (CommRing.Pic ((S : Set (V(F))).integer F)) →
    ∀ (p : Vℚ) (ω : PontryaginDual (ideleClassNorm F).ker)
      (hu : NormOneCharacterUnramifiedOutside ω S)
      (hST : S ⊆ T) (χ : PontryaginDual J₁(F, T)),
      χ = sLocalNormOneCharacter (F := F) T ω (hu.mono hST) →
      let P := primary(F, T, p)
      P.Nonempty → P ⊆ S₀ →
      let pv := sLocalHomogeneousThetaPrincipalValue (sLocalPrimaryPlaces_subset (F := F) T p) χ
      let D := zeroMoments(F, T)
      let H := Θ(F, T, χ)
      let R := Rₚ(F, T, p, χ)
      ∃ B > (0 : ℝ), ∀ (X Y : ℝ), B ≤ X → B ≤ Y → X ^ count(F, S) ≤ Y →
        ∀ (W U : Submodule ℂ H),
          ((W = unitLevel(F, S, T, hST, sLocalPWBox S (X / size(P)), D, χ) ∧
            U = unitLevel(F, S, T, hST, sLocalPWBox S X, D, χ)) ∨
           (W = unitLevel(F, S, T, hST, sLocalPWProductRegion S (Y / size(P)), D, χ) ∧
            U = unitLevel(F, S, T, hST, sLocalPWProductRegion S Y, D, χ))) →
          U.map pv ≤ W ∧
          let K := (U.map pv).comap W.subtype
          let mS := fun c ↦ (sLocalArchPolePlaces (F := F) (S := T) c).card +
            sLocalFinitePoleMultiplicity (F := F) (S := T) S c
          ∀ fourier : Bool, ∃ L : Iₚ(F, T, p, χ) → StrongDual ℂ H,
            (∀ (j : Iₚ(F, T, p, χ)) (f : B(F, T)), L j (q(F, T, χ) f) =
              if fourier then sLocalOrbitalFourierJet (F := F) (S := T) j (q(F, T, χ) f)
              else sLocalZLaurentCoeff (F := F) (S := T) f j.val.1
                ((mS j.val.1 : ℤ) - (j.val.2 : ℤ))) ∧
            ∀ σ : ℕ ≃ Iₚ(F, T, p, χ), Printed.HasPWOrbitalBases R W K (L ∘ σ)

/-- Paper: Theorem 7.3.3.4(1)–(2), pp. 360–361.
Over the rationals with one added prime and trivial character, the index contains the
order-zero jet at the trivial center. It evaluates the Fourier zeta integral at norm
power one, a nonzero multiple of evaluation at zero by Fourier inversion. Its restriction
vanishes on each zero-moment level, contradicting the unit biorthogonal pairing.
The same obstruction persists with the proof's intersection denominator. -/
theorem Printed.sLocalPWOrbital_bases_false : ¬ Printed.sLocalPWOrbital_bases :=
  by sorry

local notation "lexLe(" e ", " a ", " b ")" =>
  ((∀ i, a (e i).val = b (e i).val) ∨
    ∃ i, a (e i).val < b (e i).val ∧ ∀ j < i, a (e j).val = b (e j).val)

/-- Paper: Notation 7.3.4.1, p. 364.
The printed lexicographic orders on the real and complex cutoff tuples make
the no-pole spaces a decreasing filtration. -/
def Printed.sLocalGammaFiltration_antitone : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (V(F)))
    (χ : PontryaginDual J₁(F, S)) (r₁ r₂ : ℕ)
    (realPlaces : Fin r₁ ≃ {w : InfinitePlace F // w.IsReal})
    (complexPlaces : Fin r₂ ≃ {w : InfinitePlace F // w.IsComplex})
    (a b : InfinitePlace F → ℕ),
    lexLe(realPlaces, a, b) → lexLe(complexPlaces, a, b) →
      sLocalGammaFiltration χ b ≤ sLocalGammaFiltration χ a

/-- Paper: Notation 7.3.4.1, p. 364.
For F = ℚ(√2) and the trivial character on the archimedean stage, (0,2) is
lexicographically below (1,0). Both real places have the poles of Γℝ. Apply
the Euler differential polynomial s²(s+2)² in the Mellin variable to the
product Gaussian. Its double pole at −4 remains, while the poles at 0 and
−2 are canceled. Its class is in the stage (1,0) and outside (0,2). -/
theorem Printed.sLocalGammaFiltration_antitone_false :
    ¬ Printed.sLocalGammaFiltration_antitone := by sorry

/-- Paper: Theorem 7.3.4.1(2), pp. 364–365.
On the signed Laurent convention of Definition 7.1.2.1, the displayed positive-index
coefficients (7.3.4.4) form a finite independent spanning family for the annihilator.
On representatives after finite PV this says the finite array is onto and its common
kernel is the no-pole stage, characterized by vanishing of the negative coefficients. -/
def Printed.sLocalGammaFiltration_dual_span : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (V(F)))
    (ω : PontryaginDual J₁(F, S)) (N : InfinitePlace F → ℕ),
    let C := sLocalGammaPoleCutoff (F := F) (S := S) ω N
    let J := {j : QuasiCharacter (SIdeleQuotient F S) × ℕ // j.1 ∈ C ∧
      0 < j.2 ∧ j.2 ≤ (sLocalArchPolePlaces (F := F) (S := S) j.1).card}
    let coeff := fun (f : B(F, S)) (j : J) (k : ℤ) ↦
      sLocalZLaurentCoeff (F := F) (S := S)
        (sAdelePrincipalValue F (Finset.Subset.refl S) f) j.val.1 k
    Finite J ∧ (∀ z : J → ℂ, ∃ f : B(F, S), ∀ j : J, coeff f j j.val.2 = z j) ∧
      (∀ f : B(F, S), (∀ j : J, coeff f j j.val.2 = 0) ↔
        ∀ j : J, coeff f j (-(j.val.2 : ℤ)) = 0)

section DualSpan

open MeasureTheory

local notation "Jq" => SIdeleQuotient ℚ ∅
local notation "Iq" => (SAdeleRing ℚ ∅)ˣ
local notation "Bq" => SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅))
local notation "mq" => sIdeleQuotientNorm ℚ ∅
local notation "hmq" => (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous
local notation "circleℂ" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "chartq(" χ ")" => quasiCharacterNormTwist mq hmq ((circleℂ).comp χ)
local notation "μq" => sMultiplicativeTamagawaMeasure ℚ ∅
local notation "re∞" => InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
local notation "rq(" g ")" => (((mq (QuotientGroup.mk g) : ℝ≥0ˣ) : ℝ≥0) : ℝ)

/-- Conjugating the identity on a tensor factor by an equivalence gives the identity. -/
private theorem sec3bP_pv_aux {A B W : Type*} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B]
    (e : InductiveTensor A W ≃L[ℂ] B) (P : W →ₗ[ℂ] W) (hP : P = LinearMap.id) (f : B) :
    (e.toLinearMap.comp ((TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A) P).comp
      e.symm.toLinearMap)) f = f := by
  subst hP
  exact (congrArg e (LinearMap.congr_fun TensorProduct.map_id (e.symm f))).trans
    (e.apply_symm_apply f)

/-- With no finite places the full principal value is the identity. -/
private theorem sec3bP_PV_empty (f : Bq) :
    sAdelePrincipalValue ℚ (Finset.Subset.refl (∅ : Finset Vℚ)) f = f := by
  unfold sAdelePrincipalValue
  refine sec3bP_pv_aux _ _ ?_ f
  refine LinearMap.ext fun x ↦ ?_
  have hfun : (fun w : (∅ : Finset Vℚ) ↦ if w.val ∈ (∅ : Finset Vℚ) then
      (finitePlacePrincipalValue w.val).toLinearMap else
      (LinearMap.id : SchwartzBruhat (Multiplicative (w.val.adicCompletion ℚ)) →ₗ[ℂ] _)) =
      fun _ ↦ LinearMap.id := funext fun w ↦ absurd w.2 (Finset.notMem_empty _)
  exact (LinearMap.congr_fun (congrArg PiTensorProduct.map hfun) x).trans
    (LinearMap.congr_fun PiTensorProduct.map_id x)

/-- The residue of `g z / z ^ 2` at zero is the derivative of `g` there. -/
private theorem sec3bP_residue_sq {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    complexResidue (fun z ↦ g z / z ^ ((1 : ℤ) + 1)) 0 = deriv g 0 := by
  let h := dslope g 0
  have hh : Differentiable ℂ h := fun z ↦ ((hg.analyticAt z).dslope 0).differentiableAt
  have hgz (z : ℂ) : g z = g 0 + z * h z := by
    have := sub_smul_dslope g 0 z
    rw [sub_zero, smul_eq_mul] at this
    linear_combination -this
  unfold complexResidue
  refine (tendsto_const_nhds.congr' ?_).limUnder_eq
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have hne (z : ℂ) (hz : z ∈ Metric.sphere (0 : ℂ) r) : z ≠ 0 := by
    rintro rfl
    rw [mem_sphere_iff_norm, sub_zero, norm_zero] at hz
    exact hr.ne hz
  have heq : EqOn (fun z ↦ g z / z ^ ((1 : ℤ) + 1))
      (fun z ↦ g 0 * (z - 0) ^ (-2 : ℤ) + (z - 0)⁻¹ • h z) (Metric.sphere 0 r) := by
    intro z hz
    have h0 := hne z hz
    simp only [sub_zero, smul_eq_mul]
    rw [hgz z, show ((1 : ℤ) + 1) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast,
      show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
    field_simp
  have hc1 : CircleIntegrable (fun z ↦ g 0 * (z - 0) ^ (-2 : ℤ)) 0 r :=
    (continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).zpow₀ _
      fun z hz ↦ Or.inl (by simpa using hne z hz))).circleIntegrable hr.le
  have hc2 : CircleIntegrable (fun z ↦ (z - 0)⁻¹ • h z) 0 r :=
    (((continuousOn_id.sub continuousOn_const).inv₀ fun z hz ↦ by simpa using hne z hz).smul
      hh.continuous.continuousOn).circleIntegrable hr.le
  have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [circleIntegral.integral_congr hr.le heq, circleIntegral.integral_add hc1 hc2,
    circleIntegral.integral_const_mul, circleIntegral.integral_sub_zpow_of_ne (by norm_num),
    mul_zero, zero_add,
    Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable countable_empty
      (Metric.mem_ball_self hr) hh.continuous.continuousOn (fun z _ ↦ hh z),
    smul_eq_mul, mul_div_cancel_left₀ _ h2pi]
  exact (dslope_same g 0).symm

/-- The residue of `g z / z ^ (1 - n)` at zero vanishes for entire `g` and `1 ≤ n`. -/
private theorem sec3bP_residue_neg {g : ℂ → ℂ} (hg : Differentiable ℂ g) (n : ℕ) (hn : 0 < n) :
    complexResidue (fun z ↦ g z / z ^ (-(n : ℤ) + 1)) 0 = 0 := by
  unfold complexResidue
  have he : (fun z ↦ g z / z ^ (-(n : ℤ) + 1)) = fun z ↦ g z * z ^ (n - 1) := by
    funext z
    rw [show -(n : ℤ) + 1 = -((n - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, div_inv_eq_mul]
  rw [he]
  refine (tendsto_const_nhds.congr' ?_).limUnder_eq
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have hd : Differentiable ℂ (fun z ↦ g z * z ^ (n - 1)) := hg.mul (differentiable_id.pow _)
  rw [Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le countable_empty
    hd.continuous.continuousOn (fun z _ ↦ hd z), zero_div]

/-- A compactly supported smooth profile of the real coordinate is a test at the rational
archimedean stage. -/
private theorem sec3bP_test (φ : ℝ → ℝ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∃ f : Bq, ∀ x : SAdeleRing ℚ ∅,
      f (Multiplicative.ofAdd x) = (φ (re∞ (x.1 Rat.infinitePlace)) : ℂ) := by
  have hreal (w : InfinitePlace ℚ) : w.IsReal :=
    (Subsingleton.elim Rat.infinitePlace w) ▸ Rat.isReal_infinitePlace
  let i0 : {w : InfinitePlace ℚ // w.IsReal} := ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
  have : IsEmpty {w : InfinitePlace ℚ // w.IsComplex} :=
    ⟨fun w ↦ (InfinitePlace.not_isReal_iff_isComplex.mpr w.2) (hreal w.1)⟩
  let G : mixedEmbedding.mixedSpace ℚ → ℂ := fun y ↦ (φ (y.1 i0) : ℂ)
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G :=
    Complex.ofRealCLM.contDiff.comp (hφ.comp
      ((ContinuousLinearMap.proj i0 : ({w : InfinitePlace ℚ // w.IsReal} → ℝ) →L[ℝ] ℝ).contDiff.comp
        contDiff_fst))
  have hK : IsCompact ((fun t : ℝ ↦ ((fun _ ↦ t, 0) : mixedEmbedding.mixedSpace ℚ)) ''
      tsupport φ) :=
    hc.isCompact.image (by fun_prop)
  have hGc : HasCompactSupport G := by
    refine HasCompactSupport.intro hK fun y hy ↦ ?_
    by_contra hne
    apply hy
    refine ⟨y.1 i0, subset_tsupport φ (fun h0 ↦ hne (by simp [G, h0])), ?_⟩
    exact Prod.ext (funext fun j ↦ congrArg y.1 (Subsingleton.elim i0 j)) (Subsingleton.elim _ _)
  let Gs : SchwartzMap (mixedEmbedding.mixedSpace ℚ) ℂ := hGc.toSchwartzMap hG
  have hmem := (mem_archimedeanSchwartzBruhat_iff (F := ℚ)
    (fun x : InfiniteAdeleRing ℚ ↦ (φ (re∞ (x Rat.infinitePlace)) : ℂ))).mpr ⟨Gs, fun x ↦ rfl⟩
  let a : SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ)) := ⟨_, hmem⟩
  obtain ⟨e, he⟩ := sAdeleSchwartz_inductiveTensor_equiv ℚ (∅ : Finset Vℚ)
  let g : ∀ w : (∅ : Finset Vℚ), SchwartzBruhat (Multiplicative (w.val.adicCompletion ℚ)) :=
    fun w ↦ absurd w.2 (Finset.notMem_empty _)
  refine ⟨e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w)), fun x ↦ ?_⟩
  rw [he, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  rfl

/-- At the rational archimedean stage the real coordinate of an idele has the idelic norm
as its absolute value. -/
private theorem sec3bP_norm (g : Iq) : (re∞ (g.val.1 Rat.infinitePlace)) ^ 2 = rq(g) ^ 2 := by
  have hn : rq(g) = ‖g.val.1 Rat.infinitePlace‖ := by
    change ((sIdeleNorm ℚ ∅ g : ℝ≥0) : ℝ) = _
    rw [sIdeleNorm, Finset.univ_eq_empty (α := (∅ : Finset Vℚ)), Finset.prod_empty, mul_one,
      Fintype.prod_subsingleton _ Rat.infinitePlace, Rat.isReal_infinitePlace.mult_eq_one, pow_one]
    rfl
  rw [hn, ← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    Rat.isReal_infinitePlace).norm_map_of_map_zero (map_zero _), Real.norm_eq_abs, sq_abs]

/-- A smooth bump supported in `(4, 9)`. -/
private theorem sec3bP_bump : ∃ ψ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧ (∀ t, 0 ≤ ψ t) ∧
    (∀ t, ψ t ≠ 0 → 4 < t ∧ t < 9) ∧ ψ (25 / 4) ≠ 0 := by
  let b : ContDiffBump (25 / 4 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  refine ⟨b, b.contDiff, fun t ↦ b.nonneg, fun t ht ↦ ?_, ?_⟩
  · have h1 : t ∈ Metric.ball (25 / 4 : ℝ) (1 / 4) := by
      have := Function.mem_support.mpr ht
      rwa [b.support_eq] at this
    rw [Real.ball_eq_Ioo] at h1
    obtain ⟨h1, h2⟩ := h1
    constructor <;> linarith
  · rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num))]
    norm_num

/-- The profiles `ψ(t²) t⁻²ⁿ` are smooth and compactly supported. -/
private theorem sec3bP_profile (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hs : ∀ t, ψ t ≠ 0 → 4 < t ∧ t < 9) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ ↦ ψ (t ^ 2) * ((t ^ 2) ^ n)⁻¹) ∧
      HasCompactSupport (fun t : ℝ ↦ ψ (t ^ 2) * ((t ^ 2) ^ n)⁻¹) := by
  constructor
  · rw [contDiff_iff_contDiffAt]
    intro t
    by_cases ht : t = 0
    · subst ht
      have hev : (fun t : ℝ ↦ ψ (t ^ 2) * ((t ^ 2) ^ n)⁻¹) =ᶠ[𝓝 0] fun _ ↦ 0 := by
        have h4 : ∀ᶠ t : ℝ in 𝓝 0, t ^ 2 < 4 :=
          (continuousAt_id.pow 2).eventually_lt continuousAt_const (by norm_num)
        filter_upwards [h4] with t ht
        have : ψ (t ^ 2) = 0 := by
          by_contra h
          linarith [(hs _ h).1]
        simp [this]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · exact (hψ.contDiffAt.comp t (contDiffAt_id.pow 2)).mul
        (((contDiffAt_id.pow 2).pow n).inv (pow_ne_zero _ (pow_ne_zero _ ht)))
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) 3) fun t ht ↦ ?_
    have : ψ (t ^ 2) = 0 := by
      by_contra h
      have h9 := (hs _ h).2
      apply ht
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    simp [this]

/-- Two functions in meromorphic normal form on the plane that agree on the right
half-plane agree everywhere. -/
private theorem sec3bP_eq_of_meromorphicNFOn {G H : ℂ → ℂ}
    (hG : MeromorphicNFOn G univ) (hH : MeromorphicNFOn H univ)
    (h : ∀ z : ℂ, 0 < z.re → G z = H z) (s : ℂ) : G s = H s := by
  have hAt : meromorphicOrderAt (G - H) (1 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hn : ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), 0 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    exact (hn.filter_mono nhdsWithin_le_nhds).mono fun z hz ↦ sub_eq_zero.mpr (h z hz)
  have hOrd := (hG.meromorphicOn.sub hH.meromorphicOn).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ (1 : ℂ)) (mem_univ s) hAt
  have hNear : G =ᶠ[𝓝[≠] s] H :=
    (meromorphicOrderAt_eq_top_iff.mp hOrd).mono fun _ h ↦ sub_eq_zero.mp h
  exact (((hG (mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hH (mem_univ s))).mp
    hNear).eq_of_nhds

/-- Every quasi-character of the rational archimedean stage lies on a unitary chart. -/
private theorem sec3bP_chart (c : QuasiCharacter Jq) :
    ∃ (χ : PontryaginDual Jq) (s : ℂ), ∀ z : ℂ,
      quasiCharacterNormTwist mq hmq c z = chartq(χ) (s + z) := by
  let : LocallyCompactSpace Iq := (sIdeleGroup_description ℚ ∅).2.2.1
  have := isClosed_sProjectedDiagonal (F := ℚ) (S := ∅)
  have hp := isProperMap_sIdeleQuotientNorm ℚ ∅
  have hne : ∃ g, mq g ≠ 1 := by
    obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section ℚ ∅
    obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
    exact ⟨τ t, (hτ t).trans_ne ht⟩
  let a := quasiCharacterAbscissa mq hp hne c
  let d := quasiCharacterNormTwist mq hmq c (-(a : ℂ))
  have hrad (g : Jq) : (((mq g : ℝ≥0) : ℝ) : ℂ) ^ (a : ℂ) = (‖c g‖ : ℂ) := by
    rw [← Complex.ofReal_cpow (NNReal.coe_nonneg _) a,
      norm_quasiCharacter_eq_rpow_abscissa mq hp hne]
  have hd (g : Jq) : d g = c g / (‖c g‖ : ℂ) := by
    change c g * _ ^ (-(a : ℂ)) = _
    rw [Complex.cpow_neg, hrad, div_eq_mul_inv]
  have hn (g : Jq) : ‖c g‖ ≠ 0 := norm_ne_zero_iff.mpr ((Group.isUnit g).map c).ne_zero
  let χ : PontryaginDual Jq :=
    { toFun := fun g ↦ ⟨d g, mem_sphere_zero_iff_norm.mpr (by
        rw [hd, norm_div, Complex.norm_of_nonneg (norm_nonneg _), div_self (hn g)])⟩
      map_one' := Subtype.ext d.map_one
      map_mul' x y := Subtype.ext (d.map_mul x y)
      continuous_toFun := d.continuous.subtype_mk _ }
  refine ⟨χ, (a : ℂ), fun z ↦ ContinuousMonoidHom.ext fun g ↦ ?_⟩
  have hN : (((mq g : ℝ≥0) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (mq g).ne_zero)
  change c g * (((mq g : ℝ≥0) : ℝ) : ℂ) ^ z =
    d g * (((mq g : ℝ≥0) : ℝ) : ℂ) ^ ((a : ℂ) + z)
  rw [hd, Complex.cpow_add _ _ hN, hrad, ← mul_assoc, div_mul_cancel₀ _
    (Complex.ofReal_ne_zero.mpr (hn g))]

/-- Dividing a test by an even power of the norm shifts its zeta integral. -/
private theorem sec3bP_shift (F0 G : Bq) (n : ℕ)
    (hF : ∀ g : Iq, G (Multiplicative.ofAdd g.val) =
      F0 (Multiplicative.ofAdd g.val) * (((rq(g) : ℂ)) ^ (2 * n))⁻¹)
    (χ : PontryaginDual Jq) (v : ℂ) :
    sLocalIdelicZetaIntegral G (chartq(χ) (v + 2 * n)) =
      sLocalIdelicZetaIntegral F0 (chartq(χ) v) := by
  unfold sLocalIdelicZetaIntegral
  congr 1
  funext g
  change G _ * ((χ (QuotientGroup.mk g) : ℂ) * ((rq(g) : ℂ)) ^ (v + 2 * n)) =
    F0 _ * ((χ (QuotientGroup.mk g) : ℂ) * ((rq(g) : ℂ)) ^ v)
  have h0 : ((rq(g) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (Units.ne_zero _))
  have h1 := pow_ne_zero (2 * n) h0
  rw [hF, Complex.cpow_add _ _ h0, show (2 * (n : ℂ)) = ((2 * n : ℕ) : ℂ) by push_cast; ring,
    Complex.cpow_natCast]
  field_simp

/-- A test whose quotients by even powers of the norm are again tests has an entire
Z-function on every unitary chart. -/
private theorem sec3bP_entire (F0 : Bq) (Fn : ℕ → Bq)
    (hF : ∀ (n : ℕ) (g : Iq), Fn n (Multiplicative.ofAdd g.val) =
      F0 (Multiplicative.ofAdd g.val) * (((rq(g) : ℂ)) ^ (2 * n))⁻¹)
    (χ : PontryaginDual Jq) :
    Differentiable ℂ (fun s ↦ sLocalIdelicZFunction F0 (chartq(χ) s)) := by
  have hint (n : ℕ) (v : ℂ) := sec3bP_shift F0 (Fn n) n (hF n) χ v
  have hmer (n : ℕ) : MeromorphicNFOn
      (fun v ↦ sLocalIdelicZFunction (Fn n) (chartq(χ) (v + 2 * n))) univ := fun z _ ↦
    (meromorphicNFAt_comp_add_const_iff_meromorphicNFAt
      (f := fun s ↦ sLocalIdelicZFunction (Fn n) (chartq(χ) s))).mpr
      (sLocalIdelicZFunction_meromorphic (Fn n) χ (mem_univ _))
  have heq (n : ℕ) (v : ℂ) : sLocalIdelicZFunction F0 (chartq(χ) v) =
      sLocalIdelicZFunction (Fn n) (chartq(χ) (v + 2 * n)) := by
    refine sec3bP_eq_of_meromorphicNFOn (G := fun v ↦ sLocalIdelicZFunction F0 (chartq(χ) v))
      (sLocalIdelicZFunction_meromorphic F0 χ) (hmer n) (fun z hz ↦ ?_) v
    have hz' : 0 < (z + 2 * (n : ℂ)).re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
      norm_num
      positivity
    rw [sLocalIdelicZFunction_eq_integral F0 ⟨χ, z, hz, rfl⟩,
      sLocalIdelicZFunction_eq_integral (Fn n) ⟨χ, z + 2 * n, hz', rfl⟩, hint]
  have han (n : ℕ) (w : ℂ) (hw : 0 < w.re) :
      AnalyticAt ℂ (fun s ↦ sLocalIdelicZFunction (Fn n) (chartq(χ) s)) w := by
    have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    refine ((sLocalIdelicZetaIntegral_analyticOn (Fn n) χ) w hw).congr ?_
    filter_upwards [hopen.mem_nhds hw] with s hs
    exact (sLocalIdelicZFunction_eq_integral (Fn n) ⟨χ, s, hs, rfl⟩).symm
  intro v
  obtain ⟨n, hn⟩ := exists_nat_gt (-v.re)
  have hfun : (fun s ↦ sLocalIdelicZFunction F0 (chartq(χ) s)) =
      fun s ↦ sLocalIdelicZFunction (Fn n) (chartq(χ) (s + 2 * n)) := funext (heq n)
  rw [hfun]
  have hpos : 0 < (v + 2 * (n : ℂ)).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    norm_num
    linarith
  exact differentiableAt_comp_add_const.mpr (han n (v + 2 * n) hpos).differentiableAt

/-- A real function with a holomorphic extension, growing at least geometrically to the
right and bounded below near zero, has positive derivative at zero. -/
private theorem sec3bP_slope {g : ℂ → ℂ} (hg : Differentiable ℂ g) (G : ℝ → ℝ)
    (hgG : ∀ t : ℝ, 0 < t → g t = G t)
    (hmono : ∀ s t : ℝ, 0 < s → s < t → (2 : ℝ) ^ (t - s) * G s ≤ G t)
    (hlow : ∀ s : ℝ, 0 < s → s < 1 → (3 : ℝ) ^ (s - 1) * G 1 ≤ G s) (h1 : 0 < G 1) :
    0 < (deriv g 0).re := by
  let h : ℝ → ℝ := fun t ↦ (g t).re
  have hd : HasDerivAt h (deriv g 0).re 0 :=
    HasDerivAt.real_of_complex (z := 0) (by simpa using (hg 0).hasDerivAt)
  have hhG (t : ℝ) (ht : 0 < t) : h t = G t := by simp [h, hgG t ht]
  have hcont : Tendsto h (𝓝[>] 0) (𝓝 (h 0)) :=
    hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  set c := (3 : ℝ)⁻¹ * G 1 with hcdef
  have hc : 0 < c := by positivity
  have h0 : c ≤ h 0 := by
    refine ge_of_tendsto hcont ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs
    rw [hhG s hs.1]
    refine le_trans ?_ (hlow s hs.1 hs.2)
    apply mul_le_mul_of_nonneg_right _ h1.le
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hs.1])
  have hup (t : ℝ) (ht : 0 < t) : (2 : ℝ) ^ t * h 0 ≤ G t := by
    have hc2 : Continuous (fun s : ℝ ↦ (2 : ℝ) ^ (t - s)) := by
      simp_rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      fun_prop
    have hlim : Tendsto (fun s ↦ (2 : ℝ) ^ (t - s) * h s) (𝓝[>] 0)
        (𝓝 ((2 : ℝ) ^ (t - 0) * h 0)) :=
      ((hc2.tendsto 0).mono_left nhdsWithin_le_nhds).mul hcont
    rw [sub_zero] at hlim
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT ht] with s hs
    rw [hhG s hs.1]
    exact hmono s t hs.1 hs.2
  have hslope : Tendsto (slope h 0) (𝓝[>] 0) (𝓝 (deriv g 0).re) :=
    (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
      (nhdsWithin_mono _ fun x (hx : 0 < x) ↦ hx.ne')
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbound : Real.log 2 * c ≤ (deriv g 0).re := by
    refine ge_of_tendsto hslope ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [slope_def_field, hhG t ht, sub_zero, le_div_iff₀ ht]
    have h2 : 1 + t * Real.log 2 ≤ (2 : ℝ) ^ t := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      linarith [Real.add_one_le_exp (Real.log 2 * t)]
    have hA := mul_le_mul_of_nonneg_right h2 (hc.le.trans h0)
    have hB := mul_nonneg (mul_nonneg ht.le hlog.le) (sub_nonneg.mpr h0)
    nlinarith [hup t ht]
  exact lt_of_lt_of_le (mul_pos hlog hc) hbound

/-- On the trivial chart the Z-function of a nonnegative bump in norm between two and
three has positive derivative at zero. -/
private theorem sec3bP_deriv_pos (F0 : Bq) (ψ : ℝ → ℝ) (hψc : Continuous ψ)
    (hψ0 : ∀ t, 0 ≤ ψ t) (hs : ∀ t, ψ t ≠ 0 → 4 < t ∧ t < 9) (hψ1 : ψ (25 / 4) ≠ 0)
    (hF : ∀ g : Iq, F0 (Multiplicative.ofAdd g.val) = (ψ (rq(g) ^ 2) : ℂ))
    (hd : Differentiable ℂ (fun s ↦ sLocalIdelicZFunction F0 (chartq(1) s))) :
    0 < (deriv (fun s ↦ sLocalIdelicZFunction F0 (chartq(1) s)) 0).re := by
  let F (t : ℝ) (g : Iq) : ℝ := ψ (rq(g) ^ 2) * rq(g) ^ t
  have hpt (t : ℝ) (g : Iq) : F0 (Multiplicative.ofAdd g.val) * chartq(1) t (QuotientGroup.mk g) =
      ((F t g : ℝ) : ℂ) := by
    change F0 _ * (((1 : PontryaginDual Jq) (QuotientGroup.mk g) : ℂ) * ((rq(g) : ℂ)) ^ (t : ℂ)) = _
    rw [hF, PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.ofReal_mul,
      Complex.ofReal_cpow (NNReal.coe_nonneg _)]
  have hpos (t : ℝ) (ht : 0 < t) : chartq(1) t ∈ {c : QuasiCharacter Jq |
      ∃ (χ : PontryaginDual Jq) (s : ℂ), s ∈ Complex.re ⁻¹' Ioi (0 : ℝ) ∧ c = chartq(χ) s} :=
    ⟨1, t, by simpa using ht, rfl⟩
  have hval (t : ℝ) (ht : 0 < t) :
      sLocalIdelicZFunction F0 (chartq(1) t) = ((∫ g, F t g ∂μq : ℝ) : ℂ) := by
    let : MeasurableSpace (SAdeleRing ℚ ∅) := instMeasurableSpaceSAdeleRing ℚ ∅
    rw [sLocalIdelicZFunction_eq_integral F0 (hpos t ht), ← integral_complex_ofReal]
    unfold sLocalIdelicZetaIntegral
    congr 1
    funext g
    exact hpt t g
  have hint (t : ℝ) (ht : 0 < t) : Integrable (F t) μq := by
    have h := sLocalIdelicZetaIntegral_integrable F0 (chartq(1) t) (hpos t ht)
    simp_rw [hpt] at h
    simpa using ContinuousLinearMap.integrable_comp Complex.reCLM h
  -- Pointwise facts about the norm on the support of the bump.
  have hr0 (g : Iq) : 0 < rq(g) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hsupp (g : Iq) (hg : ψ (rq(g) ^ 2) ≠ 0) : 2 < rq(g) ∧ rq(g) < 3 := by
    obtain ⟨h4, h9⟩ := hs _ hg
    have := hr0 g
    constructor <;> nlinarith
  have hmono (s t : ℝ) (hs0 : 0 < s) (hst : s < t) :
      (2 : ℝ) ^ (t - s) * (∫ g, F s g ∂μq) ≤ ∫ g, F t g ∂μq := by
    rw [← integral_const_mul]
    refine integral_mono ((hint s hs0).const_mul _) (hint t (hs0.trans hst)) fun g ↦ ?_
    by_cases hg : ψ (rq(g) ^ 2) = 0
    · change (2 : ℝ) ^ (t - s) * (ψ (rq(g) ^ 2) * rq(g) ^ s) ≤ ψ (rq(g) ^ 2) * rq(g) ^ t
      rw [hg]
      simp
    obtain ⟨h2, -⟩ := hsupp g hg
    change (2 : ℝ) ^ (t - s) * (ψ (rq(g) ^ 2) * rq(g) ^ s) ≤ ψ (rq(g) ^ 2) * rq(g) ^ t
    have hx := hr0 g
    have hpow : (2 : ℝ) ^ (t - s) ≤ rq(g) ^ (t - s) :=
      Real.rpow_le_rpow (by norm_num) h2.le (by linarith)
    have hsplit : rq(g) ^ t = rq(g) ^ (t - s) * rq(g) ^ s := by
      rw [← Real.rpow_add hx, sub_add_cancel]
    rw [hsplit]
    have := hψ0 (rq(g) ^ 2)
    have := Real.rpow_nonneg hx.le s
    nlinarith [mul_le_mul_of_nonneg_right hpow (mul_nonneg (hψ0 (rq(g) ^ 2)) this)]
  have hlow (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
      (3 : ℝ) ^ (s - 1) * (∫ g, F 1 g ∂μq) ≤ ∫ g, F s g ∂μq := by
    rw [← integral_const_mul]
    refine integral_mono ((hint 1 one_pos).const_mul _) (hint s hs0) fun g ↦ ?_
    by_cases hg : ψ (rq(g) ^ 2) = 0
    · change (3 : ℝ) ^ (s - 1) * (ψ (rq(g) ^ 2) * rq(g) ^ (1 : ℝ)) ≤ ψ (rq(g) ^ 2) * rq(g) ^ s
      rw [hg]
      simp
    obtain ⟨-, h3⟩ := hsupp g hg
    change (3 : ℝ) ^ (s - 1) * (ψ (rq(g) ^ 2) * rq(g) ^ (1 : ℝ)) ≤ ψ (rq(g) ^ 2) * rq(g) ^ s
    have hx := hr0 g
    have hpow : (3 : ℝ) ^ (s - 1) ≤ rq(g) ^ (s - 1) :=
      Real.rpow_le_rpow_of_nonpos hx h3.le (by linarith)
    have hsplit : rq(g) ^ s = rq(g) ^ (s - 1) * rq(g) ^ (1 : ℝ) := by
      rw [← Real.rpow_add hx, sub_add_cancel]
    rw [hsplit]
    have := hψ0 (rq(g) ^ 2)
    have := Real.rpow_nonneg hx.le (1 : ℝ)
    nlinarith [mul_le_mul_of_nonneg_right hpow (mul_nonneg (hψ0 (rq(g) ^ 2)) this)]
  have h1 : 0 < ∫ g, F 1 g ∂μq := by
    have := sMultiplicativeTamagawaMeasure_isHaarMeasure (F := ℚ) (S := ∅)
    have hrc : Continuous (fun g : Iq ↦ rq(g)) :=
      NNReal.continuous_coe.comp (Units.continuous_val.comp ((isProperMap_sIdeleQuotientNorm ℚ ∅).continuous.comp QuotientGroup.continuous_mk))
    have hU : IsOpen {g : Iq | ψ (rq(g) ^ 2) ≠ 0} :=
      isOpen_ne_fun (hψc.comp (hrc.pow 2)) continuous_const
    obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section ℚ ∅
    let u : ℝ≥0ˣ := Units.mk0 (5 / 2) (by norm_num)
    obtain ⟨g, hg⟩ := (QuotientGroup.mk_surjective :
      Function.Surjective (QuotientGroup.mk : Iq → Jq)) (σ u)
    have hgr : rq(g) = 5 / 2 := by
      rw [hg, hσ u]
      simp [u]
    have hne : ({g : Iq | ψ (rq(g) ^ 2) ≠ 0}).Nonempty :=
      ⟨g, by
        change ψ (rq(g) ^ 2) ≠ 0
        rw [hgr]
        norm_num
        exact hψ1⟩
    rw [integral_pos_iff_support_of_nonneg (fun g ↦ mul_nonneg (hψ0 _)
      (Real.rpow_nonneg (hr0 g).le _)) (hint 1 one_pos)]
    refine lt_of_lt_of_le (hU.measure_pos μq hne) (measure_mono fun g hg ↦ ?_)
    exact mul_ne_zero hg (Real.rpow_pos_of_pos (hr0 g) _).ne'
  exact sec3bP_slope hd (fun t ↦ ∫ g, F t g ∂μq) hval hmono hlow h1

/-- Paper: Theorem 7.3.4.1(2), pp. 364–365.
For the rational archimedean stage and trivial character take a nonnegative nonzero even
bump in the annulus two to three. Its Mellin transform is entire, and its derivative
at zero integrates the bump against a strictly positive logarithm. The coefficient
of exponent one therefore fails to annihilate the zero-cutoff stage. -/
theorem Printed.sLocalGammaFiltration_dual_span_false : ¬ Printed.sLocalGammaFiltration_dual_span := by
  intro h
  have h3 := (h ℚ ∅ 1 (fun _ ↦ 0)).2.2
  obtain ⟨ψ, hψ, hψ0, hs, hψ1⟩ := sec3bP_bump
  choose Fn hFn using fun n : ℕ ↦ sec3bP_test _ (sec3bP_profile ψ hψ hs n).1
    (sec3bP_profile ψ hψ hs n).2
  have hval (n : ℕ) (g : Iq) : Fn n (Multiplicative.ofAdd g.val) =
      ((ψ (rq(g) ^ 2) * ((rq(g) ^ 2) ^ n)⁻¹ : ℝ) : ℂ) := by
    rw [hFn, sec3bP_norm]
  have hF : ∀ (n : ℕ) (g : Iq), Fn n (Multiplicative.ofAdd g.val) =
      Fn 0 (Multiplicative.ofAdd g.val) * (((rq(g) : ℂ)) ^ (2 * n))⁻¹ := by
    intro n g
    rw [hval, hval]
    push_cast
    rw [pow_mul]
    simp
  have hF0 (g : Iq) : Fn 0 (Multiplicative.ofAdd g.val) = (ψ (rq(g) ^ 2) : ℂ) := by
    rw [hval]
    simp
  -- Every centered Z-germ of the test is entire.
  have hent (c : QuasiCharacter Jq) :
      Differentiable ℂ (fun z ↦ sLocalIdelicZFunction (Fn 0) (quasiCharacterNormTwist mq hmq c z)) := by
    obtain ⟨χ, s, hχ⟩ := sec3bP_chart c
    simp only [hχ]
    exact (sec3bP_entire (Fn 0) Fn hF χ).comp (differentiable_const _ |>.add differentiable_id)
  have hneg := (h3 (Fn 0)).mpr (fun j ↦ by
    beta_reduce
    rw [sec3bP_PV_empty]
    exact sec3bP_residue_neg (hent _) _ j.2.2.1)
  have hC := (sLocalGammaPoleCutoff_zero (F := ℚ) ∅).1
  obtain ⟨-, w, hw, -⟩ := id hC
  have hj := hneg ⟨(1, 1), hC, Nat.one_pos, Finset.card_pos.mpr ⟨w, hw⟩⟩
  beta_reduce at hj
  rw [sec3bP_PV_empty] at hj
  change complexResidue (fun z ↦ sLocalIdelicZFunction (Fn 0)
    (quasiCharacterNormTwist mq hmq 1 z) / z ^ ((1 : ℤ) + 1)) 0 = 0 at hj
  rw [sec3bP_residue_sq (hent 1)] at hj
  have h1 : (1 : QuasiCharacter Jq) = (circleℂ).comp (1 : PontryaginDual Jq) :=
    ContinuousMonoidHom.ext fun g ↦ by
      change (1 : ℂ) = (((1 : PontryaginDual Jq) g : Circle) : ℂ)
      rw [PontryaginDual.one_apply, Circle.coe_one]
  rw [h1] at hj
  have hpos := sec3bP_deriv_pos (Fn 0) ψ hψ.continuous hψ0 hs hψ1 hF0
    (sec3bP_entire (Fn 0) Fn hF 1)
  have hzero : (deriv (fun s ↦ sLocalIdelicZFunction (Fn 0) (chartq(1) s)) 0).re = 0 := by
    rw [show deriv (fun s ↦ sLocalIdelicZFunction (Fn 0) (chartq(1) s)) 0 = 0 from hj]
    rfl
  linarith

end DualSpan

end RiemannMasullo
