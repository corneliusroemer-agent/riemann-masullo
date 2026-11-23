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

/-- Paper: Theorem 7.3.4.1(2), pp. 364–365.
For the rational archimedean stage and trivial character take a nonnegative nonzero even
bump in the annulus two to three. Its Mellin transform is entire, and its derivative
at zero integrates the bump against a strictly positive logarithm. The coefficient
of exponent one therefore fails to annihilate the zero-cutoff stage. -/
theorem Printed.sLocalGammaFiltration_dual_span_false : ¬ Printed.sLocalGammaFiltration_dual_span :=
  by sorry

end RiemannMasullo
