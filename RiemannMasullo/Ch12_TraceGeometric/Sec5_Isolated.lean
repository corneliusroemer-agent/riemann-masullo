module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5

/-! # Isolated statements of §12.5

Statements of the section that are neither proved nor refuted and that nothing else in Lean
uses, with what follows from them (`AGENTS.md`, "False statements and gaps"). Nothing imports
this file.

## The projective strip kernel needed for (12.5.1.4)

The first theorem supplies the kernel hypothesis of the smoothened diagonal formula in §12.5.
The second theorem specializes that formula to this kernel.
## The strip trace identity

The comparison that §12.3 announces, stated as an identity of traces on the strip quotient
(`spectralStripTrace_eq_localTerms`). With the kernel above it gives the conclusion of
`traceFormula_exteriorZeros` (`traceFormula_exteriorZeros_of_spectralStripTrace`), along the
route of p. 520: the spectral side (12.5.1.4) and the trace identity.
-/

@[expose] public noncomputable section

open MeasureTheory NumberField Set
open scoped NNReal

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hs₁(" hs ")" => (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) hs)
local notation "hs₀(" hs ")" => (zero_lt_one.trans hs₁(hs)).le

/-- Paper: (12.5.1.4), p. 520. For a test vanishing on the norm-one classes, a projective
Sobolev tensor represents convolution by the test after spectral projection at twist 1/2.
Reconstruction: Definition 10.4.3.7(2), p. 473, subtracts the spectral kernel. Using this
subtraction on p. 520 presupposes a tensor for the operator in (10.4.3.45).
Deviation: We ask for any representing tensor, restricted to the positive half-widths and
tests of Theorem 12.5.1.1. We impose no finite-rank expansion on the tensor.
Gap: The projective norm estimate for the geometric component of the output is missing.
Nothing in the Lean uses this statement, and it is not known how it connects with the rest of
the proof in Lean; in the paper it is used on pp. 520, 522. -/
theorem exists_projectiveKernel_stripTestAction_spectralProjection
    (φ : BruhatCompactSupport C𝔽) (_hφ : ∀ g : C₁, φ.val g = 0)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) :
    ∃ K, sobolevProjectiveKernelOperator (F := F) hα.le hs₀(hs) K =
      (hardySobolevTestAction μ𝔽 m𝔽 (-α) α s ((neg_nonpos.mpr hα.le).trans hα.le) hs₀(hs) φ).comp
        (spectralProjection (F := F) (1 / 2) hα.le hs₀(hs)) := by
  sorry

/-- Paper: (12.5.1.4), p. 520. The smoothened geometric diagonal is Haar-integrable, and the
strip zero terms sum absolutely to its negative integral.
Deviation: As in §12.5 of the library, a measurable D′-sequence specifies the smoothening,
and the sum uses the closed strip with strict reciprocal-weight multiplicities on its edges.
It agrees with the printed interior sum when both edges are zero-free.
It is proved from the kernel existence statement above, which is open, so it is no more
established than that statement. Nothing in the Lean uses it. -/
theorem hasSum_stripZeros_neg_integral_smoothenedDiagonal_of_vanishing
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s)
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    let hK := exists_projectiveKernel_stripTestAction_spectralProjection φ hφ hα hs
    let diagonal (x : C𝔽) := dSequenceKernelSmoothening μ𝔽 U
      (globalStripGeometricKernel (F := F) (1 / 2) hα.le hs₁(hs) φ hK) (x, x)
    let shift (b t : ℝ) := (b : ℂ) + (t : ℂ) * Complex.I
    let order (η : PontryaginDual C𝔽) := meromorphicOrderAt (continuedCompletedHeckeL η)
    let Z := {z : PontryaginDual C₁ × ℝ × ℝ //
      z.2.1 ∈ Icc (-α) α ∧ 0 < order (χ z.1) (shift (1 / 2 + z.2.1) z.2.2)}
    let term (z : Z) := ((spectralStripMultiplicity α s z.val.2.1
      (order (χ z.val.1) (shift (1 / 2 + z.val.2.1) z.val.2.2)).untop₀.toNat : ℕ) : ℂ) *
      modulatedFourierMellin m𝔽 univ ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
        μ𝔽 φ.val (ideleClassNormTwist (χ z.val.1) (shift z.val.2.1 z.val.2.2))
    Integrable diagonal μ𝔽 ∧ Summable (fun z ↦ ‖term z‖) ∧
      HasSum term (-(∫ x, diagonal x ∂μ𝔽)) :=
  hasSum_stripZeros_neg_integral_smoothenedDiagonal φ hφ χ hχ hα hs
    (exists_projectiveKernel_stripTestAction_spectralProjection φ hφ hα hs) U hU hBorel

section StripTrace

/-! ### The strip trace identity -/

attribute [local instance] instSpectralQuotientPolynormableSec3

local notation "V" => IsDedekindDomain.HeightOneSpectrum (𝓞 F)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "M(" φ ", " c ")" =>
  modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽 (φ : BruhatCompactSupport C𝔽).val c
local notation "twist(" χ ", " s ")" => ideleClassNormTwist (F := F) χ s
local notation "ord(" χ ", " s ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ s
local notation "zeroTerm(" φ ", " z ")" =>
  ((ord((z).val.1.val, (z).val.2) : ℤ) : ℂ) * M(φ, twist((z).val.1.val, (z).val.2 - 1 / 2))
local notation "exteriorZeros(" τ ", " α ")" =>
  {z : {χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
    0 < ord(z.1.val, z.2) ∧ α ≤ |z.2.re - 1 / 2|}
local notation "classVolume" => (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
local notation "archTest" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
local notation "finiteTest" => ((v : V) → BruhatCompactSupport (v.adicCompletion F)ˣ)
local notation "archClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "finiteClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "finiteVolume(" v ")" =>
  (finiteLocalMultiplicativeTamagawaMeasure F v
    ((IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v).units : Set _)).toReal
local notation "finiteTerm(" v ", " b ")" =>
  ((Real.log ((v : V).asIdeal.absNorm : ℝ) / finiteVolume(v) : ℝ) : ℂ) *
    finiteConnesWeilPrincipalValue v 1 b
local notation "localTerms(" φ ", " a ", " b ")" =>
  (M(φ, twist(1, 1 / 2)) + M(φ, twist(1, -1 / 2)) -
    classVolume * ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
      ∑' v : V, finiteTerm(v, b v)))
local notation "archRestricts(" φ ", " a ")" =>
  (∀ (w : InfinitePlace F) (u : w.Completionˣ), (a w).val u = (φ).val (archClass(w) u))
local notation "finiteRestricts(" φ ", " b ")" =>
  (∀ (v : V) (u : (v.adicCompletion F)ˣ), (b v).val u = (φ).val (finiteClass(v) u))
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "stripQuot(" hα ")" =>
  spectralSobolevQuotient F (1 / 2) (hStrip(hα)) (by norm_num : (0 : ℝ) ≤ 3)
local notation "stripConv(" hα ", " φ ")" =>
  spectralConvolution (F := F) (1 / 2) (hStrip(hα)) (by norm_num : (0 : ℝ) ≤ 3) φ

/-- Paper: Theorem 12.5.1.1, p. 520 (with (12.5.1.4) and §12.3, p. 514). For a test vanishing
on the norm-one classes and a half-width α > 0, the trace of convolution on the Sobolev order 3
spectral quotient of the strip [1/2 − α, 1/2 + α], for any nuclear representative, equals the
two polar Mellin terms minus the global norm-one volume times the local principal values at all
places, whose local tests are the restrictions of the test. It mentions no zeros. It follows
from the conclusion of `traceFormula_exteriorZeros`
(`spectralStripTrace_eq_localTerms_of_exteriorZeros`), and with the kernel above it gives that
conclusion back (`traceFormula_exteriorZeros_of_spectralStripTrace`). For α ≥ 1/2 it is proved
(`spectralStripTrace_eq_localTerms_of_half_le`).
Reconstruction: Page 520 obtains the trace from the geometric side and compares it with the
spectral side (12.5.1.4). The geometric side is the decomposition (11.3.1.4), the shell vanishing
of Theorem 11.3.2.1, the S-local trace of Theorem 12.4.1.1 and the global to S-local comparison
that §12.3 announces and does not contain. The paper does not state the result of these steps
as one statement; by Definition 10.4.3.7(2), p. 473, it is this identity of the trace with the
local terms.
Deviation: The local terms run over all places. For S as on p. 520 the finite local terms off S
vanish, since the test vanishes on C¹ and on norms outside (1/T, T), so they equal the S-local
terms. The Sobolev order is fixed at s = 3, the least order at which (12.5.1.4) is stated.
Gap: The comparison of §12.3 is missing (ERRATA M25, I292, I341, I351, I369).
Nothing outside this file uses this statement; in the paper it is used on p. 520. -/
theorem spectralStripTrace_eq_localTerms (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ g : C₁, φ.val g = 0) {α : ℝ} (hα : 0 < α)
    (a : archTest) (b : finiteTest) (ha : archRestricts(φ, a)) (hb : finiteRestricts(φ, b))
    (T : nuclearEndomorphisms stripQuot(hα.le))
    (hT : T.val = stripConv(hα.le, φ)) :
    hilbertTrace T = localTerms(φ, a, b) := by
  sorry

/-- Paper: Theorem 12.5.1.1, pp. 519–520, with (12.5.1.4) and Theorem B.4.4.7, p. 623. The
conclusion of `traceFormula_exteriorZeros`, derived from the two statements of this file: the
kernel of (12.5.1.4) (`exists_projectiveKernel_stripTestAction_spectralProjection`) and the strip
trace identity (`spectralStripTrace_eq_localTerms`), by `traceFormula_exteriorZeros_of_stripTrace`.
It is no more established than those two statements. Nothing outside this file uses it. -/
theorem traceFormula_exteriorZeros_of_spectralStripTrace (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F))
    (φ : BruhatCompactSupport C𝔽) (_hφ : ∀ g : C₁, φ.val g = 0) {α : ℝ} (hα : 0 < α) :
    HasSum (fun z : exteriorZeros(τ, α) ↦ zeroTerm(φ, z)) 0 :=
  RiemannMasullo.traceFormula_exteriorZeros_of_stripTrace τ hτ
    (fun hβ φ' hφ' ↦
      exists_projectiveKernel_stripTestAction_spectralProjection φ' hφ' (s := 3) hβ le_rfl)
    (fun φ' hφ' _ hβ a b ha hb T hT ↦ spectralStripTrace_eq_localTerms φ' hφ' hβ a b ha hb T hT)
    φ hα

end StripTrace

end RiemannMasullo.Isolated
