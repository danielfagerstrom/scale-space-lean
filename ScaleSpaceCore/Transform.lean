/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# The transform side on the line: symmetry, cosine transform, exponent, Laplace transform

Home: none (vocabulary, not a blueprint node of its own: the cascade-family vocabulary and the
kernel constructor that read on it are stated in `line:def:cascade-family`
(`ScaleSpaceCore.Family`) and `line:thm:main-characterization` (`ScaleSpaceCore.Construction`))

Moved by Q-0301 from Paper V's `SpatialLine/Transform.lean` and `SpatialLine/TransformBridge.lean`
at `v0.1`, statements verbatim up to the namespace. The cascade-family vocabulary
(`ScaleSpaceCore.Family`) and the kernel constructor (`ScaleSpaceCore.Construction`) are stated in
these, and a second spatial module (Paper VII) states its classification hypotheses in them.

## The primary object is the *cosine* transform

The Fourier transform `μ̂(ω) = ∫ e^{-iωx} μ(dx)` of a symmetric `μ` is real:
`μ̂(ω) = ∫ cos(ωx) μ(dx)`. Every kernel of a reflection-symmetric cascade family is symmetric, and
every statement about a kernel's transform is a statement about a *real* number — its sign, its
logarithm, its monotonicity. So `fourierCos` is the primitive, a Bochner integral of a bounded
continuous function against a finite measure, hence unconditionally defined.

Mathlib's `charFun μ ω = ∫ exp (⟪x,ω⟫ * I) ∂μ` is the complex transform with the *opposite* sign
convention. For symmetric measures the two agree and both are real, which is what
`charFun_eq_fourierCos_of_symmetric` records; `fourierCos_eq_charFun_re` holds for every finite
measure.

## The exponent

`-log μ̂` is the quantity a cascade makes additive. It is defined for every finite measure and is
junk (`Real.log` of a nonpositive number is `0`) where the transform is not positive; the
positivity is a hypothesis of the statements that need it, not part of the definition.

## The Laplace transform

`laplaceL`, an `ℝ≥0∞`-valued `lintegral`, so no integrability side condition is needed. Moved by
Q-0360 from Paper V's `SpatialLine/Transform.lean` at the cone export's `v0.1`, statement verbatim
up to the namespace: Paper VII's `lem:bernstein-triplet-unique` is the second consumer, through
`laplace_uniqueness_locally_finite` (`ScaleSpaceCore.LaplaceUniqueness`). Paper I's verbatim twin
`Hemigroup.laplaceL` stays in Paper I, which is frozen (Q-0182).

## Two small additions (Q-0364)

`isSymmetric_dirac_zero` (the point mass at the origin is symmetric), from Paper V's development
repository (`SpatialLine/PolyaFrequency.lean`, main at `387424ad8f9476af282b1fe9618aab2e9334bbd7`),
and `one_sub_cos_le` (`1 - cos(ωv) ≤ (2 + ω²)(1 ∧ v²)`), from Paper V's cone export `v0.1`
(`SpatialLine/Symbol.lean`), statements and proofs verbatim up to the namespace. Second demand:
Paper VII's `isSymmetric_dirac_zero` (`MarginalFamily`, an identical statement) and
`one_sub_cos_mul_le` (`SimilarityLine`, the same bound with `ω`, `v` named `τ`, `r` and the
factors of the product and of the minimum written in the other order).

## What stayed behind

Paper V's `IsFolded` has since moved to `ScaleSpaceCore.SDProfile` (Q-0302). The rest of
`TransformBridge` (the sine integrand, `charFun_add_measure`, `continuous_fourierCos`,
`fourierCos_gaussianReal`, …) has no second demand yet and stays in Paper V.
-/

namespace ScaleSpace

open MeasureTheory Set
open scoped ENNReal

/-! ## Symmetry -/

/-- A measure on the line is *symmetric* when it is invariant under `x ↦ -x`. The blueprint's
`R μ = μ`, with `R` extended to measures as the pushforward. -/
def IsSymmetric (μ : Measure ℝ) : Prop := μ.map (fun x => -x) = μ

/-- The point mass at the origin is symmetric. -/
theorem isSymmetric_dirac_zero : IsSymmetric (Measure.dirac (0 : ℝ)) := by
  rw [IsSymmetric, Measure.map_dirac' measurable_neg]
  norm_num

/-! ## The cosine transform -/

/-- **The Fourier transform of a symmetric measure**: `μ̂(ω) = ∫ cos(ωx) μ(dx)`.

A Bochner integral of a bounded continuous function; for a finite `μ` it always converges, and
for a symmetric `μ` it is the Fourier transform. -/
noncomputable def fourierCos (μ : Measure ℝ) (ω : ℝ) : ℝ := ∫ x, Real.cos (ω * x) ∂μ

lemma fourierCos_apply (μ : Measure ℝ) (ω : ℝ) : fourierCos μ ω = ∫ x, Real.cos (ω * x) ∂μ := rfl

/-- **The exponent `g(ω) = -log μ̂(ω)`**, the quantity a cascade makes additive.

Unconditional, hence junk where `μ̂ ≤ 0`; every statement that reads `exponent` as `-log` of a
positive number says so in its hypotheses. -/
noncomputable def exponent (μ : Measure ℝ) (ω : ℝ) : ℝ := -Real.log (fourierCos μ ω)

lemma exponent_apply (μ : Measure ℝ) (ω : ℝ) :
    exponent μ ω = -Real.log (fourierCos μ ω) := rfl

/-! ## The bridge to Mathlib's characteristic function -/

/-- The transform of `δ₀` is `1` at every frequency. -/
@[simp] theorem fourierCos_dirac_zero (ω : ℝ) :
    fourierCos (Measure.dirac (0 : ℝ)) ω = 1 := by
  rw [fourierCos_apply, integral_dirac]
  simp

/-- The integrand of `charFun` is integrable against a finite measure: it is continuous of
constant modulus `1`. -/
theorem integrable_charFun_integrand (μ : Measure ℝ) [IsFiniteMeasure μ] (ω : ℝ) :
    Integrable (fun x : ℝ => Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I)) μ := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I)) μ := by
    fun_prop
  refine ⟨hmeas, ?_⟩
  have hbound : ∀ x : ℝ, ‖Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I)‖ ≤ ‖(1 : ℝ)‖ := by
    intro x
    have : ((ω : ℂ) * (x : ℂ)) = ((ω * x : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
    simp
  exact (hasFiniteIntegral_const (1 : ℝ)).mono (Filter.Eventually.of_forall hbound)

/-- **The cosine transform is the real part of the characteristic function.**

`fourierCos μ ω = ∫ cos(ωx) ∂μ` and `charFun μ ω = ∫ exp(ωx i) ∂μ`, and `re` commutes with the
Bochner integral of an integrable function. -/
theorem fourierCos_eq_charFun_re (μ : Measure ℝ) [IsFiniteMeasure μ] (ω : ℝ) :
    fourierCos μ ω = (charFun μ ω).re := by
  rw [charFun_apply_real, ← RCLike.re_to_complex,
    ← integral_re (integrable_charFun_integrand μ ω), fourierCos_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hx : ((ω : ℂ) * (x : ℂ)) = ((ω * x : ℝ) : ℂ) := by push_cast; ring
  simp only [RCLike.re_to_complex, hx, Complex.exp_ofReal_mul_I_re]

/-- **For a symmetric finite measure the characteristic function is real**, and equal to the
cosine transform; so the sign convention is immaterial wherever a symmetric measure's transform
is read.

The imaginary part is `∫ sin(ωx) ∂μ`, which vanishes because `μ` is invariant under `x ↦ -x`
and `sin` is odd. -/
theorem charFun_eq_fourierCos_of_symmetric {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hsym : IsSymmetric μ) (ω : ℝ) :
    charFun μ ω = (fourierCos μ ω : ℂ) := by
  have hneg : Measurable fun x : ℝ => -x := measurable_neg
  -- The imaginary part is the integral of an odd function against a symmetric measure.
  have him : (charFun μ ω).im = 0 := by
    have hint := integrable_charFun_integrand μ ω
    have h1 : (charFun μ ω).im = ∫ x, Real.sin (ω * x) ∂μ := by
      rw [charFun_apply_real, ← RCLike.im_to_complex, ← integral_im hint]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      have hx : ((ω : ℂ) * (x : ℂ)) = ((ω * x : ℝ) : ℂ) := by push_cast; ring
      simp only [RCLike.im_to_complex, hx, Complex.exp_ofReal_mul_I_im]
    -- Substituting `x ↦ -x` fixes `μ` and negates the integral.
    have h2 : ∫ x, Real.sin (ω * x) ∂μ = ∫ x, Real.sin (ω * (-x)) ∂μ := by
      conv_lhs => rw [← hsym]
      rw [integral_map hneg.aemeasurable (by fun_prop)]
    have h3 : ∫ x, Real.sin (ω * (-x)) ∂μ = -∫ x, Real.sin (ω * x) ∂μ := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp [mul_neg, Real.sin_neg]
    have h4 : ∫ x, Real.sin (ω * x) ∂μ = -∫ x, Real.sin (ω * x) ∂μ := h2.trans h3
    rw [h1]
    linarith
  have hre : (charFun μ ω).re = fourierCos μ ω := (fourierCos_eq_charFun_re μ ω).symm
  exact Complex.ext (by simpa using hre) (by simpa using him)

/-! ## The truncation of `1 - cos` -/

/-- `1 - cos(ωv) ≤ (2 + ω²)(1 ∧ v²)`: the truncation both regimes of the cosine obey. -/
theorem one_sub_cos_le (ω v : ℝ) : 1 - Real.cos (ω * v) ≤ (2 + ω ^ 2) * min 1 (v ^ 2) := by
  rcases le_or_gt (v ^ 2) 1 with hv | hv
  · rw [min_eq_right hv]
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := ω * v), sq_nonneg ω, sq_nonneg v]
  · rw [min_eq_left hv.le]
    nlinarith [Real.neg_one_le_cos (ω * v), sq_nonneg ω]

/-! ## The Laplace transform -/

/-- The Laplace transform of a measure carried by the half-line, valued in `ℝ≥0∞`.

twin: `Hemigroup.laplaceL`, verbatim. -/
noncomputable def laplaceL (m : Measure ℝ) (τ : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, ENNReal.ofReal (Real.exp (-(τ * u))) ∂m

lemma laplaceL_apply (m : Measure ℝ) (τ : ℝ) :
    laplaceL m τ = ∫⁻ u, ENNReal.ofReal (Real.exp (-(τ * u))) ∂m := rfl

end ScaleSpace
