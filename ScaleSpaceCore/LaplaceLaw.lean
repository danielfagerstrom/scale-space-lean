/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# The Laplace law on the line

Home: line/cone:prop:corner-generators

The Laplace kernel of range `θ`, `laplaceDensity θ x = (2θ)⁻¹ e^{-|x|/θ}`, and the probability
measure `laplaceLaw θ` it defines: nonnegative and measurable (`laplaceDensity_nonneg`,
`measurable_laplaceDensity`), integrable (`integrable_laplaceDensity`, through its two half-line
pieces), of integral one (`integral_laplaceDensity`), and a probability measure
(`isProbabilityMeasure_laplaceLaw`).

The mass is computed from the one-sided exponential density `expoDensity` (`t⁻¹ e^{-x/t}` on
`(0,∞)`): away from the origin the Laplace density is the half-sum of `expoDensity t` and its
reflection (`laplaceDensity_eq_half_add`), so its integral is the average of two integrals equal to
one. That is the proof Paper V has, and `expoDensity` with its four lemmas is what it reads.

Moved by Q-0364, statements and proofs verbatim up to the namespace, from Paper V's sources:
`laplaceDensity` from `SpatialLine/CornerDefs.lean`, `laplaceLaw` from `SpatialLine/Corners.lean`,
and `laplaceDensity_nonneg`, `continuous_laplaceDensity`, `measurable_laplaceDensity`,
`integrableOn_laplaceDensity_Ioi`, `integrableOn_laplaceDensity_Iic`, `integrable_laplaceDensity`
from `SpatialLine/GeneratorMatern.lean` (all three in the cone export `v0.1`, identical on
development main); `expoDensity` and its lemmas, `laplaceDensity_eq_half_add`,
`laplaceDensity_ae_eq`, `integral_laplaceDensity` and `isProbabilityMeasure_laplaceLaw` from
`SpatialLine/LagKernels.lean` (development repository `spatial-hemigroup-scale-space`, main at
`387424ad8f9476af282b1fe9618aab2e9334bbd7`; on development main only, not at a release tag).
In `isProbabilityMeasure_laplaceLaw` the integrability of the density is read from
`integrable_laplaceDensity` above, where Paper V re-derives it in a private lemma from the same
half-sum; the statement is the same.

Second demand: Paper V (`prop:corner-generators`, the Lag kernels) and Paper VII
(`Formalization/AffineHemigroup/Defs/PaperVI.lean`, `RecursionHelmholtz.lean`), which defines the
same density as `(2t)⁻¹ e^{-|x|/t}` (`-|x|/t` against Paper V's `-(|x|/t)`) and proves the same
lemmas (`spatial-hemigroup-affine`, `records/formalization/SECOND-DEMAND-candidates.md` § A5).
Paper VII's `charFun_laplaceLaw`, to its own `fourierLine`, differs from Paper V's closed form and
is not moved. The rest of Paper V's Laplace material (`laplaceDensity_neg`, `laplaceDensity_dilate`,
`mconv_laplaceLaw`, the jet lemmas, `expoLaw`) has no second demand and stays there.
-/

namespace ScaleSpace

open MeasureTheory Set Filter
open scoped ENNReal Topology

private theorem integral_neg_arg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (g : ℝ → E) : ∫ x : ℝ, g (-x) = ∫ x : ℝ, g x := by
  have A : MeasurableEmbedding fun x : ℝ => -x :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have h := A.integral_map (μ := (volume : Measure ℝ)) g
  rw [Measure.map_neg_eq_self (volume : Measure ℝ)] at h
  exact h.symm

/-- `x ≠ 0` almost everywhere on the line. -/
private theorem ae_ne_zero : ∀ᵐ x : ℝ, x ≠ 0 := by
  have h0 : (volume : Measure ℝ) {(0 : ℝ)} = 0 := by simp
  filter_upwards [MeasureTheory.compl_mem_ae_iff.2 h0] with x hx
  simpa using hx

/-! ## The Laplace kernel -/

/-- The Laplace kernel of range `θ`: `(2θ)^{-1}e^{-|x|/θ}`. -/
noncomputable def laplaceDensity (θ x : ℝ) : ℝ := (2 * θ)⁻¹ * Real.exp (-(|x| / θ))

/-- The Laplace law of range `θ`. -/
noncomputable def laplaceLaw (θ : ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (laplaceDensity θ x)

/-- The Laplace density is nonnegative. -/
theorem laplaceDensity_nonneg {θ : ℝ} (hθ : 0 < θ) (x : ℝ) : 0 ≤ laplaceDensity θ x := by
  rw [laplaceDensity]; positivity

/-- The Laplace density is continuous. -/
theorem continuous_laplaceDensity (θ : ℝ) : Continuous (laplaceDensity θ) := by
  unfold laplaceDensity; fun_prop

/-- The Laplace density is measurable. -/
theorem measurable_laplaceDensity (θ : ℝ) : Measurable (laplaceDensity θ) :=
  (continuous_laplaceDensity θ).measurable

/-- The Laplace density is integrable on the positive half-line. -/
theorem integrableOn_laplaceDensity_Ioi {θ : ℝ} (hθ : 0 < θ) :
    IntegrableOn (laplaceDensity θ) (Ioi (0 : ℝ)) := by
  have hneg : -θ⁻¹ < 0 := by simp [hθ]
  have h : IntegrableOn (fun y : ℝ => (2 * θ)⁻¹ * Real.exp (-θ⁻¹ * y)) (Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_Ioi hneg 0).const_mul _
  refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
  have hy0 : (0 : ℝ) < y := hy
  rw [laplaceDensity, abs_of_pos hy0]
  field_simp

/-- The Laplace density is integrable on the negative half-line. -/
theorem integrableOn_laplaceDensity_Iic {θ : ℝ} (hθ : 0 < θ) :
    IntegrableOn (laplaceDensity θ) (Iic (0 : ℝ)) := by
  have hpos : (0 : ℝ) < θ⁻¹ := by positivity
  have h : IntegrableOn (fun y : ℝ => (2 * θ)⁻¹ * Real.exp (θ⁻¹ * y)) (Iic (0 : ℝ)) :=
    (integrableOn_exp_mul_Iic hpos 0).const_mul _
  refine h.congr_fun (fun y hy => ?_) measurableSet_Iic
  have hy0 : y ≤ 0 := hy
  rw [laplaceDensity, abs_of_nonpos hy0]
  field_simp

/-- The Laplace density is integrable on the line. -/
theorem integrable_laplaceDensity {θ : ℝ} (hθ : 0 < θ) : Integrable (laplaceDensity θ) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact (integrableOn_laplaceDensity_Iic hθ).union (integrableOn_laplaceDensity_Ioi hθ)

/-! ## The one-sided exponential density, and the mass of the Laplace law -/

/-- **`Expo_+(t)`'s density**: `t^{-1}e^{-x/t}` on `(0,∞)`, zero elsewhere. -/
noncomputable def expoDensity (t x : ℝ) : ℝ :=
  Set.indicator (Ioi (0 : ℝ)) (fun y => t⁻¹ * Real.exp (-(y / t))) x

theorem expoDensity_def (t : ℝ) :
    expoDensity t = Set.indicator (Ioi (0 : ℝ)) (fun y => t⁻¹ * Real.exp (-(y / t))) := rfl

theorem expoDensity_nonneg {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 ≤ expoDensity t x := by
  rw [expoDensity_def]
  refine Set.indicator_nonneg (fun y _ => ?_) x
  positivity

theorem integrable_expoDensity {t : ℝ} (ht : 0 < t) : Integrable (expoDensity t) := by
  rw [expoDensity_def, integrable_indicator_iff measurableSet_Ioi]
  refine Integrable.const_mul ?_ _
  have h := exp_neg_integrableOn_Ioi (0 : ℝ) (b := t⁻¹) (by positivity)
  refine h.congr_fun (fun y _ => ?_) measurableSet_Ioi
  show Real.exp (-t⁻¹ * y) = Real.exp (-(y / t))
  rw [neg_mul, ← div_eq_inv_mul]

theorem integral_expoDensity {t : ℝ} (ht : 0 < t) : ∫ x, expoDensity t x = 1 := by
  have h := integral_comp_mul_left_Ioi (fun y : ℝ => Real.exp (-y)) 0
    (b := t⁻¹) (by positivity)
  rw [mul_zero, integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one, inv_inv] at h
  have hI : ∫ x in Ioi (0 : ℝ), Real.exp (-(x / t)) = t := by
    refine Eq.trans ?_ h
    refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
    rw [div_eq_inv_mul]
  rw [expoDensity_def, integral_indicator measurableSet_Ioi, integral_const_mul, hI,
    inv_mul_cancel₀ ht.ne']

theorem integrable_expoDensity_neg {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => expoDensity t (-x)) := by
  have A : MeasurableEmbedding fun x : ℝ => -x :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have h := integrable_expoDensity ht
  rw [← Measure.map_neg_eq_self (volume : Measure ℝ)] at h
  exact (A.integrable_map_iff).1 h

/-- The Laplace density is the half-sum of the one-sided exponential density and its
reflection, away from the origin. -/
theorem laplaceDensity_eq_half_add (t : ℝ) {x : ℝ} (hx : x ≠ 0) :
    laplaceDensity t x = 2⁻¹ * (expoDensity t x + expoDensity t (-x)) := by
  rcases hx.lt_or_gt with h | h
  · have hx' : x ∉ Ioi (0 : ℝ) := by simpa using h.le
    have hnx : (-x) ∈ Ioi (0 : ℝ) := by simpa using h
    rw [expoDensity_def, Set.indicator_of_notMem hx', Set.indicator_of_mem hnx, zero_add,
      laplaceDensity, abs_of_neg h, mul_inv, mul_assoc]
  · have hx' : x ∈ Ioi (0 : ℝ) := h
    have hnx : (-x) ∉ Ioi (0 : ℝ) := by simpa using h.le
    rw [expoDensity_def, Set.indicator_of_mem hx', Set.indicator_of_notMem hnx, add_zero,
      laplaceDensity, abs_of_pos h, mul_inv, mul_assoc]

theorem laplaceDensity_ae_eq (t : ℝ) :
    laplaceDensity t =ᵐ[volume] fun x : ℝ => 2⁻¹ * (expoDensity t x + expoDensity t (-x)) := by
  filter_upwards [ae_ne_zero] with x hx using laplaceDensity_eq_half_add t hx

theorem integral_laplaceDensity {t : ℝ} (ht : 0 < t) : ∫ x, laplaceDensity t x = 1 := by
  rw [integral_congr_ae (laplaceDensity_ae_eq t), integral_const_mul,
    integral_add (integrable_expoDensity ht) (integrable_expoDensity_neg ht),
    integral_neg_arg (fun x : ℝ => expoDensity t x), integral_expoDensity ht]
  norm_num

theorem isProbabilityMeasure_laplaceLaw {t : ℝ} (ht : 0 < t) :
    IsProbabilityMeasure (laplaceLaw t) := by
  constructor
  rw [laplaceLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_laplaceDensity ht)
      (by filter_upwards [laplaceDensity_ae_eq t] with x hx
          rw [hx]
          have := expoDensity_nonneg ht x
          have := expoDensity_nonneg ht (-x)
          positivity),
    integral_laplaceDensity ht, ENNReal.ofReal_one]

end ScaleSpace
