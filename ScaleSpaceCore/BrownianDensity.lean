/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The Brownian laws and their density

The objects `lem:bridge-exponents` is written in (`BridgeExponents`), and the elementary facts its
proof reads: `brownianLaw u = g_u` is Mathlib's `gaussianReal 0 u`, and `brownianDensity u x =
g_u(x)` its density; both are thin wrappers whose only job is to let the bridge equations be
written with `u` a real time rather than an `ℝ≥0` variance. At `u = 0` the wrapper is `δ₀`, and
for `u < 0` it is junk — every statement quantifies over `u > 0` or integrates over `(0,∞)`.

Moved from the spatial article's export (`SpatialLine.BrownianDensity`, and from
`SpatialLine.Transform`/`TransformBridge` the cosine transform `fourierCos` with the two facts
that compute it at a Gaussian, at `cone-v0.1`), statements unchanged up to the namespace. Only
what `bridge_exponents` needs moved: the mixture facts about `Measure.bind brownianLaw`, which
serve `bridge_exponents_mixture` and the Gaussian variance mixtures, stayed behind.

## The two elementary bounds

`brownianDensity_div_le` bounds `g_u(x)/u` by `16/x⁴` uniformly for `u` in `(0,1]`, which is
where the Gaussian's flatness at `u = 0` pays for a missing power of `u` in a mixture carrying
`du/u`; above `1` the density is at most `1` (`brownianDensity_le_one`).
-/

namespace ScaleSpace

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

/-! ## The cosine transform -/

/-- **(2.1) for a symmetric measure**: `μ̂(ω) = ∫ cos(ωx) μ(dx)`.

A Bochner integral of a bounded continuous function; for a finite `μ` it always converges, and
for a symmetric `μ` it is the Fourier transform of (2.1). -/
noncomputable def fourierCos (μ : Measure ℝ) (ω : ℝ) : ℝ := ∫ x, Real.cos (ω * x) ∂μ

lemma fourierCos_apply (μ : Measure ℝ) (ω : ℝ) : fourierCos μ ω = ∫ x, Real.cos (ω * x) ∂μ := rfl

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

/-- **The cosine transform of a centred Gaussian law of variance `v`**, `e^{-vω²/2}`. -/
theorem fourierCos_gaussianReal (v : NNReal) (ω : ℝ) :
    fourierCos (ProbabilityTheory.gaussianReal 0 v) ω = Real.exp (-((v : ℝ) * ω ^ 2 / 2)) := by
  rw [fourierCos_eq_charFun_re, ProbabilityTheory.charFun_gaussianReal]
  have harg : (ω : ℂ) * ((0 : ℝ) : ℂ) * Complex.I - ((v : ℝ) : ℂ) * (ω : ℂ) ^ 2 / 2
      = (((-((v : ℝ) * ω ^ 2 / 2)) : ℝ) : ℂ) := by push_cast; ring
  rw [harg, ← Complex.ofReal_exp, Complex.ofReal_re]

/-! ## The Brownian laws -/

/-- **`g_u`**, the law of Brownian motion at time `u`: the centred Gaussian of variance `u`,
with `g_0 = δ_0`. -/
noncomputable def brownianLaw (u : ℝ) : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 u.toNNReal

/-- **`g_u(x)`**, the density of `brownianLaw u` for `u > 0`. -/
noncomputable def brownianDensity (u x : ℝ) : ℝ :=
  ProbabilityTheory.gaussianPDFReal 0 u.toNNReal x

/-! ## The Brownian density, explicitly -/

/-- `g_u(x) = (2πu)^{-1/2}e^{-x²/2u}` at every positive time. -/
theorem brownianDensity_eq {u : ℝ} (hu : 0 < u) (x : ℝ) :
    brownianDensity u x = (Real.sqrt (2 * Real.pi * u))⁻¹ * Real.exp (-x ^ 2 / (2 * u)) := by
  unfold brownianDensity gaussianPDFReal
  rw [Real.coe_toNNReal _ hu.le]
  norm_num

theorem brownianDensity_nonneg (u x : ℝ) : 0 ≤ brownianDensity u x :=
  gaussianPDFReal_nonneg _ _ _

theorem measurable_brownianDensity (u : ℝ) : Measurable (brownianDensity u) := by
  unfold brownianDensity; fun_prop

theorem measurable_brownianDensity_time (x : ℝ) :
    Measurable fun u : ℝ => brownianDensity u x := by
  unfold brownianDensity gaussianPDFReal; fun_prop

theorem measurable_brownianDensity_uncurry : Measurable (Function.uncurry brownianDensity) := by
  unfold brownianDensity gaussianPDFReal Function.uncurry; fun_prop

/-- `g_u` is even. -/
theorem brownianDensity_neg (u x : ℝ) : brownianDensity u (-x) = brownianDensity u x := by
  unfold brownianDensity gaussianPDFReal; simp

theorem brownianLaw_eq_withDensity {u : ℝ} (hu : 0 < u) :
    brownianLaw u = volume.withDensity fun x => ENNReal.ofReal (brownianDensity u x) := by
  unfold brownianLaw brownianDensity
  rw [gaussianReal_of_var_ne_zero _ (by positivity)]
  rfl

/-! ## Two elementary bounds on the density -/

/-- `y² ≤ 4e^y` for `y ≥ 0`: the second-order term of the exponential series, in the form the
near-origin bound uses. -/
theorem sq_le_four_mul_exp {y : ℝ} (hy : 0 ≤ y) : y ^ 2 ≤ 4 * Real.exp y := by
  have h := Real.add_one_le_exp (y / 2)
  have h2 : Real.exp (y / 2) ^ 2 = Real.exp y := by
    rw [← Real.exp_nat_mul]; norm_num; ring_nf
  nlinarith [Real.exp_pos (y / 2), h, h2]

/-- **The near-origin bound.** `g_u(x)/u ≤ 16/x⁴` for `0 < u ≤ 1` and `x ≠ 0`.

This is what lets the mixture integrand, which carries `du/u`, be dominated on `(0,1)` by a
multiple of `k_I(u)` — the *first* integrability field of `def:causal-admissible`, which
carries no `u⁻¹`. The Gaussian's flatness at `u = 0` pays for the missing power. -/
theorem brownianDensity_div_le {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) {x : ℝ} (hx : x ≠ 0) :
    brownianDensity u x / u ≤ 16 / x ^ 4 := by
  have hpi := Real.two_le_pi
  have hx4 : (0 : ℝ) < x ^ 4 := by positivity
  have hy : (0 : ℝ) ≤ x ^ 2 / (2 * u) := by positivity
  have hpos : (0 : ℝ) < Real.exp (x ^ 2 / (2 * u)) := Real.exp_pos _
  have h := sq_le_four_mul_exp hy
  have hsq : (x ^ 2 / (2 * u)) ^ 2 = x ^ 4 / (4 * u ^ 2) := by field_simp; ring
  rw [hsq, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * u ^ 2)] at h
  have hexp : Real.exp (-x ^ 2 / (2 * u)) ≤ 16 * u ^ 2 / x ^ 4 := by
    have hinv : Real.exp (-x ^ 2 / (2 * u)) = (Real.exp (x ^ 2 / (2 * u)))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [hinv, inv_le_iff_one_le_mul₀ hpos, div_mul_eq_mul_div, le_div_iff₀ hx4]
    nlinarith [h]
  have hsqrt : u ≤ Real.sqrt (2 * Real.pi * u) := by
    have hle : u ^ 2 ≤ 2 * Real.pi * u := by nlinarith
    calc u = Real.sqrt (u ^ 2) := (Real.sqrt_sq hu0.le).symm
      _ ≤ Real.sqrt (2 * Real.pi * u) := Real.sqrt_le_sqrt hle
  have hspos : (0 : ℝ) < Real.sqrt (2 * Real.pi * u) := by
    apply Real.sqrt_pos.mpr; nlinarith
  rw [brownianDensity_eq hu0, div_le_div_iff₀ (by positivity) hx4]
  have hstep : (Real.sqrt (2 * Real.pi * u))⁻¹ * Real.exp (-x ^ 2 / (2 * u)) * x ^ 4
      ≤ (Real.sqrt (2 * Real.pi * u))⁻¹ * (16 * u ^ 2 / x ^ 4) * x ^ 4 := by
    have hmul := mul_le_mul_of_nonneg_left hexp
      (by positivity : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi * u))⁻¹)
    nlinarith [hmul]
  have hsimp : (Real.sqrt (2 * Real.pi * u))⁻¹ * (16 * u ^ 2 / x ^ 4) * x ^ 4
      = 16 * u ^ 2 / Real.sqrt (2 * Real.pi * u) := by field_simp
  rw [hsimp] at hstep
  have hfin : 16 * u ^ 2 / Real.sqrt (2 * Real.pi * u) ≤ 16 * u := by
    rw [div_le_iff₀ hspos]; nlinarith [hsqrt, hu0.le]
  linarith

/-- **The bound above the origin.** `g_u(x) ≤ 1` for `u ≥ 1`, so the mixture integrand is
dominated there by `k_I(u)/u` — the second integrability field, verbatim. -/
theorem brownianDensity_le_one {u : ℝ} (hu : 1 ≤ u) (x : ℝ) : brownianDensity u x ≤ 1 := by
  have hpi := Real.two_le_pi
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  have hspos : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * u) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    apply Real.sqrt_le_sqrt; nlinarith
  have hle : -x ^ 2 / (2 * u) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith [sq_nonneg x]
    · positivity
  have hexp : Real.exp (-x ^ 2 / (2 * u)) ≤ 1 := Real.exp_le_one_iff.mpr hle
  have hinv : (Real.sqrt (2 * Real.pi * u))⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; right; exact hspos
  rw [brownianDensity_eq hu0]
  nlinarith [Real.exp_pos (-x ^ 2 / (2 * u)),
    inv_nonneg.mpr (Real.sqrt_nonneg (2 * Real.pi * u))]

/-! ## The Gaussian jump integral -/

theorem lintegral_brownianLaw_one_sub_cos {u : ℝ} (hu : 0 ≤ u) (ω : ℝ) :
    (∫⁻ x, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂(brownianLaw u))
      = ENNReal.ofReal (1 - Real.exp (-(u * ω ^ 2 / 2))) := by
  set N := brownianLaw u with hN
  have hprob : IsProbabilityMeasure N := by rw [hN, brownianLaw]; infer_instance
  have hcos : Integrable (fun x : ℝ => Real.cos (ω * x)) N := by
    refine Integrable.mono' (integrable_const 1) (by fun_prop) (.of_forall fun x => ?_)
    simpa using Real.abs_cos_le_one (ω * x)
  have hint : Integrable (fun x : ℝ => 1 - Real.cos (ω * x)) N :=
    (integrable_const 1).sub hcos
  have hnn : ∀ᵐ x ∂N, 0 ≤ 1 - Real.cos (ω * x) :=
    .of_forall fun x => by linarith [Real.cos_le_one (ω * x)]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [integral_sub (integrable_const 1) hcos]
  have hval : (∫ x, Real.cos (ω * x) ∂N) = Real.exp (-(u * ω ^ 2 / 2)) := by
    have h1 : (∫ x, Real.cos (ω * x) ∂N) = fourierCos N ω := by rw [fourierCos_apply]
    rw [h1, hN, brownianLaw, fourierCos_gaussianReal, Real.coe_toNNReal _ hu]
  rw [hval]
  simp

/-- Integration against `g_u` is integration against its density. -/
theorem lintegral_brownianDensity {u : ℝ} (hu : 0 < u) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x, ENNReal.ofReal (brownianDensity u x) * g x) = ∫⁻ x, g x ∂(brownianLaw u) := by
  rw [brownianLaw_eq_withDensity hu,
    lintegral_withDensity_eq_lintegral_mul _ ((measurable_brownianDensity u).ennreal_ofReal) hg]
  rfl

/-- An even function integrates over the line to twice its integral over the positive axis. -/
theorem lintegral_even_eq_two_mul {g : ℝ → ℝ≥0∞} (heven : ∀ x, g (-x) = g x) :
    (∫⁻ x, g x) = 2 * ∫⁻ x in Ioi (0 : ℝ), g x := by
  have hemb : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).toMeasurableEquiv.measurableEmbedding
  have hmp : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg volume
  have hpre : (fun x : ℝ => -x) ⁻¹' (Ioi (0 : ℝ)) = Iio (0 : ℝ) := by ext x; simp
  have hIio : (∫⁻ x in Iio (0 : ℝ), g x) = ∫⁻ x in Ioi (0 : ℝ), g x := by
    have hkey := hmp.setLIntegral_comp_preimage_emb hemb g (Ioi (0 : ℝ))
    rw [hpre] at hkey
    rw [← hkey]
    exact setLIntegral_congr_fun measurableSet_Iio fun x _ => (heven x).symm
  have hsplit := lintegral_add_compl (μ := (volume : Measure ℝ)) g
    (measurableSet_Iio (a := (0 : ℝ)))
  rw [compl_Iio] at hsplit
  have hIci : (∫⁻ x in Ici (0 : ℝ), g x) = ∫⁻ x in Ioi (0 : ℝ), g x :=
    setLIntegral_congr Ioi_ae_eq_Ici.symm
  rw [hIio, hIci] at hsplit
  rw [← hsplit]
  ring

/-- **The folded Gaussian jump integral**, `2∫₀^∞(1 - cos ωx)g_u(x)dx = 1 - e^{-uω²/2}`.

This is the identity the exponent computation runs on: the folding by `2` is exactly the
folding `k = 2xν₂` of `eq:bridge-profile`, so the factor cancels. -/
theorem lintegral_Ioi_brownianDensity_one_sub_cos {u : ℝ} (hu : 0 < u) (ω : ℝ) :
    (∫⁻ x in Ioi (0 : ℝ), 2 * ENNReal.ofReal ((1 - Real.cos (ω * x)) * brownianDensity u x))
      = ENNReal.ofReal (1 - Real.exp (-(u * ω ^ 2 / 2))) := by
  have hg : Measurable fun x : ℝ => ENNReal.ofReal (1 - Real.cos (ω * x)) := by fun_prop
  have hfull : (∫⁻ x, ENNReal.ofReal ((1 - Real.cos (ω * x)) * brownianDensity u x))
      = ENNReal.ofReal (1 - Real.exp (-(u * ω ^ 2 / 2))) := by
    rw [← lintegral_brownianLaw_one_sub_cos hu.le ω, ← lintegral_brownianDensity hu _ hg]
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.ofReal_mul (brownianDensity_nonneg u x), mul_comm]
  have heven : ∀ x : ℝ, ENNReal.ofReal ((1 - Real.cos (ω * -x)) * brownianDensity u (-x))
      = ENNReal.ofReal ((1 - Real.cos (ω * x)) * brownianDensity u x) := by
    intro x
    rw [brownianDensity_neg, mul_neg, Real.cos_neg]
  rw [← hfull, lintegral_even_eq_two_mul heven, ← lintegral_const_mul' _ _ (by norm_num)]

end ScaleSpace
