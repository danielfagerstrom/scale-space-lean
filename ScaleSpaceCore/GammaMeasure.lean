/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The Gamma law's Laplace transform

Four facts about Mathlib's `ProbabilityTheory.gammaMeasure`: integration against it is
integration against its density on `(0, ∞)` (`lintegral_gammaMeasure`); its Laplace transform
against `u^q e^{-su}` (`lintegral_gammaMeasure_rpow_mul_exp`, the one computation a Gamma-mixture
argument needs both for the transform and for the moments); and that it lives on the positive
axis (`gammaMeasure_Iio_zero`, `ae_pos_gammaMeasure`).

Moved from Paper V's cone export (`cone-v0.1`, `f28c066e`, `SpatialLine.MaternMixture`),
statements unchanged up to the namespace. Second demand: Paper V's `matern_gamma_mixture` and
Paper VII's `lintegral_exp_gammaMeasure`/`ae_nonneg_gammaMeasure`
(`Formalization/AffineHemigroup/MaternOrbit.lean`), the case `q = 0`, `r = 1`, both read
`lintegral_gammaMeasure_rpow_mul_exp`. Everything here is proved from Mathlib's gamma-measure and
Gaussian-integral lemmas alone.
-/

namespace ScaleSpace

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal

/-- Integration against the Gamma law is integration against its density on `(0,∞)`. -/
theorem lintegral_gammaMeasure {a r : ℝ} {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ u, g u ∂(gammaMeasure a r))
      = ∫⁻ u in Ioi (0 : ℝ),
          ENNReal.ofReal (r ^ a / Real.Gamma a * u ^ (a - 1) * Real.exp (-(r * u))) * g u := by
  have hpdfm : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  rw [gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ hpdfm hg]
  have hsplit := lintegral_add_compl (μ := (volume : Measure ℝ))
    (fun u => gammaPDF a r u * g u) (measurableSet_Iio (a := (0 : ℝ)))
  rw [compl_Iio] at hsplit
  have hneg : (∫⁻ u in Iio (0 : ℝ), gammaPDF a r u * g u) = 0 := by
    refine (setLIntegral_congr_fun measurableSet_Iio fun u hu => ?_).trans lintegral_zero
    rw [gammaPDF_of_neg hu, zero_mul]
  have hIci : (∫⁻ u in Ici (0 : ℝ), gammaPDF a r u * g u)
      = ∫⁻ u in Ioi (0 : ℝ), gammaPDF a r u * g u :=
    setLIntegral_congr Ioi_ae_eq_Ici.symm
  rw [hneg, hIci, zero_add] at hsplit
  simp only [Pi.mul_apply]
  rw [← hsplit]
  refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  rw [gammaPDF_of_nonneg (le_of_lt hu)]

/-- **The Gamma law against `u^q e^{-su}`**, the one computation both second-demand consumers'
proofs need. -/
theorem lintegral_gammaMeasure_rpow_mul_exp {a r : ℝ} (ha : 0 < a) (hr : 0 < r) {q s : ℝ}
    (hq : 0 < a + q) (hs : 0 ≤ s) :
    (∫⁻ u, ENNReal.ofReal (u ^ q * Real.exp (-(s * u))) ∂(gammaMeasure a r))
      = ENNReal.ofReal
          (r ^ a * (1 / (r + s)) ^ (a + q) * Real.Gamma (a + q) / Real.Gamma a) := by
  have hR : (0 : ℝ) < r + s := by linarith
  have hGa : (0 : ℝ) < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hmeas : Measurable fun u : ℝ => ENNReal.ofReal (u ^ q * Real.exp (-(s * u))) := by
    fun_prop
  rw [lintegral_gammaMeasure hmeas]
  have hpt : ∀ u ∈ Ioi (0 : ℝ),
      ENNReal.ofReal (r ^ a / Real.Gamma a * u ^ (a - 1) * Real.exp (-(r * u)))
          * ENNReal.ofReal (u ^ q * Real.exp (-(s * u)))
        = ENNReal.ofReal (r ^ a / Real.Gamma a
            * (u ^ ((a + q) - 1) * Real.exp (-((r + s) * u)))) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [show (a + q) - 1 = (a - 1) + q by ring, Real.rpow_add hu0,
      show -((r + s) * u) = -(r * u) + -(s * u) by ring, Real.exp_add]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt]
  have hint : IntegrableOn (fun u : ℝ => r ^ a / Real.Gamma a
      * (u ^ ((a + q) - 1) * Real.exp (-((r + s) * u)))) (Ioi (0 : ℝ)) := by
    have h0 : IntegrableOn (fun u : ℝ => r ^ a / Real.Gamma a
        * (u ^ ((a + q) - 1) * Real.exp (-(r + s) * u ^ (1 : ℝ)))) (Ioi (0 : ℝ)) :=
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (a + q) - 1) (p := 1) (b := r + s)
        (by linarith) le_rfl hR).const_mul (r ^ a / Real.Gamma a)
    refine h0.congr_fun (fun u hu => ?_) measurableSet_Ioi
    show r ^ a / Real.Gamma a * (u ^ ((a + q) - 1) * Real.exp (-(r + s) * u ^ (1 : ℝ)))
      = r ^ a / Real.Gamma a * (u ^ ((a + q) - 1) * Real.exp (-((r + s) * u)))
    rw [Real.rpow_one]
    ring_nf
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun u hu => by
      have hu0 : (0 : ℝ) < u := hu; positivity))]
  rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hq hR]
  congr 1
  field_simp

/-- The Gamma law lives on the positive axis. -/
theorem gammaMeasure_Iio_zero (a r : ℝ) : gammaMeasure a r (Iio (0 : ℝ)) = 0 := by
  rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

theorem ae_pos_gammaMeasure (a r : ℝ) : ∀ᵐ u ∂(gammaMeasure a r), 0 < u := by
  have hIic : gammaMeasure a r (Iic (0 : ℝ)) = 0 := by
    rw [gammaMeasure, withDensity_apply _ measurableSet_Iic,
      setLIntegral_congr (Iio_ae_eq_Iic (a := (0 : ℝ))).symm]
    exact lintegral_gammaPDF_of_nonpos le_rfl
  rw [ae_iff]
  convert hIic using 2
  ext u; simp

end ScaleSpace
