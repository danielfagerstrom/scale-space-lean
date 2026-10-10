/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The integral of `e^{-cu}` over the half-line

Home: none (an elementary computation whose proof is the whole content: `∫ e^{-cu} du = c⁻¹` from
Mathlib's `integral_exp_mul_Ioi` alone, needing no citation beyond itself)

`∫₀^∞ e^{-cu} du = c⁻¹` for `c > 0`, as a lower Lebesgue integral valued in `ℝ≥0∞`
(`lintegral_Ioi_exp_neg_mul`), with the integrability of `e^{-pu}` on `(0,∞)` it reads
(`integrableOn_exp_neg_Ioi_zero`).

Moved by Q-0364, statements and proofs verbatim up to the namespace: `lintegral_Ioi_exp_neg_mul`
from Paper V's cone export `v0.1` (`SpatialLine/ThorinBridgeOnto.lean`) and
`integrableOn_exp_neg_Ioi_zero` from `SpatialLine/Frullani.lean` (identical on development main).
Second demand: Paper VII's `lintegral_exp_neg_mul_Ioi` (`Formalization/AffineHemigroup/
MaternOrbit.lean`), the same identity with the value written `1 / t` (`spatial-hemigroup-affine`,
`records/formalization/SECOND-DEMAND-candidates.md` § A6).
-/

namespace ScaleSpace

open MeasureTheory Set
open scoped ENNReal

/-- `e^{-px}` is integrable on `(0,∞)`. -/
theorem integrableOn_exp_neg_Ioi_zero {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun x : ℝ => Real.exp (-(p * x))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 0) (b := p)
    (by norm_num) le_rfl hp
  simpa [Real.rpow_one, Real.rpow_zero, neg_mul] using h

/-- `∫₀^∞ e^{-cu}du = c⁻¹`, `ℝ≥0∞`-valued. -/
theorem lintegral_Ioi_exp_neg_mul {c : ℝ} (hc : 0 < c) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(c * u)))) = ENNReal.ofReal c⁻¹ := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi_zero hc)
    (.of_forall fun _ => (Real.exp_pos _).le)]
  congr 1
  have h := integral_exp_mul_Ioi (a := -c) (by linarith) 0
  simp only [mul_zero, Real.exp_zero] at h
  calc (∫ u in Ioi (0 : ℝ), Real.exp (-(c * u))) = ∫ u in Ioi (0 : ℝ), Real.exp (-c * u) := by
        refine integral_congr_ae (.of_forall fun u => ?_)
        simp only [neg_mul]
    _ = c⁻¹ := by rw [h]; field_simp

end ScaleSpace
