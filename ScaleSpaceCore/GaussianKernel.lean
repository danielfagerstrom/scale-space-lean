/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import ScaleSpaceCore.BrownianDensity

/-!
# The Gaussian kernel `u ↦ N(0, uI_d)` is measurable

Paper VII (`spatial-hemigroup-affine`) mixes multivariate Gaussians over a variance law,
`ρ.bind (gaussVar d)` with `gaussVar d u = multivariateGaussian 0 (u • 1)`; `Measure.bind` of a
non-measurable kernel is `0`, so every such mixture needs `measurable_gaussVar`,
`Measurable fun u : ℝ => multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (u • 1)`. This is
that statement, in Mathlib's types (RELEASES case (a)): second demand is Paper VII's use and
(not filed) the line's Gaussian variance mixtures, of which this is the `ℝ^d` generalization with
the line an instance (SSL-9,
`spatial-hemigroup-affine/records/formalization/SECOND-DEMAND.md` § 6).

The proof identifies `CFC.sqrt (u • 1) = Real.sqrt u • 1` for every `u : ℝ`, including `u < 0`:
Mathlib's junk convention for `CFC.sqrt` off the positive-semidefinite cone (`0`) and `Real.sqrt`'s
junk convention off the nonnegative reals (`0`) agree, so the identity needs no side condition.
This turns `multivariateGaussian 0 (u • 1)` into the pushforward of the fixed measure `stdGaussian`
by the jointly continuous map `(u, x) ↦ Real.sqrt u • x`, and measurability of the kernel follows
from the general fact that pushing a fixed measure forward along a jointly measurable family is
measurable in the parameter (`Measurable.map_prodMk_left` composed with `Measure.measurable_map`).

At `d = 1`, `EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] ℝ` identifies `multivariateGaussian 0 (u • 1)` with
`ProbabilityTheory.gaussianReal 0 u.toNNReal`, this module's `ScaleSpace.brownianLaw u`
(`BrownianDensity`); the identification is not formalized here; `measurable_brownianDensity_time`'s
cousin `Measurable fun u : ℝ => brownianLaw u` is immediate from `measurable_gaussVar` the same way
(`gaussianReal 0 u.toNNReal` is `gaussianReal`'s own junk convention off `u ≥ 0`, matching
`brownianLaw`'s doc comment).
-/

namespace ScaleSpace

open MeasureTheory ProbabilityTheory

variable {d : ℕ}

/-- **The square root of a scalar multiple of the identity matrix**, for every real scalar
`u`, including `u < 0`. `CFC.sqrt`'s junk value off the positive-semidefinite cone (`0`) and
`Real.sqrt`'s junk value off the nonnegative reals (`0`) agree, so no side condition on `u` is
needed. -/
theorem sqrt_smul_one_eq (d : ℕ) (u : ℝ) :
    CFC.sqrt (u • (1 : Matrix (Fin d) (Fin d) ℝ)) = Real.sqrt u • 1 := by
  by_cases hd : IsEmpty (Fin d)
  · ext i j
    exact hd.elim i
  rw [not_isEmpty_iff] at hd
  rcases le_or_lt 0 u with hu | hu
  · have hS : (0 : Matrix (Fin d) (Fin d) ℝ) ≤ u • 1 :=
      Matrix.nonneg_iff_posSemidef.mpr (Matrix.PosSemidef.one.smul hu)
    have hT : (0 : Matrix (Fin d) (Fin d) ℝ) ≤ Real.sqrt u • 1 :=
      Matrix.nonneg_iff_posSemidef.mpr (Matrix.PosSemidef.one.smul (Real.sqrt_nonneg u))
    refine (CFC.sqrt_eq_iff _ _ hS hT).mpr ?_
    rw [smul_mul_smul_comm, mul_one, Real.mul_self_sqrt hu]
  · have hnS : ¬ (0 : Matrix (Fin d) (Fin d) ℝ) ≤ u • 1 := by
      rw [Matrix.nonneg_iff_posSemidef]
      intro hPSD
      have hi := hPSD.diag_nonneg (i := hd.some)
      rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hi
      exact absurd hi (not_le.mpr hu)
    rw [CFC.sqrt_of_not_nonneg hnS, Real.sqrt_eq_zero_of_nonpos hu.le, zero_smul]

/-- **The multivariate Gaussian `N(0, uI_d)` is the pushforward of the standard Gaussian by
scaling**, for every real `u`, with `Real.sqrt`'s own junk convention off `u < 0` doing the work
of `multivariateGaussian`'s junk convention there: both sides are `dirac 0`. -/
theorem multivariateGaussian_zero_smul_one (d : ℕ) (u : ℝ) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (u • 1) =
      (stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun x => Real.sqrt u • x) := by
  rw [multivariateGaussian, sqrt_smul_one_eq]
  congr 1
  ext x
  rw [zero_add, map_smul, ContinuousLinearMap.smul_apply, map_one, ContinuousLinearMap.one_apply]

/-- **`u ↦ N(0, uI_d)` is measurable**, Paper VII's `measurable_gaussVar` in Mathlib's types
(`gaussVar d u = multivariateGaussian 0 (u • 1)`), `d` arbitrary. -/
theorem measurable_multivariateGaussian_zero_smul_one (d : ℕ) :
    Measurable fun u : ℝ => multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (u • 1) := by
  simp_rw [multivariateGaussian_zero_smul_one]
  have hcont : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin d) => Real.sqrt p.1 • p.2 :=
    (Real.continuous_sqrt.comp continuous_fst).smul continuous_snd
  have hmap : Measurable fun μ : Measure (ℝ × EuclideanSpace ℝ (Fin d)) =>
      μ.map (fun p : ℝ × EuclideanSpace ℝ (Fin d) => Real.sqrt p.1 • p.2) :=
    Measure.measurable_map _ hcont.measurable
  have hprod : Measurable fun u : ℝ =>
      (stdGaussian (EuclideanSpace ℝ (Fin d))).map (Prod.mk u) :=
    Measurable.map_prodMk_left
  have := hmap.comp hprod
  simpa [Measure.map_map hcont.measurable measurable_prodMk_left] using this

end ScaleSpace
