/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import ScaleSpaceCore.BrownianDensity
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The bridge between the cosine transform and Mathlib's characteristic function

Nothing here is a blueprint node. These are the two identities that let the article's real
cosine transform `fourierCos` (the primitive of `blueprint/src/parts/02-preliminaries.tex`,
equation (2.1) read on a symmetric measure) and Mathlib's complex `charFun` be used in the same
proof.

`charFun μ ω = ∫ exp (ω x i) ∂μ` carries the **opposite** sign convention to (2.1). Every use in
this development is either sign-insensitive — uniqueness, the value `1`, continuity — or is
about a symmetric measure, where the two transforms agree and are real. That is what the second
lemma below records.

Proving campaign, chapter 2 (2026-09-09): moved here from `Skeleton/Chapter2.lean`, where the
two were stated as `Skeleton.fourierCos_eq_charFun_re` and
`Skeleton.charFun_eq_fourierCos_of_symmetric`.
-/

namespace ScaleSpace

open MeasureTheory Set

/-- The cosine transform's integrand is integrable against a finite measure: it is continuous
and bounded by `1`.

Wave 1 of the proving campaign (2026-09-09) moved this here. It was proved three times
independently — as `integrable_cos` in `SpatialLine/LatticeZero.lean`, and as
`integrable_cos_mul` in `SpatialLine/Nonvanishing.lean` and `SpatialLine/Pairing.lean`. This
file is the chapter-2 home of the elementary facts about (2.1), and it sits low enough in the
import graph for every chapter to reach it. -/
theorem integrable_cos_mul (μ : Measure ℝ) [IsFiniteMeasure μ] (ω : ℝ) :
    Integrable (fun x : ℝ => Real.cos (ω * x)) μ := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (ω * x)

/-- The sine transform's integrand is integrable against a finite measure: it is continuous and
bounded by `1`, the twin of `integrable_cos_mul` above.

Lifted here by the wave-6 merge (2026-09-10) from `SpatialLine/Pairing.lean` (chapter 4), which
had carried it since the sine half of the characteristic function was written, and from
`SpatialLine/GeneratorSignal.lean` (chapter 11), which wrote it again. This is the wave-1 remedy
applied to the other half of the pair: `integrable_cos_mul` was moved out of `Pairing.lean` for
the same reason and by the same argument. -/
theorem integrable_sin_mul (μ : Measure ℝ) [IsFiniteMeasure μ] (ω : ℝ) :
    Integrable (fun x : ℝ => Real.sin (ω * x)) μ := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (ω * x)

/-! ## Elementary facts about the cosine transform

Moved here by wave 2's merge (2026-09-09) from `SpatialLine/Nonvanishing.lean`, on wave 1's
rule: these are elementary facts about (2.1), not about `lem:nonvanishing`, so they belong in
the chapter-2 file every chapter can reach. `SpatialLine/Interfaces.lean` needs two of them for
the reverse direction of ledger A1 and must not import chapter 4. -/

@[simp] theorem fourierCos_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    fourierCos μ 0 = 1 := by
  simp [fourierCos_apply]

theorem fourierCos_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (ω : ℝ) :
    fourierCos μ ω ≤ 1 := by
  have h := integral_mono (integrable_cos_mul μ ω) (integrable_const (1 : ℝ))
    (fun x => Real.cos_le_one (ω * x))
  simpa [fourierCos_apply] using h

theorem continuous_fourierCos (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Continuous (fourierCos μ) := by
  refine continuous_of_dominated (F := fun ω x => Real.cos (ω * x)) (bound := fun _ => (1 : ℝ))
    (fun ω => (integrable_cos_mul μ ω).aestronglyMeasurable) ?_ (integrable_const 1) ?_
  · intro ω
    filter_upwards with x
    simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (ω * x)
  · filter_upwards with x
    exact (Real.continuous_cos.comp (continuous_id.mul continuous_const))

/-- **The transform of a dilated measure** is the transform at the dilated frequency.

Moved here by wave 2's merge (2026-09-09) from `MaternData.charFun_map_const_mul`, where it
was stranded in a concrete namespace: it mentions no Matérn datum, and
`SpatialLine/MainConstruction.lean` already called it across the namespace boundary. -/
theorem charFun_map_const_mul (μ : Measure ℝ) [IsFiniteMeasure μ] (c ω : ℝ) :
    charFun (μ.map (fun x => c * x)) ω = charFun μ (c * ω) := by
  have hmeas : ∀ ν : Measure ℝ, AEStronglyMeasurable
      (fun x : ℝ => Complex.exp (↑ω * ↑x * Complex.I)) ν := fun ν =>
    (Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)).aestronglyMeasurable
  calc charFun (μ.map (fun x => c * x)) ω
      = ∫ x, Complex.exp (↑ω * ↑x * Complex.I) ∂(μ.map (fun x => c * x)) := charFun_apply_real ω
    _ = ∫ x, Complex.exp (↑ω * ↑(c * x) * Complex.I) ∂μ :=
        integral_map (measurable_const_mul c).aemeasurable (hmeas _)
    _ = ∫ x, Complex.exp (↑(c * ω) * ↑x * Complex.I) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        push_cast
        ring_nf
    _ = charFun μ (c * ω) := (charFun_apply_real (c * ω)).symm

end ScaleSpace
