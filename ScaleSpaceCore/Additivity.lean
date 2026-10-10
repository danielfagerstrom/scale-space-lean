/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import ScaleSpaceCore.Cascade
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# `lem:additivity`: the cascade, at the level of measures and of exponents

Home: line:lem:additivity

Blueprint: `blueprint/src/parts/05-cascade.tex`, `lem:additivity`.

Chapter 5 opens by transporting (A6) down two levels. `lem:convolution-representation` turned
the operators into measures — supplied here as the hypothesis `IsKernelFamily` — and
`Cascade` reads the cascade law off it as an identity of measures; the
transform turns convolution into multiplication, and `-log` turns multiplication into addition.
What comes out is a two-parameter family of exponents additive along the cascade, hence the
difference of the single one-parameter function `G(t, ω) = g_{0,t}(ω)`.

twin: `Hemigroup.CascadeCore.additivity`, bundled the same way so the blueprint node has one
Lean name for its ten clauses. The one place the two developments part company is the
positivity of the transform: on the half-line it is free (`laplace_pos_of_prob`), here it is
`lem:nonvanishing` and costs the whole of `Cascade`.

`G` is not given a name. The blueprint's `G(t,ω) := g_{0,t}(ω)` is written inline as
`exponent (μ 0 t) ω` throughout: it is an abbreviation in the text, and naming a function of a
hypothesised object in the `sorry`-free library would be vocabulary without a consumer.

## Provenance

Moved by Q-0305 from Paper V's `SpatialLine/Additivity.lean` (the public cone export,
`cone-v0.1`, commit `f28c066e`) for the line classification (`MainAnalysis`,
`MainConstruction`): only the declarations those theorems reach, with statements and
proofs unchanged up to the namespace. Blueprint labels are Paper V's.
-/

namespace ScaleSpace

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal Topology

/-! ## Elementary properties of the cosine transform

Four of the five this file proved — continuity, evenness, the value at `0` and the bound `≤ 1` —
were proved again in `Nonvanishing` for `lem:nonvanishing`, and the wave-1 merge
(2026-09-09) kept that copy and deleted these. Only the absolute-value form below is this file's
own.
-/

lemma abs_fourierCos_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (ω : ℝ) :
    |fourierCos ν ω| ≤ 1 := by
  calc |fourierCos ν ω| = ‖∫ x, Real.cos (ω * x) ∂ν‖ := by
        rw [fourierCos_apply, Real.norm_eq_abs]
    _ ≤ ∫ x, ‖Real.cos (ω * x)‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ _, (1:ℝ) ∂ν :=
        integral_mono (integrable_cos_mul ν ω).norm (integrable_const 1)
          (fun x => by simpa using Real.abs_cos_le_one (ω * x))
    _ = 1 := by simp

/-! ## The exponents -/

variable {Fam : PreCascadeCore} {μ : ℝ → ℝ → Measure ℝ}

/-- **`g_{r,t} = g_{r,s} + g_{s,t}`.** Convolution becomes multiplication under the transform and
multiplication becomes addition under `-log`, which is legitimate exactly because the transform
of a kernel is strictly positive (`kernel_transform_pos`). -/
theorem exponent_add (hker : IsKernelFamily Fam.Φ μ) {r s t : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s)
    (hst : s ≤ t) (ω : ℝ) :
    exponent (μ r t) ω = exponent (μ r s) ω + exponent (μ s t) ω := by
  have h1 := kernel_transform_pos hker hr hrs ω
  have h2 := kernel_transform_pos hker (hr.trans hrs) hst ω
  simp only [exponent_apply, fourierCos_kernel_mul_comm hker hr hrs hst ω]
  rw [Real.log_mul h2.ne' h1.ne']
  ring

/-- **`g_{t,t} = 0`.** -/
theorem exponent_self (hker : IsKernelFamily Fam.Φ μ) {t : ℝ} (ht : 0 ≤ t) (ω : ℝ) :
    exponent (μ t t) ω = 0 := by
  simp [exponent_apply, fourierCos_kernel_diag hker ht ω]

/-- **The exponents are nonnegative**: the transform of a probability measure is at most `1`. -/
theorem exponent_nonneg (hker : IsKernelFamily Fam.Φ μ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ω : ℝ) : 0 ≤ exponent (μ s t) ω := by
  haveI := hker.isProbability s t hs hst
  rw [exponent_apply, neg_nonneg]
  exact Real.log_nonpos (kernel_transform_pos hker hs hst ω).le (fourierCos_le_one _ ω)

/-- **`g_{s,t} = G(t,·) - G(s,·)`.** -/
theorem exponent_eq_sub (hker : IsKernelFamily Fam.Φ μ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ω : ℝ) : exponent (μ s t) ω = exponent (μ 0 t) ω - exponent (μ 0 s) ω := by
  have h := exponent_add hker le_rfl hs hst ω
  linarith

/-- **`G(·,ω)` is continuous on `[0,∞)`** — (A7) along the slice `t ↦ (0,t)`, divided by the
transform of the test function and composed with `log`. -/
theorem continuousOn_exponent (hker : IsKernelFamily Fam.Φ μ) (ω : ℝ) :
    ContinuousOn (fun t => exponent (μ 0 t) ω) (Ici 0) := by
  have hmap : MapsTo (fun t : ℝ => ((0:ℝ), t)) (Ici 0) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} :=
    fun t ht => ⟨le_rfl, ht⟩
  have hcos : ContinuousOn (fun t => fourierCos (μ 0 t) ω) (Ici 0) :=
    (continuousOn_fourierCos_kernel hker ω).comp
      ((continuous_const.prodMk continuous_id).continuousOn) hmap
  exact (hcos.log fun t ht => (kernel_transform_pos hker le_rfl (mem_Ici.mp ht) ω).ne').neg

/-- **`G(t,·)` is continuous** — the continuity of a characteristic function. -/
theorem continuous_exponent (hker : IsKernelFamily Fam.Φ μ) {t : ℝ} (ht : 0 ≤ t) :
    Continuous (exponent (μ 0 t)) := by
  haveI := hker.isProbability 0 t le_rfl ht
  exact ((continuous_fourierCos (μ 0 t)).log
    fun ω => (kernel_transform_pos hker le_rfl ht ω).ne').neg

/-- **`G(t,0) = 0`.** -/
theorem exponent_atZero (hker : IsKernelFamily Fam.Φ μ) {t : ℝ} (ht : 0 ≤ t) :
    exponent (μ 0 t) 0 = 0 := by
  haveI := hker.isProbability 0 t le_rfl ht
  simp [exponent_apply, fourierCos_zero]

end ScaleSpace
