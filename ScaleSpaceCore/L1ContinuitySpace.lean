/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import ScaleSpaceCore.BochnerConvolutionSpace
import ScaleSpaceCore.L1Continuity

/-!
# The modulus of continuity of translation on `L¹(E)`, and the estimate (★)

Q-0332 (SSL-5, stretch), the `d`-dimensional counterpart of `ScaleSpaceCore.L1Continuity`:
`Θ_f(y) = ‖T_y f - f‖₁` is bounded, continuous and vanishes at `0` (`transDiffE`, packaged as
`transDiffBCFE`), and for a probability measure

  `‖μ * f - f‖₁ ≤ ∫ ‖T_y f - f‖₁ μ(dy)`.                                            (★)

On the line (★) is proved by Tonelli; here it is one line from the Bochner form
`μ * f = ∫ T_y f dμ(y)` (`bconvME_eq_mconvL1E`): `μ * f - f = ∫ (T_y f - f) dμ(y)`, and the norm
of an integral is at most the integral of the norm.

Over an inner product space the Lévy clause follows as on the line: kernels whose
characteristic functions tend to `1` give operators tending strongly to the identity
(`tendsto_norm_mconvL1E_sub_of_tendsto_charFun`), through Mathlib's Lévy continuity theorem on a
finite-dimensional inner product space.
-/

namespace ScaleSpace

open MeasureTheory Set Filter
open scoped ENNReal Topology

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- `Θ_f(y) = ‖T_y f - f‖₁`, the modulus of continuity of translation at `f`. -/
noncomputable def transDiffE (f : E →₁[volume] ℝ) (y : E) : ℝ := ‖transL1E y f - f‖

theorem continuous_transDiffE (f : E →₁[volume] ℝ) : Continuous (transDiffE f) :=
  ((continuous_transL1E f).sub continuous_const).norm

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem transDiffE_nonneg (f : E →₁[volume] ℝ) (y : E) : 0 ≤ transDiffE f y := norm_nonneg _

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp]
theorem transDiffE_zero (f : E →₁[volume] ℝ) : transDiffE f 0 = 0 := by
  rw [transDiffE, transL1E_zero, ContinuousLinearMap.id_apply, sub_self, norm_zero]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- `Θ_f ≤ 2‖f‖`. -/
theorem transDiffE_le (f : E →₁[volume] ℝ) (y : E) : transDiffE f y ≤ 2 * ‖f‖ := by
  calc transDiffE f y ≤ ‖transL1E y f‖ + ‖f‖ := norm_sub_le _ _
    _ ≤ 2 * ‖f‖ := by linarith [norm_transL1E_le y f]

theorem integrable_transDiffE (μ : Measure E) [IsFiniteMeasure μ] (f : E →₁[volume] ℝ) :
    Integrable (transDiffE f) μ :=
  (integrable_const (2 * ‖f‖)).mono' (continuous_transDiffE f).aestronglyMeasurable
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (transDiffE_nonneg f y)]
      exact transDiffE_le f y)

/-- **(★).** `‖μ * f - f‖₁ ≤ ∫ Θ_f dμ` for a probability measure `μ`. -/
theorem norm_mconvL1E_sub_le (μ : Measure E) [IsProbabilityMeasure μ] (f : E →₁[volume] ℝ) :
    ‖mconvL1E μ f - f‖ ≤ ∫ y, transDiffE f y ∂μ := by
  have hsplit : mconvL1E μ f - f = ∫ y, (transL1E y f - f) ∂μ := by
    rw [integral_sub (integrable_transL1E μ f) (integrable_const f), integral_const,
      ← bconvME_eq_mconvL1E, bconvME, probReal_univ, one_smul]
  rw [hsplit]
  exact norm_integral_le_integral_norm _

/-- **The modulus of continuity decreases under convolution**: `Θ_{ν*f} ≤ Θ_f`. -/
theorem transDiffE_mconvL1E_le (ν : Measure E) [IsProbabilityMeasure ν] (f : E →₁[volume] ℝ)
    (y : E) : transDiffE (mconvL1E ν f) y ≤ transDiffE f y := by
  have hcomm : transL1E y (mconvL1E ν f) - mconvL1E ν f = mconvL1E ν (transL1E y f - f) := by
    rw [ContinuousLinearMap.map_sub, mconvL1E_transL1E]
  rw [transDiffE, transDiffE, hcomm]
  exact norm_mconvL1E_le ν _

/-- **(★) after an operator**, with the bound still expressed at `f`. -/
theorem norm_mconvL1E_comp_sub_le (μ ν : Measure E) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (f : E →₁[volume] ℝ) :
    ‖mconvL1E μ (mconvL1E ν f) - mconvL1E ν f‖ ≤ ∫ y, transDiffE f y ∂μ :=
  (norm_mconvL1E_sub_le μ (mconvL1E ν f)).trans
    (integral_mono (integrable_transDiffE μ _) (integrable_transDiffE μ f)
      (transDiffE_mconvL1E_le ν f))

/-- The modulus of continuity as a bounded continuous function on `E`. -/
noncomputable def transDiffBCFE (f : E →₁[volume] ℝ) : BoundedContinuousFunction E ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (transDiffE f) (continuous_transDiffE f)
    (2 * ‖f‖) fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (transDiffE_nonneg f y)]
      exact transDiffE_le f y

@[simp]
theorem transDiffBCFE_apply (f : E →₁[volume] ℝ) (y : E) :
    transDiffBCFE f y = transDiffE f y := rfl

theorem transDiffE_real (f : X) (y : ℝ) : transDiffE f y = transDiff f y := by
  rw [transDiffE, transDiff, transL1E_real]

end Normed

/-! ## The Lévy clause, over an inner product space -/

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- **Kernels whose characteristic functions tend to `1` concentrate at the origin**, measured by
the modulus of continuity. -/
theorem tendsto_integral_transDiffE_of_tendsto_charFun {μ : ℕ → Measure E}
    [hμ : ∀ n, IsProbabilityMeasure (μ n)]
    (h : ∀ ω, Tendsto (fun n => charFun (μ n) ω) atTop (𝓝 1)) (f : E →₁[volume] ℝ) :
    Tendsto (fun n => ∫ y, transDiffE f y ∂(μ n)) atTop (𝓝 0) := by
  set P : ℕ → ProbabilityMeasure E := fun n => ⟨μ n, hμ n⟩ with hP
  set P₀ : ProbabilityMeasure E := ⟨Measure.dirac 0, inferInstance⟩ with hP₀
  have hconv : Tendsto P atTop (𝓝 P₀) := by
    refine ProbabilityMeasure.tendsto_of_tendsto_charFun fun ω => ?_
    have h0 : charFun (P₀ : Measure E) ω = 1 := by
      change charFun (Measure.dirac (0 : E)) ω = 1
      rw [charFun_dirac]
      simp
    rw [h0]
    exact h ω
  have := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv (transDiffBCFE f)
  simpa [hP, hP₀] using this

/-- **Kernels whose characteristic functions tend to `1` give operators tending strongly to the
identity.** -/
theorem tendsto_norm_mconvL1E_sub_of_tendsto_charFun {μ : ℕ → Measure E}
    [∀ n, IsProbabilityMeasure (μ n)]
    (h : ∀ ω, Tendsto (fun n => charFun (μ n) ω) atTop (𝓝 1)) (f : E →₁[volume] ℝ) :
    Tendsto (fun n => ‖mconvL1E (μ n) f - f‖) atTop (𝓝 0) :=
  squeeze_zero (fun _ => norm_nonneg _) (fun n => norm_mconvL1E_sub_le (μ n) f)
    (tendsto_integral_transDiffE_of_tendsto_charFun h f)

end Inner

end ScaleSpace
