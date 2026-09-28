/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Two finite measures on `[0,1]` with the same moments are equal

Slice 3 of E-0009 (hub `proposals/E-0009.md`), moved from Paper I's `Injectivity.lean` and
Paper V's `SpatialLine/LaplaceUniqueness.lean`, where it was proved identically in both
articles, differing only in which one-sided predicate (`IsCausal` or `IsFolded`) supplies the
finiteness/positivity hypotheses that consume it
(`offices/engineer/notes/2026-09-19-lean-duplication-survey.md` §§ 3, 6; already queued by hand
in this trunk's own README before the survey). This file is the Mathlib-only core the two
articles both build their Laplace-uniqueness proposition on; the predicate and the final
half-line statement stay behind, in each article.

## The route

Two routes were ruled out on both sides: Mathlib's `Measure.ext_of_complexMGF_id_eq` needs the
complex moment generating functions to agree on all of `ℂ`, and Stone–Weierstrass on `ℝ` fails
directly, because `t ↦ e^{-st}` is unbounded there. What works is the classical substitution
`x = e^{-t}`, which carries a positive half-line onto `(0,1]`: there the transform at natural
numbers is the sequence of moments, polynomials are dense by Weierstrass, and two finite measures
agreeing on every bounded continuous function are equal.
-/

namespace ScaleSpace

open MeasureTheory Set

/-! ## The substitution `x = e^{-t}` -/

/-- The change of variable carrying a half-line onto `(0,1]`. -/
noncomputable def expNeg (t : ℝ) : ℝ := Real.exp (-t)

lemma continuous_expNeg : Continuous expNeg := by unfold expNeg; fun_prop

lemma injective_expNeg : Function.Injective expNeg := fun x y hxy => by
  have : -x = -y := Real.exp_eq_exp.mp hxy
  linarith

/-- `expNeg` is a measurable embedding: injective and continuous on a Polish space. -/
lemma measurableEmbedding_expNeg : MeasurableEmbedding expNeg :=
  continuous_expNeg.measurableEmbedding injective_expNeg

/-! ## Integrating continuous functions against a compactly carried measure -/

/-- A continuous function is integrable against a finite measure carried by a compact set — it
need not be bounded on all of `ℝ`, which is what lets polynomials be used below. -/
theorem integrable_of_carried {ν : Measure ℝ} [IsFiniteMeasure ν] {K : Set ℝ} (hK : IsCompact K)
    (hcar : ν Kᶜ = 0) {g : ℝ → ℝ} (hg : Continuous g) : Integrable g ν := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  have hae : ∀ᵐ x ∂ν, ‖g x‖ ≤ ‖C‖ := by
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) hcar
    simp only [mem_setOf_eq, not_le] at hx
    exact fun hxK => absurd ((hC x hxK).trans (le_abs_self C)) (not_le.mpr hx)
  exact (hasFiniteIntegral_const C).mono hae

/-- The `ε`-estimate: two integrals of functions uniformly `ε`-close on the carrier differ by at
most `ε` times the mass. -/
theorem abs_integral_sub_le_of_carried {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hcar : ν (Icc (0 : ℝ) 1)ᶜ = 0) {g₁ g₂ : ℝ → ℝ}
    (h₁ : Integrable g₁ ν) (h₂ : Integrable g₂ ν) {ε : ℝ}
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, |g₁ x - g₂ x| ≤ ε) :
    |∫ x, g₁ x ∂ν - ∫ x, g₂ x ∂ν| ≤ ε * (ν univ).toReal := by
  rw [← integral_sub h₁ h₂]
  have hae : ∀ᵐ x ∂ν, ‖g₁ x - g₂ x‖ ≤ ε := by
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) hcar
    simp only [mem_setOf_eq, not_le, Real.norm_eq_abs] at hx
    exact fun hxK => absurd (hb x hxK) (not_le.mpr hx)
  calc |∫ x, (g₁ x - g₂ x) ∂ν|
      ≤ ∫ x, ‖g₁ x - g₂ x‖ ∂ν := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := ν) (fun x => g₁ x - g₂ x)
    _ ≤ ∫ _, ε ∂ν := integral_mono_ae (h₁.sub h₂).norm (integrable_const ε) hae
    _ = ε * (ν univ).toReal := by
        rw [integral_const, smul_eq_mul, mul_comm, measureReal_def]

/-! ## Equal moments force equal measures on `[0,1]` -/

/-- Equal moments give equal polynomial integrals, by linearity. -/
theorem integral_polynomial_eq_of_moments {ν ν' : Measure ℝ} [IsFiniteMeasure ν]
    [IsFiniteMeasure ν'] (hν : ν (Icc (0 : ℝ) 1)ᶜ = 0) (hν' : ν' (Icc (0 : ℝ) 1)ᶜ = 0)
    (hmom : ∀ n : ℕ, ∫ x, x ^ n ∂ν = ∫ x, x ^ n ∂ν') (p : Polynomial ℝ) :
    ∫ x, p.eval x ∂ν = ∫ x, p.eval x ∂ν' := by
  have hint : ∀ (σ : Measure ℝ) [IsFiniteMeasure σ], σ (Icc (0 : ℝ) 1)ᶜ = 0 → ∀ i : ℕ,
      Integrable (fun x : ℝ => p.coeff i * x ^ i) σ := fun σ _ hσ i =>
    integrable_of_carried isCompact_Icc hσ (by fun_prop)
  simp only [Polynomial.eval_eq_sum_range]
  rw [integral_finsetSum _ (fun i _ => hint ν hν i),
    integral_finsetSum _ (fun i _ => hint ν' hν' i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_const_mul, hmom i]

/-- **Two finite measures carried by `[0,1]` with the same moments are equal.** Weierstrass plus
the `ε`-estimate. -/
theorem ext_of_moments {ν ν' : Measure ℝ} [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (hν : ν (Icc (0 : ℝ) 1)ᶜ = 0) (hν' : ν' (Icc (0 : ℝ) 1)ᶜ = 0)
    (hmom : ∀ n : ℕ, ∫ x, x ^ n ∂ν = ∫ x, x ^ n ∂ν') : ν = ν' := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  have hfν : Integrable (fun x => f x) ν :=
    integrable_of_carried isCompact_Icc hν f.continuous
  have hfν' : Integrable (fun x => f x) ν' :=
    integrable_of_carried isCompact_Icc hν' f.continuous
  have key : ∀ δ : ℝ, 0 < δ → |∫ x, f x ∂ν - ∫ x, f x ∂ν'| ≤ δ := by
    intro δ hδ
    set M : ℝ := (ν univ).toReal + (ν' univ).toReal with hM
    have hM0 : 0 ≤ M := by positivity
    have hpos : 0 < δ / (M + 1) := by positivity
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 (fun x => f x)
      f.continuous.continuousOn _ hpos
    have hpν : Integrable (fun x => p.eval x) ν :=
      integrable_of_carried isCompact_Icc hν (by fun_prop)
    have hpν' : Integrable (fun x => p.eval x) ν' :=
      integrable_of_carried isCompact_Icc hν' (by fun_prop)
    have hb : ∀ x ∈ Icc (0 : ℝ) 1, |f x - p.eval x| ≤ δ / (M + 1) := fun x hx => by
      rw [abs_sub_comm]; exact (hp x hx).le
    have e₁ := abs_integral_sub_le_of_carried hν hfν hpν hb
    have e₂ := abs_integral_sub_le_of_carried hν' hfν' hpν' hb
    have emid : ∫ x, p.eval x ∂ν = ∫ x, p.eval x ∂ν' :=
      integral_polynomial_eq_of_moments hν hν' hmom p
    have htri : |∫ x, f x ∂ν - ∫ x, f x ∂ν'|
        ≤ |∫ x, f x ∂ν - ∫ x, p.eval x ∂ν| + |∫ x, f x ∂ν' - ∫ x, p.eval x ∂ν'| := by
      rw [emid]
      calc |∫ x, f x ∂ν - ∫ x, f x ∂ν'|
          = |(∫ x, f x ∂ν - ∫ x, p.eval x ∂ν') - (∫ x, f x ∂ν' - ∫ x, p.eval x ∂ν')| := by
            ring_nf
        _ ≤ _ := abs_sub _ _
    refine htri.trans ?_
    have : δ / (M + 1) * (ν univ).toReal + δ / (M + 1) * (ν' univ).toReal ≤ δ := by
      rw [← mul_add, ← hM, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    exact (add_le_add e₁ e₂).trans this
  have habs : |∫ x, f x ∂ν - ∫ x, f x ∂ν'| ≤ 0 :=
    le_of_forall_pos_le_add fun δ hδ => by simpa using key δ hδ
  exact sub_eq_zero.mp (abs_nonpos_iff.mp habs)

end ScaleSpace
