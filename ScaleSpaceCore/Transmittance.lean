/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import ScaleSpaceCore.Additivity

/-!
# `cor:smoothed-transmittance`: one strictly monotone number per scale

Blueprint: `blueprint/src/parts/05-cascade.tex`, `cor:smoothed-transmittance`.

The coordinate the gauge argument of Chapter 6 runs on, and the one node of Chapter 5 with no
causal counterpart: the causal argument read the action off the accumulated exponent at one
fixed value of the transform variable, which `cor:monotonicity` does not licence on the line.
What replaces it is

  `Θ(t) = ∫ μ̂_{0,t}(ω) ρ(ω) dω = ∫ e^{-x²/2} μ_{0,t}(dx)`,

a single number attached to each scale, continuous, in `(0,1]`, and — under (ND) — strictly
decreasing.

The Gaussian density `ρ` of the statement is `ScaleSpace.gaussTest`, the same test function
`Pairing` uses for the uniqueness clause, and the Fubini identity of the first
clause is `integral_cos_mul_gaussTest` read in the other variable: the cosine moment of the
standard Gaussian density is `e^{-x²/2}` at frequency `x`, which is exactly the integrand on the
measure side.

## What proving it found

Two of the six clauses need less than the blueprint's proof cites. Positivity of `Θ` is *not*
`lem:nonvanishing`: the integrand `e^{-x²/2}` is strictly positive at every point, so the
integral of a probability measure against it is positive for the elementary reason, and the
formal proof spends no positivity of the transform. Only the antitone clause and the strict
clause use `kernel_transform_pos`, and the strict one uses it only to know that the factor
`μ̂_{0,s} ρ` is positive.

## Provenance

Moved by Q-0305 from Paper V's `SpatialLine/Transmittance.lean` (the public cone export,
`cone-v0.1`, commit `f28c066e`) for the line classification (`MainAnalysis`,
`MainConstruction`): only the declarations those theorems reach, with statements and
proofs unchanged up to the namespace. Blueprint labels are Paper V's.
-/

namespace ScaleSpace

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal Topology

/-! ## The Gaussian density, written as the statement writes it -/

lemma gaussTest_apply (ω : ℝ) :
    gaussTest ω = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(ω ^ 2) / 2) := by
  simp [gaussTest, gaussianPDFReal]

lemma gaussTest_pos (x : ℝ) : 0 < gaussTest x := gaussianPDFReal_pos 0 1 x one_ne_zero

lemma continuous_gaussTest : Continuous gaussTest := by
  have h : gaussTest = fun ω => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(ω ^ 2) / 2) :=
    funext gaussTest_apply
  rw [h]
  fun_prop

/-! ## The Fubini identity -/

/-- **The two forms of `Θ` agree.** The frequency-side integral against the standard Gaussian
density equals the measure-side integral of `e^{-x²/2}`. -/
theorem integral_fourierCos_mul_gaussTest (ν : Measure ℝ) [IsFiniteMeasure ν] :
    ∫ ω, fourierCos ν ω * gaussTest ω = ∫ x, Real.exp (-(x ^ 2) / 2) ∂ν := by
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.cos (p.1 * p.2) * gaussTest p.1) (volume.prod ν) := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (Real.continuous_cos.comp (continuous_fst.mul continuous_snd)).aestronglyMeasurable
    · exact (measurable_gaussTest.comp measurable_fst).aestronglyMeasurable
  have hint : Integrable (fun p : ℝ × ℝ => Real.cos (p.1 * p.2) * gaussTest p.1)
      (volume.prod ν) := by
    refine (integrable_gaussTest.comp_fst ν).mono' hmeas ?_
    filter_upwards with p
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (gaussTest_pos p.1)]
    exact mul_le_of_le_one_left (gaussTest_pos p.1).le (Real.abs_cos_le_one _)
  calc ∫ ω, fourierCos ν ω * gaussTest ω
      = ∫ ω, ∫ x, Real.cos (ω * x) * gaussTest ω ∂ν := by
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        dsimp only
        rw [fourierCos_apply, integral_mul_const]
    _ = ∫ x, ∫ ω, Real.cos (ω * x) * gaussTest ω ∂volume ∂ν := integral_integral_swap hint
    _ = ∫ x, Real.exp (-(x ^ 2) / 2) ∂ν := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        dsimp only
        have hcomm : (fun ω => Real.cos (ω * x) * gaussTest ω)
            = fun ω => Real.cos (x * ω) * gaussTest ω := by
          funext ω; rw [mul_comm ω x]
        rw [hcomm]
        exact integral_cos_mul_gaussTest x

/-! ## The clauses -/

variable {Fam : PreCascadeCore} {μ : ℝ → ℝ → Measure ℝ}

/-- **`Θ` is strictly decreasing under (ND).**

The integrand `(1 - μ̂_{a,b}) μ̂_{0,a} ρ` is nonnegative and vanishes exactly where
`μ̂_{a,b} = 1`; the complement of that set is open and, by (ND) and the uniqueness of the
transform, nonempty, hence of positive Lebesgue measure. -/
theorem strictAntiOn_transmittance (hker : IsKernelFamily Fam.Φ μ) (hnd : IsNondegenerate Fam.Φ) :
    StrictAntiOn (fun t => ∫ x, Real.exp (-(x ^ 2) / 2) ∂(μ 0 t)) (Ici 0) := by
  intro a ha b hb hab
  haveI := hker.isProbability 0 a le_rfl (mem_Ici.mp ha)
  haveI := hker.isProbability 0 b le_rfl (mem_Ici.mp hb)
  haveI := hker.isProbability a b (mem_Ici.mp ha) hab.le
  simp only
  rw [← integral_fourierCos_mul_gaussTest (μ 0 a), ← integral_fourierCos_mul_gaussTest (μ 0 b)]
  set f : ℝ → ℝ := fun ω =>
    (1 - fourierCos (μ a b) ω) * (fourierCos (μ 0 a) ω * gaussTest ω) with hfdef
  have hfnn : ∀ ω, 0 ≤ f ω := by
    intro ω
    have h1 : 0 ≤ 1 - fourierCos (μ a b) ω := by linarith [fourierCos_le_one (μ a b) ω]
    have h2 : 0 ≤ fourierCos (μ 0 a) ω * gaussTest ω :=
      mul_nonneg (kernel_transform_pos hker le_rfl (mem_Ici.mp ha) ω).le (gaussTest_pos ω).le
    exact mul_nonneg h1 h2
  have hfint : Integrable f := by
    refine (integrable_gaussTest.const_mul 2).mono' ?_ ?_
    · exact (((continuous_const.sub (continuous_fourierCos (μ a b))).mul
        ((continuous_fourierCos (μ 0 a)).mul continuous_gaussTest))
        ).aestronglyMeasurable
    · refine ae_of_all _ fun ω => ?_
      have h1 : |1 - fourierCos (μ a b) ω| ≤ 2 := by
        have := abs_fourierCos_le_one (μ a b) ω
        rw [abs_le] at this ⊢
        constructor <;> linarith [this.1, this.2]
      have h2 : |fourierCos (μ 0 a) ω| ≤ 1 := abs_fourierCos_le_one (μ 0 a) ω
      simp only [hfdef, Real.norm_eq_abs, abs_mul, abs_of_pos (gaussTest_pos ω)]
      have hg := (gaussTest_pos ω).le
      calc |1 - fourierCos (μ a b) ω| * (|fourierCos (μ 0 a) ω| * gaussTest ω)
          ≤ 2 * (1 * gaussTest ω) := by
            refine mul_le_mul h1 ?_ ?_ (by norm_num)
            · exact mul_le_mul_of_nonneg_right h2 hg
            · positivity
        _ = 2 * gaussTest ω := by ring
  -- the difference of the two integrals is `∫ f`
  have hdiff : (∫ ω, fourierCos (μ 0 a) ω * gaussTest ω)
      - (∫ ω, fourierCos (μ 0 b) ω * gaussTest ω) = ∫ ω, f ω := by
    have hia : Integrable (fun ω => fourierCos (μ 0 a) ω * gaussTest ω) :=
      integrable_gaussTest.bdd_mul (continuous_fourierCos (μ 0 a)).aestronglyMeasurable
        (ae_of_all _ fun ω => by
          simpa [Real.norm_eq_abs] using abs_fourierCos_le_one (μ 0 a) ω)
    have hib : Integrable (fun ω => fourierCos (μ 0 b) ω * gaussTest ω) :=
      integrable_gaussTest.bdd_mul (continuous_fourierCos (μ 0 b)).aestronglyMeasurable
        (ae_of_all _ fun ω => by
          simpa [Real.norm_eq_abs] using abs_fourierCos_le_one (μ 0 b) ω)
    rw [← integral_sub hia hib]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [hfdef]
    rw [fourierCos_kernel_mul_comm hker le_rfl (mem_Ici.mp ha) hab.le ω]
    ring
  -- and that integral is positive
  have hsupp : Function.support f = {ω : ℝ | fourierCos (μ a b) ω ≠ 1} := by
    ext ω
    simp only [Function.mem_support, hfdef, mem_setOf_eq, ne_eq, mul_eq_zero, not_or, sub_eq_zero]
    constructor
    · rintro ⟨h1, -⟩ h2
      exact h1 h2.symm
    · intro h
      refine ⟨fun hc => h hc.symm, ?_⟩
      exact ⟨(kernel_transform_pos hker le_rfl (mem_Ici.mp ha) ω).ne', (gaussTest_pos ω).ne'⟩
  have hopen : IsOpen {ω : ℝ | fourierCos (μ a b) ω ≠ 1} := by
    have : {ω : ℝ | fourierCos (μ a b) ω ≠ 1} = (fourierCos (μ a b)) ⁻¹' {1}ᶜ := rfl
    rw [this]
    exact (continuous_fourierCos (μ a b)).isOpen_preimage _ isOpen_compl_singleton
  have hne : {ω : ℝ | fourierCos (μ a b) ω ≠ 1}.Nonempty := by
    by_contra hcon
    rw [not_nonempty_iff_eq_empty] at hcon
    refine kernel_ne_dirac hker hnd (mem_Ici.mp ha) hab ?_
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    have hall : fourierCos (μ a b) ω = 1 := by
      by_contra hc
      exact absurd (mem_setOf_eq ▸ hc : ω ∈ {ω : ℝ | fourierCos (μ a b) ω ≠ 1})
        (by rw [hcon]; exact notMem_empty ω)
    rw [charFun_eq_fourierCos_of_symmetric
      (kernel_symmetric hker (mem_Ici.mp ha) hab.le) ω, hall]
    simp
  have hpos : 0 < ∫ ω, f ω := by
    rw [integral_pos_iff_support_of_nonneg hfnn hfint, hsupp]
    exact hopen.measure_pos volume hne
  linarith [hdiff, hpos]

end ScaleSpace
