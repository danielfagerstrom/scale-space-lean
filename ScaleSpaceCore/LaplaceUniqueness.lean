/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import ScaleSpaceCore.Transform
import ScaleSpaceCore.SDProfile
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
half-line statement stayed behind, in each article, until Q-0360 moved Paper V's (below).

## The route

Two routes were ruled out on both sides: Mathlib's `Measure.ext_of_complexMGF_id_eq` needs the
complex moment generating functions to agree on all of `ℂ`, and Stone–Weierstrass on `ℝ` fails
directly, because `t ↦ e^{-st}` is unbounded there. What works is the classical substitution
`x = e^{-t}`, which carries a positive half-line onto `(0,1]`: there the transform at natural
numbers is the sequence of moments, polynomials are dense by Weierstrass, and two finite measures
agreeing on every bounded continuous function are equal.

## The half-line statement (Q-0360)

The last two sections were moved by Q-0360 from Paper V's `SpatialLine/LaplaceUniqueness.lean` at
the cone export's `v0.1`, statements verbatim up to the namespace: the Laplace transform as a real
integral, the pushforward under `expNeg` of a folded measure, and injectivity of `laplaceL` on
folded measures — finite (`laplaceL_injective_of_isFiniteMeasure`), finite at one point
(`laplaceL_injective_of_ne_top`), and `prop:laplace-uniqueness-locally-finite`
(`laplace_uniqueness_locally_finite`). E-0009 left them behind only because `IsFolded` was then
spatial-only; it has been in `ScaleSpaceCore.SDProfile` since Q-0302, and Paper VII's
`lem:bernstein-triplet-unique` is the second consumer. Paper I's `IsCausal` twins stay in Paper I,
which is frozen (Q-0182).
-/

namespace ScaleSpace

open MeasureTheory Set
open scoped ENNReal

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

/-! ## The Laplace transform as a real integral -/

/-- The `ℝ≥0∞`-valued transform and the Bochner integral of `e^{-τu}` agree, unconditionally:
where the transform is infinite both sides are `0`, the integrand failing to be integrable.

twin: `Hemigroup.laplace_eq_toReal_laplaceL`. -/
theorem integral_exp_neg_eq_toReal_laplaceL (m : Measure ℝ) (τ : ℝ) :
    ∫ u, Real.exp (-(τ * u)) ∂m = (laplaceL m τ).toReal := by
  rw [laplaceL, ← integral_toReal]
  · refine integral_congr_ae ?_
    filter_upwards with u
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  · exact (Real.continuous_exp.comp (by fun_prop)).aemeasurable.ennreal_ofReal
  · filter_upwards with _ using ENNReal.ofReal_lt_top

/-! ## The pushforward of a folded measure under `expNeg` -/

lemma expNeg_mem_Icc {t : ℝ} (ht : 0 ≤ t) : expNeg t ∈ Icc (0 : ℝ) 1 :=
  ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by simp [ht])⟩

/-- The pushforward of a folded measure is carried by the compact set `[0,1]`. This is the step
that makes Weierstrass applicable, and the only place the folding is used. -/
lemma map_expNeg_compl_Icc {m : Measure ℝ} (h : IsFolded m) :
    (m.map expNeg) (Icc (0 : ℝ) 1)ᶜ = 0 := by
  rw [Measure.map_apply continuous_expNeg.measurable measurableSet_Icc.compl]
  refine measure_mono_null (fun t ht => ?_) h
  simp only [mem_Iic]
  by_contra hc
  exact ht (expNeg_mem_Icc (not_le.mp hc).le)

instance isFiniteMeasure_map_expNeg {m : Measure ℝ} [IsFiniteMeasure m] :
    IsFiniteMeasure (m.map expNeg) := by
  constructor
  rw [Measure.map_apply continuous_expNeg.measurable MeasurableSet.univ, preimage_univ]
  exact measure_lt_top m univ

/-- **The transform at a natural number is a moment of the pushforward.** This is the identity the
whole proof turns on. -/
lemma integral_pow_map_expNeg {m : Measure ℝ} (n : ℕ) :
    ∫ x, x ^ n ∂(m.map expNeg) = (laplaceL m n).toReal := by
  rw [measurableEmbedding_expNeg.integral_map, ← integral_exp_neg_eq_toReal_laplaceL]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [expNeg]
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-! ## The theorem -/

/-- Injectivity of the Laplace transform on **finite** folded measures.

twin: `Hemigroup.laplace_injective`. -/
theorem laplaceL_injective_of_isFiniteMeasure {m m' : Measure ℝ} [IsFiniteMeasure m]
    [IsFiniteMeasure m'] (hm : IsFolded m) (hm' : IsFolded m')
    (h : ∀ s : ℝ, 0 ≤ s → laplaceL m s = laplaceL m' s) : m = m' := by
  have hmap : m.map expNeg = m'.map expNeg := by
    refine ext_of_moments (map_expNeg_compl_Icc hm) (map_expNeg_compl_Icc hm') fun n => ?_
    rw [integral_pow_map_expNeg, integral_pow_map_expNeg, h n (Nat.cast_nonneg n)]
  ext A hA
  have himg : MeasurableSet (expNeg '' A) := measurableEmbedding_expNeg.measurableSet_image' hA
  have hmA : (m.map expNeg) (expNeg '' A) = m A := by
    rw [Measure.map_apply continuous_expNeg.measurable himg,
      Set.preimage_image_eq A injective_expNeg]
  have hm'A : (m'.map expNeg) (expNeg '' A) = m' A := by
    rw [Measure.map_apply continuous_expNeg.measurable himg,
      Set.preimage_image_eq A injective_expNeg]
  rw [← hmA, ← hm'A, hmap]

/-- Damping a measure by `e^{-τ₁ u}` shifts its transform.

twin: `Hemigroup.laplaceL_withDensity_expNeg`. -/
theorem laplaceL_withDensity_expNeg (m : Measure ℝ) (τ₁ τ : ℝ) :
    laplaceL (m.withDensity fun u => ENNReal.ofReal (Real.exp (-(τ₁ * u)))) τ
      = laplaceL m (τ₁ + τ) := by
  have hf : Measurable fun u : ℝ => ENNReal.ofReal (Real.exp (-(τ₁ * u))) := by fun_prop
  have hg : Measurable fun u : ℝ => ENNReal.ofReal (Real.exp (-(τ * u))) := by fun_prop
  rw [laplaceL, lintegral_withDensity_eq_lintegral_mul _ hf hg, laplaceL]
  refine lintegral_congr fun u => ?_
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

/-- Injectivity of the Laplace transform without a finiteness assumption on the measures: two
folded measures whose transforms agree on `[τ₁,∞)`, one of them finite at `τ₁`, are equal.

twin: `Hemigroup.laplaceL_injective_of_ne_top`, verbatim with `IsCausal` replaced by `IsFolded`.
The proof is the damping trick: `e^{-τ₁u}m(du)` is finite precisely because the transform
converges at `τ₁`, its transform at `τ` is `m`'s at `τ₁ + τ`, and the damping is undone by
multiplying the density back, `e^{-τ₁u}` being everywhere positive and finite. -/
theorem laplaceL_injective_of_ne_top {m m' : Measure ℝ} (hm : IsFolded m) (hm' : IsFolded m')
    {τ₁ : ℝ} (hfin : laplaceL m τ₁ ≠ ⊤) (h : ∀ τ, τ₁ ≤ τ → laplaceL m τ = laplaceL m' τ) :
    m = m' := by
  set f : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (Real.exp (-(τ₁ * u))) with hf_def
  set g : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (Real.exp (τ₁ * u)) with hg_def
  have hfm : Measurable f := by fun_prop
  have hgm : Measurable g := by fun_prop
  have hmass : ∀ ν : Measure ℝ, ∫⁻ u, f u ∂ν = laplaceL ν τ₁ := fun _ => rfl
  haveI : IsFiniteMeasure (m.withDensity f) :=
    isFiniteMeasure_withDensity (by rw [hmass]; exact hfin)
  haveI : IsFiniteMeasure (m'.withDensity f) :=
    isFiniteMeasure_withDensity (by rw [hmass, ← h τ₁ le_rfl]; exact hfin)
  have hfold : ∀ ν : Measure ℝ, IsFolded ν → IsFolded (ν.withDensity f) := fun ν hν =>
    (withDensity_absolutelyContinuous ν f) hν
  have hdamped : m.withDensity f = m'.withDensity f := by
    refine laplaceL_injective_of_isFiniteMeasure (hfold m hm) (hfold m' hm') fun τ hτ => ?_
    rw [laplaceL_withDensity_expNeg, laplaceL_withDensity_expNeg, h (τ₁ + τ) (by linarith)]
  have hfg : f * g = 1 := by
    funext u
    rw [Pi.mul_apply, hf_def, hg_def, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
      neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, Pi.one_apply]
  calc m = m.withDensity (f * g) := by rw [hfg, withDensity_one]
    _ = (m.withDensity f).withDensity g := withDensity_mul _ hfm hgm
    _ = (m'.withDensity f).withDensity g := by rw [hdamped]
    _ = m'.withDensity (f * g) := (withDensity_mul _ hfm hgm).symm
    _ = m' := by rw [hfg, withDensity_one]

/-- **`prop:laplace-uniqueness-locally-finite`.** Two Borel measures on `(0,∞)`, not necessarily
finite, whose Laplace transforms agree and are finite on some ray `(τ₀,∞)`, are equal.

The blueprint's hypothesis is the whole open ray; the proof needs finiteness at one point of it,
which is the sharpening the causal side found and which `laplaceL_injective_of_ne_top` records. -/
theorem laplace_uniqueness_locally_finite {m m' : Measure ℝ} (hm : IsFolded m) (hm' : IsFolded m')
    {τ₀ : ℝ} (heq : ∀ τ, τ₀ < τ → laplaceL m τ = laplaceL m' τ)
    (hfin : ∀ τ, τ₀ < τ → laplaceL m τ ≠ ⊤) : m = m' := by
  have hτ : τ₀ < τ₀ + 1 := by linarith
  exact laplaceL_injective_of_ne_top hm hm' (hfin _ hτ)
    fun τ hτ' => heq τ (lt_of_lt_of_le hτ hτ')

end ScaleSpace
