/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import ScaleSpaceCore.CausalCone
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Three generators of the causal admissible cone

One datum per family, each a value of `ScaleSpace.CausalAdmissible`:

* `driftDatum b₀`, the data `(b₀, 0)`, with exponent `σ ↦ b₀σ` on `[0,∞)`;
* `gammaCausalDatum γ`, the data `(0, γe^{-u})`;
* `stableCausalDatum α`, `0 < α < 1`, the data `(0, c_α u^{-α})` with `c_α = α/Γ(1-α)`, with
  exponent `σ ↦ σ^α` on `[0,∞)`.

The profiles are the causal article's `Hemigroup.SelfDecomposableExponent.gammaExponent` and
`.stableDensity`, guarded at the origin the same way. Closed forms of the Gamma exponent are not
here: each article evaluates it on its own route.

## The stable exponent needs no limit at the origin

The profile is homogeneous, `k(u/c) = c^α k(u)`, so the dilation of the datum *is* its multiple
by `c^α` (`stableCausalDatum_dilate_k`), and `exponent_dilate` with `exponent_smul` gives
`F(c) = c^α F(1)` for every `c > 0`. One constant is left, and one derivative fixes it: at
`σ = 1`, `hasDerivAt_exponent` gives `∫₀^∞ e^{-u}c_α u^{-α}du = c_αΓ(1-α) = α`, so `F(1) = 1`.
-/

namespace ScaleSpace

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CausalAdmissible

/-! ## The drift -/

/-- **The causal drift datum** `(b₀, 0)`. -/
noncomputable def driftDatum (b₀ : ℝ) (hb : 0 ≤ b₀) : CausalAdmissible where
  b₀ := b₀
  k := fun _ => 0
  b₀_nonneg := hb
  k_nonneg := fun _ _ => le_rfl
  k_antitone := fun _ _ _ _ _ => le_rfl
  k_zero := rfl
  integrable_near_zero := by simp
  integrable_at_top := by simp

/-- The drift datum's exponent is `σ ↦ b₀σ` on `[0,∞)`. -/
theorem driftDatum_exponent {b₀ : ℝ} (hb : 0 ≤ b₀) {σ : ℝ} (hσ : 0 ≤ σ) :
    (driftDatum b₀ hb).exponent σ = b₀ * σ := by
  rw [exponent_eq _ hσ]
  simp [driftDatum]

/-! ## The Gamma profile -/

/-- The causal Gamma profile `γe^{-u}`, guarded at the origin. -/
noncomputable def gammaCausalProfile (γ : ℝ) : ℝ → ℝ :=
  fun u => if 0 < u then γ * Real.exp (-u) else 0

theorem gammaCausalProfile_nonneg {γ : ℝ} (hγ : 0 ≤ γ) (u : ℝ) : 0 ≤ gammaCausalProfile γ u := by
  unfold gammaCausalProfile
  split_ifs
  · positivity
  · exact le_rfl

theorem gammaCausalProfile_le {γ : ℝ} (hγ : 0 ≤ γ) (u : ℝ) : gammaCausalProfile γ u ≤ γ := by
  unfold gammaCausalProfile
  split_ifs with hu
  · have : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith
  · exact hγ

theorem integrableOn_gammaCausalProfile (γ : ℝ) :
    IntegrableOn (gammaCausalProfile γ) (Ioo (0 : ℝ) 1) := by
  have hbase : IntegrableOn (fun u : ℝ => γ * Real.exp (-u)) (Ioo (0 : ℝ) 1) :=
    (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioo_subset_Icc_self
  refine hbase.congr_fun (fun u hu => ?_) measurableSet_Ioo
  simp [gammaCausalProfile, hu.1]

theorem integrableOn_gammaCausalProfile_div {γ : ℝ} (hγ : 0 ≤ γ) :
    IntegrableOn (fun u => gammaCausalProfile γ u / u) (Ioi (1 : ℝ)) := by
  have hbase : IntegrableOn (fun u : ℝ => γ * Real.exp (-(1 * u))) (Ioi (1 : ℝ)) :=
    IntegrableOn.congr_fun ((integrableOn_exp_neg_Ioi 1).const_mul γ) (fun u _ => by simp)
      measurableSet_Ioi
  have hmeas : Measurable fun u : ℝ => gammaCausalProfile γ u / u := by
    unfold gammaCausalProfile
    exact (Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const).div measurable_id
  refine Integrable.mono' hbase hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun u hu => ?_)
  have hu1 : (1 : ℝ) < u := hu
  have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one hu1
  have hc : (0 : ℝ) ≤ γ * Real.exp (-u) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (gammaCausalProfile_nonneg hγ u) hu0.le),
    div_le_iff₀ hu0]
  simp only [gammaCausalProfile, if_pos hu0, one_mul]
  nlinarith

/-- **The causal Gamma datum** `(0, γe^{-u})`. -/
noncomputable def gammaCausalDatum (γ : ℝ) (hγ : 0 ≤ γ) : CausalAdmissible where
  b₀ := 0
  k := gammaCausalProfile γ
  b₀_nonneg := le_rfl
  k_nonneg := fun u _ => gammaCausalProfile_nonneg hγ u
  k_antitone := by
    intro x hx y hy hxy
    have hx0 : (0 : ℝ) < x := hx
    have hy0 : (0 : ℝ) < y := hy
    simp only [gammaCausalProfile, if_pos hx0, if_pos hy0]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hγ
  k_zero := by simp [gammaCausalProfile]
  integrable_near_zero :=
    lintegral_ofReal_ne_top_of_integrableOn (integrableOn_gammaCausalProfile γ)
      (.of_forall fun u => gammaCausalProfile_nonneg hγ u)
  integrable_at_top :=
    lintegral_ofReal_ne_top_of_integrableOn (integrableOn_gammaCausalProfile_div hγ)
      ((ae_restrict_iff' measurableSet_Ioi).mpr
        (.of_forall fun u hu =>
          div_nonneg (gammaCausalProfile_nonneg hγ u) (lt_trans zero_lt_one hu).le))

@[simp] theorem gammaCausalDatum_b₀ (γ : ℝ) (hγ : 0 ≤ γ) : (gammaCausalDatum γ hγ).b₀ = 0 := rfl

theorem gammaCausalDatum_k {γ : ℝ} (hγ : 0 ≤ γ) {u : ℝ} (hu : 0 < u) :
    (gammaCausalDatum γ hγ).k u = γ * Real.exp (-u) := by
  simp [gammaCausalDatum, gammaCausalProfile, hu]

/-! ## The stable profile -/

/-- The causal stable profile `c_α u^{-α}`, `c_α = α/Γ(1-α)`, guarded at the origin. -/
noncomputable def stableCausalProfile (α : ℝ) : ℝ → ℝ :=
  fun u => if 0 < u then α / Real.Gamma (1 - α) * u ^ (-α) else 0

variable {α : ℝ}

theorem stableCausalConst_pos (hα : 0 < α) (hα1 : α < 1) : 0 < α / Real.Gamma (1 - α) :=
  div_pos hα (Real.Gamma_pos_of_pos (by linarith))

theorem stableCausalProfile_nonneg (hα : 0 < α) (hα1 : α < 1) (u : ℝ) :
    0 ≤ stableCausalProfile α u := by
  unfold stableCausalProfile
  split
  · exact mul_nonneg (stableCausalConst_pos hα hα1).le (Real.rpow_nonneg (by linarith) _)
  · exact le_rfl

theorem stableCausalProfile_antitoneOn (hα : 0 < α) (hα1 : α < 1) :
    AntitoneOn (stableCausalProfile α) (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  have hxpos : (0 : ℝ) < x := mem_Ioi.mp hx
  have hypos : (0 : ℝ) < y := mem_Ioi.mp hy
  simp only [stableCausalProfile, if_pos hxpos, if_pos hypos]
  refine mul_le_mul_of_nonneg_left ?_ (stableCausalConst_pos hα hα1).le
  rw [Real.rpow_neg hxpos.le, Real.rpow_neg hypos.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hxpos _) (Real.rpow_le_rpow hxpos.le hxy hα.le)

/-- Integrable at the origin exactly because `α < 1`. -/
theorem integrableOn_stableCausalProfile (hα1 : α < 1) :
    IntegrableOn (stableCausalProfile α) (Ioo (0 : ℝ) 1) := by
  have hrpow : IntegrableOn (fun t : ℝ => t ^ (-α)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < -α)).1
  have hbase : IntegrableOn (fun t : ℝ => α / Real.Gamma (1 - α) * t ^ (-α)) (Ioo 0 1) :=
    IntegrableOn.mono_set (hrpow.const_mul (α / Real.Gamma (1 - α))) Ioo_subset_Ioc_self
  refine IntegrableOn.congr_fun hbase ?_ measurableSet_Ioo
  intro t ht
  rw [stableCausalProfile, if_pos ht.1]

/-- Integrable against `du/u` at infinity exactly because `α > 0`. -/
theorem integrableOn_stableCausalProfile_div (hα : 0 < α) :
    IntegrableOn (fun t => stableCausalProfile α t / t) (Ioi 1) := by
  have hrpow : IntegrableOn (fun t : ℝ => t ^ (-α - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith : -α - 1 < -1) zero_lt_one
  refine IntegrableOn.congr_fun (hrpow.const_mul (α / Real.Gamma (1 - α))) ?_ measurableSet_Ioi
  intro t ht
  have htpos : (0 : ℝ) < t := lt_trans zero_lt_one (mem_Ioi.mp ht)
  simp only [stableCausalProfile, if_pos htpos]
  rw [Real.rpow_sub htpos, Real.rpow_one]
  field_simp

/-- **The causal stable datum** `(0, c_α u^{-α})`, `0 < α < 1`. -/
noncomputable def stableCausalDatum (α : ℝ) (hα : 0 < α) (hα1 : α < 1) : CausalAdmissible where
  b₀ := 0
  k := stableCausalProfile α
  b₀_nonneg := le_rfl
  k_nonneg := fun u _ => stableCausalProfile_nonneg hα hα1 u
  k_antitone := stableCausalProfile_antitoneOn hα hα1
  k_zero := by simp [stableCausalProfile]
  integrable_near_zero :=
    lintegral_ofReal_ne_top_of_integrableOn (integrableOn_stableCausalProfile hα1)
      (.of_forall fun u => stableCausalProfile_nonneg hα hα1 u)
  integrable_at_top :=
    lintegral_ofReal_ne_top_of_integrableOn (integrableOn_stableCausalProfile_div hα)
      ((ae_restrict_iff' measurableSet_Ioi).mpr
        (.of_forall fun u hu =>
          div_nonneg (stableCausalProfile_nonneg hα hα1 u) (lt_trans zero_lt_one hu).le))

@[simp] theorem stableCausalDatum_b₀ (hα : 0 < α) (hα1 : α < 1) :
    (stableCausalDatum α hα hα1).b₀ = 0 := rfl

/-- The profile is homogeneous of degree `-α`: `k(u/c) = c^α k(u)` for `c > 0`, at every real
`u`, the guard making both sides `0` off `(0,∞)`. -/
theorem stableCausalDatum_dilate_k (hα : 0 < α) (hα1 : α < 1) {c : ℝ} (hc : 0 < c) (u : ℝ) :
    (stableCausalDatum α hα hα1).k (u / c) = c ^ α * (stableCausalDatum α hα hα1).k u := by
  change stableCausalProfile α (u / c) = c ^ α * stableCausalProfile α u
  rcases lt_or_ge 0 u with hu | hu
  · have huc : 0 < u / c := div_pos hu hc
    simp only [stableCausalProfile, if_pos hu, if_pos huc]
    rw [Real.div_rpow hu.le hc.le, Real.rpow_neg hc.le]
    field_simp
  · have huc : ¬ 0 < u / c := not_lt.mpr (div_nonpos_of_nonpos_of_nonneg hu hc.le)
    simp [stableCausalProfile, not_lt.mpr hu, huc]

/-- The stable exponent is homogeneous of degree `α`: `F(cσ) = c^α F(σ)` for `c > 0`. -/
theorem stableCausalDatum_exponent_mul (hα : 0 < α) (hα1 : α < 1) {c : ℝ} (hc : 0 < c)
    (σ : ℝ) :
    (stableCausalDatum α hα hα1).exponent (c * σ)
      = c ^ α * (stableCausalDatum α hα hα1).exponent σ := by
  have hcα : 0 ≤ c ^ α := Real.rpow_nonneg hc.le α
  rw [← exponent_dilate _ hc, ← exponent_smul _ hcα]
  simp only [exponent, exponentL, dilate_b₀, dilate_k, smul_b₀, smul_k,
    stableCausalDatum_dilate_k hα hα1 hc, stableCausalDatum_b₀, mul_zero, zero_mul]

/-- `∫₀^∞ e^{-u}c_α u^{-α}\,du = c_αΓ(1-α) = α`: Mathlib's Gamma integral at shape `1 - α`. -/
theorem stableCausalDatum_integral_one (hα : 0 < α) (hα1 : α < 1) :
    (∫ u in Ioi (0 : ℝ), Real.exp (-(1 * u)) * (stableCausalDatum α hα hα1).k u) = α := by
  have hΓ : 0 < Real.Gamma (1 - α) := Real.Gamma_pos_of_pos (by linarith)
  have hpt : ∀ u ∈ Ioi (0 : ℝ), Real.exp (-(1 * u)) * (stableCausalDatum α hα hα1).k u
      = α / Real.Gamma (1 - α) * (u ^ ((1 - α) - 1) * Real.exp (-(1 * u))) := by
    intro u hu
    change Real.exp (-(1 * u)) * stableCausalProfile α u = _
    rw [stableCausalProfile, if_pos (mem_Ioi.mp hu), show (1 - α) - 1 = -α by ring]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith : (0 : ℝ) < 1 - α) one_pos]
  rw [div_one, Real.one_rpow, one_mul]
  field_simp

/-- **The causal stable exponent** `F(σ) = σ^α` on `[0,∞)`, `0 < α < 1`.

Homogeneity gives `F(σ) = σ^α F(1)` for `σ > 0`; differentiating both sides at `σ = 1`,
`hasDerivAt_exponent` and `stableCausalDatum_integral_one` give `αF(1) = α`. The value at the
origin is `exponent_zero`. -/
theorem stableCausalDatum_exponent (hα : 0 < α) (hα1 : α < 1) {σ : ℝ} (hσ : 0 ≤ σ) :
    (stableCausalDatum α hα hα1).exponent σ = σ ^ α := by
  set F := stableCausalDatum α hα hα1 with hF
  have hmul : ∀ c : ℝ, 0 < c → F.exponent c = c ^ α * F.exponent 1 := fun c hc => by
    simpa using stableCausalDatum_exponent_mul hα hα1 hc 1
  have hd1 := F.hasDerivAt_exponent one_pos
  rw [stableCausalDatum_b₀, stableCausalDatum_integral_one, zero_add] at hd1
  have hd2 : HasDerivAt (fun σ : ℝ => σ ^ α * F.exponent 1) (α * 1 ^ (α - 1) * F.exponent 1) 1 :=
    (Real.hasDerivAt_rpow_const (Or.inl one_ne_zero)).mul_const _
  have heq : F.exponent =ᶠ[𝓝 1] fun σ : ℝ => σ ^ α * F.exponent 1 := by
    filter_upwards [Ioi_mem_nhds one_pos] with σ hσ
    exact hmul σ hσ
  have hone : α * 1 ^ (α - 1) * F.exponent 1 = α := (hd2.congr_of_eventuallyEq heq).unique hd1
  have hE : F.exponent 1 = 1 := by
    rw [Real.one_rpow, mul_one] at hone
    exact (mul_eq_left₀ hα.ne').mp hone
  rcases hσ.lt_or_eq with hpos | rfl
  · rw [hmul σ hpos, hE, mul_one]
  · rw [F.exponent_zero, Real.zero_rpow hα.ne']

end CausalAdmissible

end ScaleSpace
