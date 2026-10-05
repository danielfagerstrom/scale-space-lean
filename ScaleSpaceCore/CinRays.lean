/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import ScaleSpaceCore.Cin
import ScaleSpaceCore.SDProfile

/-!
# `lem:cin-rays`(1): the `Cin` rays

`cinSDProfile τ` is the unit-step profile `1_{(0,τ)}` packaged as an `SDProfile`, and `cin_ray`
says its exponent is `Cin(τ·)`. It is defined for every real `τ` — for `τ ≤ 0` it is the zero
profile — because none of the structure's fields needs `τ > 0`; positivity of the step enters
only where the exponent is identified, `cinSDProfile_exponentL`, which is where the split of
`(0,∞)` at `τ` is made.

Moved from the spatial article's export (`SpatialLine.CinRays`, at `cone-v0.1`), statements
unchanged up to the namespace. The superposition clause of `lem:cin-rays`(2), which is stated
through the article's Choquet-measure specification `HasProfileTail`, stayed behind.
-/

namespace ScaleSpace

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## `lem:cin-rays`(1): the ray -/

theorem cinProfile_nonneg (τ : ℝ) (x : ℝ) : 0 ≤ cinProfile τ x := by
  rw [cinProfile]
  by_cases hx : x ∈ Ioo (0 : ℝ) τ <;> simp [hx]

theorem cinProfile_le_one (τ : ℝ) (x : ℝ) : cinProfile τ x ≤ 1 := by
  rw [cinProfile]
  by_cases hx : x ∈ Ioo (0 : ℝ) τ <;> simp [hx]

theorem cinProfile_eq_zero {τ x : ℝ} (hx : x ∉ Ioo (0 : ℝ) τ) : cinProfile τ x = 0 := by
  simp [cinProfile, hx]

theorem cinProfile_eq_one {τ x : ℝ} (hx : x ∈ Ioo (0 : ℝ) τ) : cinProfile τ x = 1 := by
  simp [cinProfile, hx]

theorem antitoneOn_cinProfile (τ : ℝ) : AntitoneOn (cinProfile τ) (Ioi (0 : ℝ)) := by
  intro a ha b hb hab
  by_cases hb' : b ∈ Ioo (0 : ℝ) τ
  · rw [cinProfile_eq_one hb', cinProfile_eq_one ⟨ha, lt_of_le_of_lt hab hb'.2⟩]
  · rw [cinProfile_eq_zero hb']
    exact cinProfile_nonneg τ a

theorem measurable_cinProfile (τ : ℝ) : Measurable (cinProfile τ) :=
  (measurable_const.indicator measurableSet_Ioo)

/-- The `Cin` ray of step `τ` as an `SDProfile`: Gaussian coefficient `0`, profile `1_{(0,τ)}`. -/
noncomputable def cinSDProfile (τ : ℝ) : SDProfile where
  a := 0
  k := cinProfile τ
  a_nonneg := le_rfl
  k_nonneg := fun x _ => cinProfile_nonneg τ x
  k_antitone := antitoneOn_cinProfile τ
  k_zero := cinProfile_eq_zero (by simp)
  integrable_near_zero := by
    have hle : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x * cinProfile τ x))
        ≤ ∫⁻ _ in Ioo (0 : ℝ) 1, 1 := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      refine (ENNReal.ofReal_le_one).mpr ?_
      nlinarith [cinProfile_le_one τ x, cinProfile_nonneg τ x, hx.1.le, hx.2.le]
    refine ne_top_of_le_ne_top ?_ hle
    rw [setLIntegral_one, Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  integrable_at_top := by
    have hle : (∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (cinProfile τ x / x))
        ≤ ∫⁻ x in Ioi (1 : ℝ), (Ioo (0 : ℝ) τ).indicator (fun _ => (1 : ℝ≥0∞)) x := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx1 : (1 : ℝ) < x := hx
      by_cases hxm : x ∈ Ioo (0 : ℝ) τ
      · rw [Set.indicator_of_mem hxm]
        refine (ENNReal.ofReal_le_one).mpr ?_
        rw [div_le_one (by linarith)]
        exact le_trans (cinProfile_le_one τ x) hx1.le
      · rw [cinProfile_eq_zero hxm, zero_div, ENNReal.ofReal_zero]
        exact _root_.zero_le
    refine ne_top_of_le_ne_top ?_ hle
    rw [lintegral_indicator measurableSet_Ioo, setLIntegral_one]
    refine ne_top_of_le_ne_top ?_ (Measure.restrict_apply_le _ _)
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top

theorem cinSDProfile_exponentL {τ : ℝ} (hτ : 0 < τ) (ω : ℝ) :
    (cinSDProfile τ).exponentL ω = ENNReal.ofReal (cin (τ * ω)) := by
  have hzero : (∫⁻ x in Ici τ,
      ENNReal.ofReal ((1 - Real.cos (ω * x)) * cinProfile τ x / x)) = 0 := by
    refine setLIntegral_eq_zero measurableSet_Ici fun x hx => ?_
    rw [cinProfile_eq_zero (by simp only [mem_Ioo, not_and, not_lt]; exact fun _ => hx),
      mul_zero, zero_div, ENNReal.ofReal_zero]
    rfl
  have hdisj : Disjoint (Ioo (0 : ℝ) τ) (Ici τ) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx2⟩ hx3
    exact absurd (mem_Ici.mp hx3) (not_le.mpr hx2)
  have hsplit : (∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal ((1 - Real.cos (ω * x)) * cinProfile τ x / x))
      = ∫⁻ x in Ioo (0 : ℝ) τ, ENNReal.ofReal ((1 - Real.cos (ω * x)) / x) := by
    rw [← Ioo_union_Ici_eq_Ioi hτ, lintegral_union measurableSet_Ici hdisj, hzero, add_zero]
    refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [cinProfile_eq_one hx, mul_one]
  have hint : IntegrableOn (fun x : ℝ => (1 - Real.cos (ω * x)) / x) (Ioo (0 : ℝ) τ) := by
    have h := intervalIntegrable_dilate_cinIntegrand ω hτ.le
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.le] at h
    exact h.mono_set Ioo_subset_Ioc_self
  rw [SDProfile.exponentL, show (cinSDProfile τ).a = 0 from rfl,
    show (cinSDProfile τ).k = cinProfile τ from rfl, zero_mul, ENNReal.ofReal_zero, zero_add,
    hsplit, ← ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_iff' measurableSet_Ioo).mpr
        (.of_forall fun x hx => dilate_cinIntegrand_nonneg ω hx.1.le))]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hτ.le,
    intervalIntegral_dilate_cinIntegrand, mul_comm]

/-- **`lem:cin-rays`(1), the ray.** The unit-step profile `1_{(0,τ)}` is admissible, with Gaussian
coefficient `0`, and its exponent is `Cin(τ·)`. -/
theorem cin_ray {τ : ℝ} (hτ : 0 < τ) :
    ∃ Q : SDProfile, Q.a = 0 ∧ Q.k = cinProfile τ ∧ ∀ ω : ℝ, Q.exponent ω = cin (τ * ω) :=
  ⟨cinSDProfile τ, rfl, rfl, fun ω => by
    rw [SDProfile.exponent, cinSDProfile_exponentL hτ ω,
      ENNReal.toReal_ofReal (cin_nonneg' _)]⟩

end ScaleSpace
