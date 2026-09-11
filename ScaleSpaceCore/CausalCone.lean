/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The causal admissible cone

The data of a self-decomposable law on the half-line, in the form both articles in this line
quantify over: a drift `b₀ ≥ 0` and a nonincreasing delay profile `k ≥ 0` on `(0,∞)`, with
exponent

`F(σ) = b₀σ + ∫₀^∞ (1 - e^{-σu})\,k(u)\,du/u`.

This module is shared across articles. The causal article carries these data as
`Hemigroup.SelfDecomposableExponent`, the spatial article as `SpatialLine.CausalAdmissible` (the
causal side of its subordination bridge); `CausalAdmissible` below is the one type both are meant
to use. Everything here is elementary measure theory and calculus on the half-line.

## The two forms of the finiteness condition

The structure carries the **two integrability windows** `∫₀¹ k < ∞` and `∫₁^∞ k(u)u^{-1}du < ∞`,
which is how the definition is printed. The causal article's structure carries instead the single
condition that the exponent is finite at every `σ ≥ 0`. They are equivalent for `k ≥ 0`
(`ne_top_iff_windows`), and `ofNeTop` builds the structure from the second form, so a consumer
holding that form converts with one call. Both directions go through the one-integral reading
`∫₀^∞ (1 ∧ u)\,k(u)\,du/u < ∞` (`lintegral_min_split`) and the two elementary bounds
`1 - e^{-σu} ≤ (1 ∨ σ)(1 ∧ u)` and `1 ∧ u ≤ 2(1 - e^{-u})`; no measurability is needed.

## The three combinators

Sums, nonnegative multiples and dilations `F ↦ F(c\,\cdot)`, with data `(b₀¹ + b₀², k¹ + k²)`,
`(c b₀, c k)` and `(c b₀, k(\cdot/c))`, and their exponents. The dilation is priced through the
one-integral form, because the change of variables `u = cx` leaves `du/u` alone and turns
`1 ∧ u` into `1 ∧ cx ≤ (1 ∨ c)(1 ∧ x)`.
-/

namespace ScaleSpace

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## Half-line integrals -/

/-- The split `(0,∞) = (0,1) ∪ (1,∞)` of a lower Lebesgue integral; the point `1` is null. -/
theorem lintegral_Ioi_split (f : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioi (0 : ℝ), f t
      = (∫⁻ t in Ioo (0 : ℝ) 1, f t) + ∫⁻ t in Ioi (1 : ℝ), f t := by
  have hsplit : Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 ∪ Ici (1 : ℝ) := by
    ext x
    constructor
    · intro hx
      rcases lt_or_ge x 1 with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
    · rintro (⟨hx, -⟩ | hx)
      · exact hx
      · exact lt_of_lt_of_le zero_lt_one (mem_Ici.mp hx)
  have hdisj : Disjoint (Ioo (0 : ℝ) 1) (Ici (1 : ℝ)) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx1⟩ hx
    exact absurd (mem_Ici.mp hx) (not_le.mpr hx1)
  rw [hsplit, lintegral_union measurableSet_Ici hdisj]
  congr 1
  exact setLIntegral_congr Ioi_ae_eq_Ici.symm

/-- The image of Lebesgue measure on `(0,∞)` under `x ↦ cx`, `c > 0`, is `c⁻¹` times itself. -/
theorem map_mul_restrict_Ioi {c : ℝ} (hc : 0 < c) :
    Measure.map (fun x : ℝ => c * x) (volume.restrict (Ioi (0 : ℝ)))
      = ENNReal.ofReal c⁻¹ • volume.restrict (Ioi (0 : ℝ)) := by
  have hpre : (fun x : ℝ => c * x) ⁻¹' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext x
    simp only [mem_preimage, mem_Ioi, mul_pos_iff_of_pos_left hc]
  have h1 : Measure.map (fun x : ℝ => c * x) (volume.restrict (Ioi (0 : ℝ)))
      = (Measure.map (fun x : ℝ => c * x) volume).restrict (Ioi (0 : ℝ)) := by
    rw [Measure.restrict_map (measurable_const_mul c) measurableSet_Ioi, hpre]
  rw [h1, Real.map_volume_mul_left hc.ne', Measure.restrict_smul,
    abs_of_pos (inv_pos.mpr hc)]

/-- **The change of variables `u = cx` on the half-line**, for an arbitrary `ℝ≥0∞`-valued
integrand: `∫_{(0,∞)} G = c ∫_{(0,∞)} G(c\,\cdot)`. No measurability of `G` is needed. -/
theorem setLIntegral_Ioi_comp_mul {c : ℝ} (hc : 0 < c) (G : ℝ → ℝ≥0∞) :
    (∫⁻ u in Ioi (0 : ℝ), G u) = ENNReal.ofReal c * ∫⁻ x in Ioi (0 : ℝ), G (c * x) := by
  have hemb : MeasurableEmbedding (fun x : ℝ => c * x) :=
    (Homeomorph.mulLeft₀ c hc.ne').toMeasurableEquiv.measurableEmbedding
  have hpush : ∫⁻ u, G u ∂(Measure.map (fun x : ℝ => c * x) (volume.restrict (Ioi (0 : ℝ))))
      = ∫⁻ x in Ioi (0 : ℝ), G (c * x) := hemb.lintegral_map G
  rw [map_mul_restrict_Ioi hc, lintegral_smul_measure, smul_eq_mul] at hpush
  rw [← hpush, ← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne',
    ENNReal.ofReal_one, one_mul]

/-- An integrable, a.e. nonnegative function has a finite lower integral of its `ofReal`. -/
theorem lintegral_ofReal_ne_top_of_integrableOn {f : ℝ → ℝ} {s : Set ℝ}
    (hf : IntegrableOn f s) (hnn : ∀ᵐ x ∂(volume.restrict s), 0 ≤ f x) :
    (∫⁻ x in s, ENNReal.ofReal (f x)) ≠ ⊤ := by
  rw [← ofReal_integral_eq_lintegral_ofReal hf hnn]
  exact ENNReal.ofReal_ne_top

/-! ## The structure -/

/-- **The causal admissible cone**: a drift `b₀ ≥ 0` and a nonincreasing delay profile `k ≥ 0`
on `(0,∞)` with `∫₀¹ k < ∞` and `∫₁^∞ k(u)u^{-1}du < ∞` (`blueprint: def:causal-admissible`).

The field layout and names are the causal article's `Hemigroup.SelfDecomposableExponent`; the
last two fields are the pair of integrability windows rather than its single finiteness field
`ne_top`, which is recovered as `exponentL_ne_top` and accepted by `ofNeTop`. -/
structure CausalAdmissible where
  /-- The drift coefficient. -/
  b₀ : ℝ
  /-- The delay profile, a density against `du/u` on `(0,∞)`. -/
  k : ℝ → ℝ
  b₀_nonneg : 0 ≤ b₀
  k_nonneg : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ k u
  k_antitone : AntitoneOn k (Ioi (0 : ℝ))
  /-- A normalisation, not a constraint: every other field leaves `k 0` free. -/
  k_zero : k 0 = 0
  /-- `∫₀¹ k(u)\,du < ∞`. -/
  integrable_near_zero : ∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (k u) ≠ ⊤
  /-- `∫₁^∞ k(u)\,u^{-1}du < ∞`. -/
  integrable_at_top : ∫⁻ u in Ioi (1 : ℝ), ENNReal.ofReal (k u / u) ≠ ⊤

namespace CausalAdmissible

/-- **The causal exponent** `F(σ) = b₀σ + ∫₀^∞ (1 - e^{-σu})\,k(u)\,du/u`, `ℝ≥0∞`-valued.

Definitionally the causal article's `Hemigroup.levyExponentD F.b₀ F.k`. -/
noncomputable def exponentL (F : CausalAdmissible) (σ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (F.b₀ * σ)
    + ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(σ * u))) * F.k u / u)

/-- The real-valued causal exponent. -/
noncomputable def exponent (F : CausalAdmissible) (σ : ℝ) : ℝ := (F.exponentL σ).toReal

section Exponent

variable (F : CausalAdmissible)

/-! ## Measurability -/

/-- The delay profile is a.e. measurable on `(0,∞)`: it is antitone there. -/
theorem aemeasurable_k : AEMeasurable F.k (volume.restrict (Ioi (0 : ℝ))) :=
  aemeasurable_restrict_of_antitoneOn measurableSet_Ioi F.k_antitone

theorem aemeasurable_k_mono {s : Set ℝ} (hs : s ⊆ Ioi (0 : ℝ)) :
    AEMeasurable F.k (volume.restrict s) :=
  F.aemeasurable_k.mono_measure (Measure.restrict_mono hs le_rfl)

/-! ## The two integrability windows, as real integrals -/

/-- `k` is integrable on `(0,1)`: the first window, read as a Bochner statement. -/
theorem integrableOn_k_Ioo : IntegrableOn F.k (Ioo (0 : ℝ) 1) := by
  refine ⟨(F.aemeasurable_k_mono Ioo_subset_Ioi_self).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal]
  · exact lt_top_iff_ne_top.mpr F.integrable_near_zero
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact F.k_nonneg u (Ioo_subset_Ioi_self hu)

/-- `k(u)/u` is integrable on `(1,∞)`: the second window, read as a Bochner statement. -/
theorem integrableOn_k_div_Ioi : IntegrableOn (fun u => F.k u / u) (Ioi (1 : ℝ)) := by
  have hsub : Ioi (1 : ℝ) ⊆ Ioi (0 : ℝ) := fun _ hx => lt_trans zero_lt_one (mem_Ioi.mp hx)
  refine ⟨((F.aemeasurable_k_mono hsub).div aemeasurable_id).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal]
  · exact lt_top_iff_ne_top.mpr F.integrable_at_top
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact div_nonneg (F.k_nonneg u (hsub hu)) (le_of_lt (lt_trans zero_lt_one (mem_Ioi.mp hu)))

/-! ## The elementary inequalities -/

/-- `x ≤ e^x`, in the form `u e^{-σu} ≤ σ^{-1}` for `σ > 0`. -/
theorem mul_exp_neg_le {σ : ℝ} (hσ : 0 < σ) (u : ℝ) :
    u * Real.exp (-(σ * u)) ≤ σ⁻¹ := by
  have hx : σ * u ≤ Real.exp (σ * u) := by
    have := Real.add_one_le_exp (σ * u)
    linarith
  have hpos : (0 : ℝ) < Real.exp (σ * u) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos, inv_mul_eq_div, le_div_iff₀ hσ]
  nlinarith

/-- `0 ≤ 1 - e^{-σu} ≤ σu` for `σ, u ≥ 0`. -/
theorem one_sub_exp_bounds {σ u : ℝ} (hσ : 0 ≤ σ) (hu : 0 ≤ u) :
    0 ≤ 1 - Real.exp (-(σ * u)) ∧ 1 - Real.exp (-(σ * u)) ≤ σ * u := by
  constructor
  · have := Real.exp_le_one_iff.mpr (by nlinarith : -(σ * u) ≤ 0)
    linarith
  · have := Real.add_one_le_exp (-(σ * u))
    linarith

/-! ## The splitting of `(0,∞)` -/

theorem Ioi_zero_eq_union : Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 ∪ Ici (1 : ℝ) := by
  ext x
  constructor
  · intro hx
    rcases lt_or_ge x 1 with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr h
  · rintro (⟨hx, -⟩ | hx)
    · exact hx
    · exact lt_of_lt_of_le zero_lt_one (mem_Ici.mp hx)

/-- `k(u)/u` is integrable on `[1,∞)`, the closed window the union splitting uses. -/
theorem integrableOn_k_div_Ici : IntegrableOn (fun u => F.k u / u) (Ici (1 : ℝ)) :=
  (F.integrableOn_k_div_Ioi).congr_set_ae Ioi_ae_eq_Ici.symm

theorem aemeasurable_k_Ioo : AEMeasurable F.k (volume.restrict (Ioo (0 : ℝ) 1)) :=
  F.aemeasurable_k_mono Ioo_subset_Ioi_self

theorem aemeasurable_k_Ici : AEMeasurable F.k (volume.restrict (Ici (1 : ℝ))) :=
  F.aemeasurable_k_mono fun _ hx => lt_of_lt_of_le zero_lt_one (mem_Ici.mp hx)

theorem measurable_expIntegrand (σ : ℝ) : Measurable fun u : ℝ => Real.exp (-(σ * u)) := by
  fun_prop

/-! ## The exponent's integrand -/

/-- The integrand of `F` is integrable on `(0,∞)` at every nonnegative frequency. -/
theorem integrableOn_exponentIntegrand {σ : ℝ} (hσ : 0 ≤ σ) :
    IntegrableOn (fun u => (1 - Real.exp (-(σ * u))) * F.k u / u) (Ioi (0 : ℝ)) := by
  rw [Ioi_zero_eq_union]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' ((F.integrableOn_k_Ioo).const_mul σ)
      ((((measurable_const.sub (measurable_expIntegrand σ)).aemeasurable.mul
        F.aemeasurable_k_Ioo).div aemeasurable_id).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hu0 : (0 : ℝ) < u := hu.1
    have hk : 0 ≤ F.k u := F.k_nonneg u (Ioo_subset_Ioi_self hu)
    obtain ⟨hlo, hhi⟩ := one_sub_exp_bounds hσ hu0.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hu0]
    nlinarith
  · refine Integrable.mono' (F.integrableOn_k_div_Ici)
      ((((measurable_const.sub (measurable_expIntegrand σ)).aemeasurable.mul
        F.aemeasurable_k_Ici).div aemeasurable_id).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    have hu1 : (1 : ℝ) ≤ u := hu
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu1
    have hk : 0 ≤ F.k u := F.k_nonneg u hu0
    obtain ⟨hlo, -⟩ := one_sub_exp_bounds hσ hu0.le
    have hnum : (1 - Real.exp (-(σ * u))) * F.k u ≤ F.k u := by
      nlinarith [Real.exp_pos (-(σ * u))]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr

/-- The integrand of `F'` is integrable on `(0,∞)` at every **positive** frequency. At `σ = 0`
this is false in general: `∫₀^∞ k` need not converge. -/
theorem integrableOn_derivIntegrand {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun u => Real.exp (-(σ * u)) * F.k u) (Ioi (0 : ℝ)) := by
  rw [Ioi_zero_eq_union]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' (F.integrableOn_k_Ioo)
      (((measurable_expIntegrand σ).aemeasurable.mul
        F.aemeasurable_k_Ioo).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hu0 : (0 : ℝ) < u := hu.1
    have hk : 0 ≤ F.k u := F.k_nonneg u (Ioo_subset_Ioi_self hu)
    have hexp : Real.exp (-(σ * u)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith : -(σ * u) ≤ 0)
    have hep := Real.exp_pos (-(σ * u))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith
  · refine Integrable.mono' ((F.integrableOn_k_div_Ici).const_mul σ⁻¹)
      (((measurable_expIntegrand σ).aemeasurable.mul
        F.aemeasurable_k_Ici).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    have hu1 : (1 : ℝ) ≤ u := hu
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu1
    have hk : 0 ≤ F.k u := F.k_nonneg u hu0
    have hep := Real.exp_pos (-(σ * u))
    have hmul := mul_exp_neg_le hσ u
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hkey : Real.exp (-(σ * u)) * F.k u
        = (u * Real.exp (-(σ * u))) * (F.k u / u) := by
      field_simp
    rw [hkey]
    exact mul_le_mul_of_nonneg_right hmul (by positivity)

/-! ## The exponent as a real integral -/

/-- The integrand of `F` is nonnegative on `(0,∞)`. -/
theorem exponentIntegrand_nonneg {σ : ℝ} (hσ : 0 ≤ σ) {u : ℝ} (hu : 0 < u) :
    0 ≤ (1 - Real.exp (-(σ * u))) * F.k u / u := by
  have hk : 0 ≤ F.k u := F.k_nonneg u hu
  obtain ⟨hlo, -⟩ := one_sub_exp_bounds hσ hu.le
  positivity

theorem lintegral_exponentIntegrand_ne_top {σ : ℝ} (hσ : 0 ≤ σ) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(σ * u))) * F.k u / u)) ≠ ⊤ := by
  have h2 := (F.integrableOn_exponentIntegrand hσ).2
  rw [hasFiniteIntegral_iff_ofReal] at h2
  · exact h2.ne
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact F.exponentIntegrand_nonneg hσ hu

/-- **`F` is finite at every nonnegative frequency**: the causal article's field `ne_top`. -/
theorem exponentL_ne_top {σ : ℝ} (hσ : 0 ≤ σ) : F.exponentL σ ≠ ⊤ := by
  rw [exponentL]
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, F.lintegral_exponentIntegrand_ne_top hσ⟩

/-- The exponent as a Bochner integral: `F(σ) = b₀σ + ∫₀^∞ (1 - e^{-σu}) k(u)\,du/u`, `σ ≥ 0`. -/
theorem exponent_eq {σ : ℝ} (hσ : 0 ≤ σ) :
    F.exponent σ = F.b₀ * σ + ∫ u in Ioi (0 : ℝ), (1 - Real.exp (-(σ * u))) * F.k u / u := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun u => (1 - Real.exp (-(σ * u))) * F.k u / u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact F.exponentIntegrand_nonneg hσ hu
  have hmeas : AEStronglyMeasurable (fun u => (1 - Real.exp (-(σ * u))) * F.k u / u)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (((measurable_const.sub (measurable_expIntegrand σ)).aemeasurable.mul
      F.aemeasurable_k).div aemeasurable_id).aestronglyMeasurable
  rw [exponent, exponentL,
    ENNReal.toReal_add ENNReal.ofReal_ne_top (F.lintegral_exponentIntegrand_ne_top hσ),
    ENNReal.toReal_ofReal (mul_nonneg F.b₀_nonneg hσ)]
  congr 1
  exact (integral_eq_lintegral_of_nonneg_ae hnn hmeas).symm

theorem exponent_zero : F.exponent 0 = 0 := by
  rw [F.exponent_eq le_rfl]
  simp

/-! ## Differentiation under the integral sign -/

/-- **`F'(σ) = b₀ + ∫₀^∞ e^{-σu} k(u)\,du`** at every positive frequency.

The dominating function on `(σ/2, 2σ)` is `e^{-σu/2}k(u)`, integrable by
`integrableOn_derivIntegrand`. -/
theorem hasDerivAt_exponent {σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt F.exponent
      (F.b₀ + ∫ u in Ioi (0 : ℝ), Real.exp (-(σ * u)) * F.k u) σ := by
  have hhalf : (0 : ℝ) < σ / 2 := by linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun x u => (1 - Real.exp (-(x * u))) * F.k u / u)
    (F' := fun x u => Real.exp (-(x * u)) * F.k u)
    (bound := fun u => Real.exp (-(σ / 2 * u)) * F.k u) (x₀ := σ) (s := Ioo (σ / 2) (2 * σ))
    (Ioo_mem_nhds (by linarith) (by linarith))
    (.of_forall fun x =>
      (((measurable_const.sub (measurable_expIntegrand x)).aemeasurable.mul
        F.aemeasurable_k).div aemeasurable_id).aestronglyMeasurable)
    (F.integrableOn_exponentIntegrand hσ.le)
    (((measurable_expIntegrand σ).aemeasurable.mul F.aemeasurable_k).aestronglyMeasurable)
    ?bound (F.integrableOn_derivIntegrand hhalf) ?diff
  case bound =>
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu x hx
    have hu0 : (0 : ℝ) < u := hu
    have hk : 0 ≤ F.k u := F.k_nonneg u hu0
    have hmono : Real.exp (-(x * u)) ≤ Real.exp (-(σ / 2 * u)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hx.1]
    have hep := Real.exp_pos (-(x * u))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right hmono hk
  case diff =>
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu x _
    have hu0 : (0 : ℝ) < u := hu
    have hlin : HasDerivAt (fun y : ℝ => y * u) u x := by
      simpa using (hasDerivAt_id x).mul_const u
    have hin : HasDerivAt (fun y : ℝ => -(y * u)) (-u) x := by
      simpa [Pi.neg_def] using hlin.neg
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (-(y * u)))
        (Real.exp (-(x * u)) * (-u)) x := hin.exp
    have hsub : HasDerivAt (fun y : ℝ => 1 - Real.exp (-(y * u)))
        (u * Real.exp (-(x * u))) x := by
      have h := hexp.const_sub 1
      have hval : -(Real.exp (-(x * u)) * (-u)) = u * Real.exp (-(x * u)) := by ring
      rwa [hval] at h
    have hmul := (hsub.mul_const (F.k u)).div_const u
    have heq : u * Real.exp (-(x * u)) * F.k u / u = Real.exp (-(x * u)) * F.k u := by
      field_simp
    rwa [heq] at hmul
  have heq : F.exponent
      =ᶠ[𝓝 σ] fun x : ℝ => F.b₀ * x + ∫ u in Ioi (0 : ℝ), (1 - Real.exp (-(x * u))) * F.k u / u :=
    by
      filter_upwards [Ioi_mem_nhds (show σ / 2 < σ by linarith)] with x hx
      exact F.exponent_eq (by linarith [mem_Ioi.mp hx])
  have hlin : HasDerivAt (fun x : ℝ => F.b₀ * x) F.b₀ σ := by
    simpa using (hasDerivAt_id σ).const_mul F.b₀
  exact ((hlin.add key.2).congr_of_eventuallyEq heq)

/-! ## Positivity of the derivative -/

/-- If the data vanish, so does the exponent on `[0,∞)`. -/
theorem exponent_eq_zero_of_trivial (hb : F.b₀ = 0)
    (hk : F.k =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0) {σ : ℝ} (hσ : 0 ≤ σ) : F.exponent σ = 0 := by
  rw [F.exponent_eq hσ, hb, zero_mul, zero_add]
  have hz : (fun u => (1 - Real.exp (-(σ * u))) * F.k u / u)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
    filter_upwards [hk] with u hu
    simp [hu]
  rw [integral_congr_ae hz]
  simp

/-- **`F' > 0` on `(0,∞)` for every nonzero `F`.** The derivative is `b₀ + ∫₀^∞ e^{-σu}k(u)\,du`;
if it vanishes then `b₀ = 0` and `k = 0` a.e. on `(0,∞)`, and then `F` vanishes on `[0,∞)`. The
representing measure is given by the structure, so no Bernstein theorem is involved. -/
theorem deriv_integral_pos {σ : ℝ} (hσ : 0 < σ)
    (hne : ∃ τ : ℝ, 0 ≤ τ ∧ F.exponent τ ≠ 0) :
    0 < F.b₀ + ∫ u in Ioi (0 : ℝ), Real.exp (-(σ * u)) * F.k u := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun u => Real.exp (-(σ * u)) * F.k u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (Real.exp_pos _).le (F.k_nonneg u hu)
  have hint : 0 ≤ ∫ u in Ioi (0 : ℝ), Real.exp (-(σ * u)) * F.k u :=
    integral_nonneg_of_ae hnn
  rcases lt_or_eq_of_le (by linarith [F.b₀_nonneg] :
      (0 : ℝ) ≤ F.b₀ + ∫ u in Ioi (0 : ℝ), Real.exp (-(σ * u)) * F.k u) with h | h
  · exact h
  exfalso
  obtain ⟨τ, hτ, hτne⟩ := hne
  have hb : F.b₀ = 0 := by linarith [F.b₀_nonneg]
  have hzero : (∫ u in Ioi (0 : ℝ), Real.exp (-(σ * u)) * F.k u) = 0 := by linarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn (F.integrableOn_derivIntegrand hσ)).mp hzero
  have hk : F.k =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
    filter_upwards [hae] with u hu
    have := Real.exp_pos (-(σ * u))
    simpa [Pi.zero_apply, mul_eq_zero, this.ne'] using hu
  exact hτne (F.exponent_eq_zero_of_trivial hb hk hτ)

end Exponent

/-! ## The two field forms -/

/-- The two integrability windows are the two halves of `∫₀^∞ (1 ∧ u)k(u)\,du/u`. -/
theorem lintegral_min_split (k : ℝ → ℝ) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (min 1 u * k u / u))
      = (∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (k u))
        + ∫⁻ u in Ioi (1 : ℝ), ENNReal.ofReal (k u / u) := by
  rw [lintegral_Ioi_split]
  congr 1
  · refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu.1
    have hmin : min 1 u = u := min_eq_right hu.2.le
    rw [hmin]
    congr 1
    field_simp
  · refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
    rw [min_eq_left hu1]
    congr 1
    ring

/-- The one-integral form of the two windows, for a causally admissible datum. -/
theorem lintegral_min_ne_top (F : CausalAdmissible) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (min 1 u * F.k u / u)) ≠ ⊤ := by
  rw [lintegral_min_split]
  exact ENNReal.add_ne_top.mpr ⟨F.integrable_near_zero, F.integrable_at_top⟩

/-- `1 ∧ cx ≤ (1 ∨ c)(1 ∧ x)` for `x > 0`: the inequality that prices a dilation, and a
frequency `σ`, against the undilated one-integral form. -/
theorem min_one_mul_le (c : ℝ) {x : ℝ} (hx : 0 < x) :
    min 1 (c * x) ≤ max 1 c * min 1 x := by
  have hc1 : (1 : ℝ) ≤ max 1 c := le_max_left _ _
  have hcc : c ≤ max 1 c := le_max_right _ _
  rcases le_or_gt (c * x) 1 with hcx | hcx
  · rw [min_eq_right hcx]
    rcases le_or_gt x 1 with hx1 | hx1
    · rw [min_eq_right hx1]
      nlinarith
    · rw [min_eq_left hx1.le]
      linarith
  · rw [min_eq_left hcx.le]
    rcases le_or_gt x 1 with hx1 | hx1
    · rw [min_eq_right hx1]
      nlinarith
    · rw [min_eq_left hx1.le]
      linarith

/-- `1 ∧ u ≤ 2(1 - e^{-u})` for `u > 0`: from `e^u ≥ 1 + u`, `1 - e^{-u} ≥ u/(1+u)`. -/
theorem min_one_le_two_mul_one_sub_exp {u : ℝ} (hu : 0 < u) :
    min 1 u ≤ 2 * (1 - Real.exp (-(1 * u))) := by
  have h1 : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hprod : Real.exp (-(1 * u)) * Real.exp u = 1 := by
    rw [one_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hep := Real.exp_pos (-(1 * u))
  have hkey : Real.exp (-(1 * u)) * (1 + u) ≤ 1 := by
    calc Real.exp (-(1 * u)) * (1 + u) ≤ Real.exp (-(1 * u)) * Real.exp u :=
          mul_le_mul_of_nonneg_left h1 hep.le
      _ = 1 := hprod
  rcases le_or_gt u 1 with hu1 | hu1
  · rw [min_eq_right hu1]
    nlinarith
  · rw [min_eq_left hu1.le]
    nlinarith

/-- **Windows to finiteness**: if `k ≥ 0` meets both windows, the exponent's integral is finite at
every `σ ≥ 0`, by `1 - e^{-σu} ≤ 1 ∧ σu ≤ (1 ∨ σ)(1 ∧ u)`. -/
theorem lintegral_exponentIntegrand_ne_top_of_windows {k : ℝ → ℝ}
    (hk : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ k u)
    (h0 : ∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (k u) ≠ ⊤)
    (h1 : ∫⁻ u in Ioi (1 : ℝ), ENNReal.ofReal (k u / u) ≠ ⊤) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(σ * u))) * k u / u)) ≠ ⊤ := by
  have hmin : (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (min 1 u * k u / u)) ≠ ⊤ := by
    rw [lintegral_min_split]
    exact ENNReal.add_ne_top.mpr ⟨h0, h1⟩
  have hle : (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(σ * u))) * k u / u))
      ≤ ENNReal.ofReal (max 1 σ) * ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (min 1 u * k u / u) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := hu
    have hku : 0 ≤ k u := hk u hu0
    obtain ⟨hlo, hhi⟩ := one_sub_exp_bounds hσ hu0.le
    have hone : 1 - Real.exp (-(σ * u)) ≤ 1 := by linarith [Real.exp_pos (-(σ * u))]
    have hm : 1 - Real.exp (-(σ * u)) ≤ max 1 σ * min 1 u :=
      (le_min hone hhi).trans (min_one_mul_le σ hu0)
    rw [← ENNReal.ofReal_mul (le_trans zero_le_one (le_max_left _ _))]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_div_assoc', ← mul_assoc]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hm hku) hu0.le
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmin) hle

/-- **Finiteness to windows**: finiteness of the exponent's integral at `σ = 1` alone forces both
windows, by `1 ∧ u ≤ 2(1 - e^{-u})`. -/
theorem windows_of_lintegral_exponentIntegrand_ne_top {k : ℝ → ℝ}
    (hk : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ k u)
    (h : (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(1 * u))) * k u / u)) ≠ ⊤) :
    (∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (k u)) ≠ ⊤
      ∧ (∫⁻ u in Ioi (1 : ℝ), ENNReal.ofReal (k u / u)) ≠ ⊤ := by
  have hle : (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (min 1 u * k u / u))
      ≤ ENNReal.ofReal 2
        * ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(1 * u))) * k u / u) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := hu
    have hku : 0 ≤ k u := hk u hu0
    rw [← ENNReal.ofReal_mul zero_le_two]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_div_assoc', ← mul_assoc]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_one_le_two_mul_one_sub_exp hu0) hku) hu0.le
  have hfin := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h) hle
  rw [lintegral_min_split] at hfin
  exact ENNReal.add_ne_top.mp hfin

/-- **The two field forms are equivalent.** For `k ≥ 0` on `(0,∞)`, the causal article's
single condition — the exponent is finite at every `σ ≥ 0` — holds exactly when the two
integrability windows do. Neither the sign of `b₀` nor the monotonicity of `k` is used. -/
theorem ne_top_iff_windows (b₀ : ℝ) {k : ℝ → ℝ} (hk : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ k u) :
    (∀ σ, 0 ≤ σ → (ENNReal.ofReal (b₀ * σ)
        + ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(σ * u))) * k u / u)) ≠ ⊤)
      ↔ (∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (k u)) ≠ ⊤
        ∧ (∫⁻ u in Ioi (1 : ℝ), ENNReal.ofReal (k u / u)) ≠ ⊤ := by
  constructor
  · intro h
    exact windows_of_lintegral_exponentIntegrand_ne_top hk
      (ENNReal.add_ne_top.mp (h 1 zero_le_one)).2
  · rintro ⟨h0, h1⟩ σ hσ
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.ofReal_ne_top, lintegral_exponentIntegrand_ne_top_of_windows hk h0 h1 hσ⟩

/-- **The constructor from the causal article's field form**: the four sign, monotonicity and
normalisation fields and the finiteness of the exponent at every `σ ≥ 0`, which is
`Hemigroup.SelfDecomposableExponent.ne_top` up to unfolding `levyExponentD`. -/
noncomputable def ofNeTop (b₀ : ℝ) (k : ℝ → ℝ) (b₀_nonneg : 0 ≤ b₀)
    (k_nonneg : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ k u) (k_antitone : AntitoneOn k (Ioi (0 : ℝ)))
    (k_zero : k 0 = 0)
    (ne_top : ∀ σ, 0 ≤ σ → (ENNReal.ofReal (b₀ * σ)
        + ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(σ * u))) * k u / u)) ≠ ⊤) :
    CausalAdmissible where
  b₀ := b₀
  k := k
  b₀_nonneg := b₀_nonneg
  k_nonneg := k_nonneg
  k_antitone := k_antitone
  k_zero := k_zero
  integrable_near_zero := ((ne_top_iff_windows b₀ k_nonneg).mp ne_top).1
  integrable_at_top := ((ne_top_iff_windows b₀ k_nonneg).mp ne_top).2

section OfNeTop

variable {b₀ : ℝ} {k : ℝ → ℝ} {hb : 0 ≤ b₀} {hk : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ k u}
  {hanti : AntitoneOn k (Ioi (0 : ℝ))} {hk0 : k 0 = 0}
  {hne : ∀ σ, 0 ≤ σ → (ENNReal.ofReal (b₀ * σ)
    + ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(σ * u))) * k u / u)) ≠ ⊤}

@[simp] theorem ofNeTop_b₀ : (ofNeTop b₀ k hb hk hanti hk0 hne).b₀ = b₀ := rfl

@[simp] theorem ofNeTop_k : (ofNeTop b₀ k hb hk hanti hk0 hne).k = k := rfl

/-- The exponent of `ofNeTop` is the exponent the finiteness hypothesis is about, by `rfl`. -/
theorem ofNeTop_exponentL (σ : ℝ) :
    (ofNeTop b₀ k hb hk hanti hk0 hne).exponentL σ = ENNReal.ofReal (b₀ * σ)
      + ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(σ * u))) * k u / u) := rfl

end OfNeTop

/-! ## The sum -/

/-- **The sum of two causally admissible data**, with data `(b₀¹ + b₀², k¹ + k²)`. -/
noncomputable def add (F G : CausalAdmissible) : CausalAdmissible where
  b₀ := F.b₀ + G.b₀
  k := fun u => F.k u + G.k u
  b₀_nonneg := add_nonneg F.b₀_nonneg G.b₀_nonneg
  k_nonneg := fun u hu => add_nonneg (F.k_nonneg u hu) (G.k_nonneg u hu)
  k_antitone := fun _ hx _ hy hxy =>
    add_le_add (F.k_antitone hx hy hxy) (G.k_antitone hx hy hxy)
  k_zero := by simp [F.k_zero, G.k_zero]
  integrable_near_zero := by
    have hm : AEMeasurable (fun u : ℝ => ENNReal.ofReal (F.k u))
        (volume.restrict (Ioo (0 : ℝ) 1)) := F.aemeasurable_k_Ioo.ennreal_ofReal
    have hsplit : (∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (F.k u + G.k u))
        = (∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (F.k u))
          + ∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (G.k u) := by
      rw [← lintegral_add_left' hm]
      refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
      exact ENNReal.ofReal_add (F.k_nonneg u (Ioo_subset_Ioi_self hu))
        (G.k_nonneg u (Ioo_subset_Ioi_self hu))
    rw [hsplit]
    exact ENNReal.add_ne_top.mpr ⟨F.integrable_near_zero, G.integrable_near_zero⟩
  integrable_at_top := by
    have hsub : Ioi (1 : ℝ) ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi zero_le_one
    have hm : AEMeasurable (fun u : ℝ => ENNReal.ofReal (F.k u / u))
        (volume.restrict (Ioi (1 : ℝ))) :=
      ((F.aemeasurable_k_mono hsub).div aemeasurable_id).ennreal_ofReal
    have hsplit : (∫⁻ u in Ioi (1 : ℝ), ENNReal.ofReal ((F.k u + G.k u) / u))
        = (∫⁻ u in Ioi (1 : ℝ), ENNReal.ofReal (F.k u / u))
          + ∫⁻ u in Ioi (1 : ℝ), ENNReal.ofReal (G.k u / u) := by
      rw [← lintegral_add_left' hm]
      refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
      have hu0 : (0 : ℝ) < u := hsub hu
      rw [← ENNReal.ofReal_add (div_nonneg (F.k_nonneg u hu0) hu0.le)
        (div_nonneg (G.k_nonneg u hu0) hu0.le)]
      congr 1
      ring
    rw [hsplit]
    exact ENNReal.add_ne_top.mpr ⟨F.integrable_at_top, G.integrable_at_top⟩

/-! ## The nonnegative multiple -/

/-- **A nonnegative multiple of a causally admissible datum**, with data `(c b₀, c k)`. -/
noncomputable def smul (F : CausalAdmissible) {c : ℝ} (hc : 0 ≤ c) : CausalAdmissible where
  b₀ := c * F.b₀
  k := fun u => c * F.k u
  b₀_nonneg := mul_nonneg hc F.b₀_nonneg
  k_nonneg := fun u hu => mul_nonneg hc (F.k_nonneg u hu)
  k_antitone := fun _ hx _ hy hxy => mul_le_mul_of_nonneg_left (F.k_antitone hx hy hxy) hc
  k_zero := by simp [F.k_zero]
  integrable_near_zero := by
    have hsplit : (∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (c * F.k u))
        = ENNReal.ofReal c * ∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (F.k u) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
      rw [← ENNReal.ofReal_mul hc]
    rw [hsplit]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top F.integrable_near_zero
  integrable_at_top := by
    have hsplit : (∫⁻ u in Ioi (1 : ℝ), ENNReal.ofReal (c * F.k u / u))
        = ENNReal.ofReal c * ∫⁻ u in Ioi (1 : ℝ), ENNReal.ofReal (F.k u / u) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      rw [← ENNReal.ofReal_mul hc]
      congr 1
      ring
    rw [hsplit]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top F.integrable_at_top

/-! ## The dilation -/

/-- The dilated datum meets the one-integral form of the two windows. -/
theorem lintegral_min_dilate_ne_top (F : CausalAdmissible) {c : ℝ} (hc : 0 < c) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (min 1 u * F.k (u / c) / u)) ≠ ⊤ := by
  rw [setLIntegral_Ioi_comp_mul hc]
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
  have hbound : ∀ x ∈ Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (c * x) * F.k (c * x / c) / (c * x))
        ≤ ENNReal.ofReal (max 1 c / c) * ENNReal.ofReal (min 1 x * F.k x / x) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hk : 0 ≤ F.k x := F.k_nonneg x hx0
    have hcancel : c * x / c = x := by field_simp
    rw [hcancel, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hmin := min_one_mul_le c hx0
    have hmin0 : 0 ≤ min 1 x := le_min zero_le_one hx0.le
    have hstep : min 1 (c * x) * F.k x ≤ max 1 c * min 1 x * F.k x :=
      mul_le_mul_of_nonneg_right hmin hk
    have hpos : (0 : ℝ) < c * x := by positivity
    rw [div_le_iff₀ hpos]
    have hrhs : max 1 c / c * (min 1 x * F.k x / x) * (c * x)
        = max 1 c * min 1 x * F.k x := by field_simp
    rw [hrhs]
    exact hstep
  have hle : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (c * x) * F.k (c * x / c) / (c * x)))
      ≤ ENNReal.ofReal (max 1 c / c)
        * ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (min 1 x * F.k x / x) := by
    have hmeas : AEMeasurable (fun a : ℝ => ENNReal.ofReal (min 1 a * F.k a / a))
        (volume.restrict (Ioi (0 : ℝ))) :=
      (((aemeasurable_const.min aemeasurable_id).mul F.aemeasurable_k).div
        aemeasurable_id).ennreal_ofReal
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact setLIntegral_mono_ae (aemeasurable_const.mul hmeas) (.of_forall hbound)
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top F.lintegral_min_ne_top) hle

/-- **The dilation of a causally admissible datum**, `F ↦ F(c\,\cdot)`, with data
`(c b₀, k(\cdot/c))`. -/
noncomputable def dilate (F : CausalAdmissible) {c : ℝ} (hc : 0 < c) : CausalAdmissible where
  b₀ := c * F.b₀
  k := fun u => F.k (u / c)
  b₀_nonneg := mul_nonneg hc.le F.b₀_nonneg
  k_nonneg := fun u hu => F.k_nonneg _ (div_pos hu hc)
  k_antitone := by
    intro x hx y hy hxy
    exact F.k_antitone (div_pos hx hc) (div_pos hy hc) (by gcongr)
  k_zero := by simp [F.k_zero]
  integrable_near_zero := by
    have h := F.lintegral_min_dilate_ne_top hc
    rw [lintegral_min_split] at h
    exact (ENNReal.add_ne_top.mp h).1
  integrable_at_top := by
    have h := F.lintegral_min_dilate_ne_top hc
    rw [lintegral_min_split] at h
    exact (ENNReal.add_ne_top.mp h).2

/-! ## The exponents of the three constructions -/

@[simp] theorem add_b₀ (F G : CausalAdmissible) : (F.add G).b₀ = F.b₀ + G.b₀ := rfl

@[simp] theorem add_k (F G : CausalAdmissible) (u : ℝ) : (F.add G).k u = F.k u + G.k u := rfl

@[simp] theorem smul_b₀ (F : CausalAdmissible) {c : ℝ} (hc : 0 ≤ c) :
    (F.smul hc).b₀ = c * F.b₀ := rfl

@[simp] theorem smul_k (F : CausalAdmissible) {c : ℝ} (hc : 0 ≤ c) (u : ℝ) :
    (F.smul hc).k u = c * F.k u := rfl

@[simp] theorem dilate_b₀ (F : CausalAdmissible) {c : ℝ} (hc : 0 < c) :
    (F.dilate hc).b₀ = c * F.b₀ := rfl

@[simp] theorem dilate_k (F : CausalAdmissible) {c : ℝ} (hc : 0 < c) (u : ℝ) :
    (F.dilate hc).k u = F.k (u / c) := rfl

/-- The exponent is additive in the data, at every nonnegative frequency. -/
theorem exponentL_add (F G : CausalAdmissible) {σ : ℝ} (hσ : 0 ≤ σ) :
    (F.add G).exponentL σ = F.exponentL σ + G.exponentL σ := by
  have hm : AEMeasurable
      (fun u : ℝ => ENNReal.ofReal ((1 - Real.exp (-(σ * u))) * F.k u / u))
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((((measurable_const.sub (measurable_expIntegrand σ)).aemeasurable).mul
      F.aemeasurable_k).div aemeasurable_id).ennreal_ofReal
  have hjump : (∫⁻ u in Ioi (0 : ℝ),
        ENNReal.ofReal ((1 - Real.exp (-(σ * u))) * (F.k u + G.k u) / u))
      = (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(σ * u))) * F.k u / u))
        + ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(σ * u))) * G.k u / u) := by
    rw [← lintegral_add_left' hm]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    rw [← ENNReal.ofReal_add (F.exponentIntegrand_nonneg hσ hu0)
      (G.exponentIntegrand_nonneg hσ hu0)]
    congr 1
    ring
  have hgauss : ENNReal.ofReal ((F.b₀ + G.b₀) * σ)
      = ENNReal.ofReal (F.b₀ * σ) + ENNReal.ofReal (G.b₀ * σ) := by
    rw [← ENNReal.ofReal_add (mul_nonneg F.b₀_nonneg hσ) (mul_nonneg G.b₀_nonneg hσ)]
    congr 1
    ring
  simp only [exponentL, add_b₀, add_k]
  rw [hgauss, hjump]
  ring

/-- The exponent is homogeneous in the data, at every frequency. -/
theorem exponentL_smul (F : CausalAdmissible) {c : ℝ} (hc : 0 ≤ c) (σ : ℝ) :
    (F.smul hc).exponentL σ = ENNReal.ofReal c * F.exponentL σ := by
  have hjump : (∫⁻ u in Ioi (0 : ℝ),
        ENNReal.ofReal ((1 - Real.exp (-(σ * u))) * (c * F.k u) / u))
      = ENNReal.ofReal c
        * ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(σ * u))) * F.k u / u) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [← ENNReal.ofReal_mul hc]
    congr 1
    ring
  have hgauss : ENNReal.ofReal (c * F.b₀ * σ)
      = ENNReal.ofReal c * ENNReal.ofReal (F.b₀ * σ) := by
    rw [← ENNReal.ofReal_mul hc]
    congr 1
    ring
  simp only [exponentL, smul_b₀, smul_k]
  rw [hgauss, hjump, mul_add]

/-- **The dilation's exponent**: `F(c\,\cdot)`, exactly. The change of variables `u = cx` leaves
`du/u` alone, which is why the dilated profile carries no Jacobian. -/
theorem exponentL_dilate (F : CausalAdmissible) {c : ℝ} (hc : 0 < c) (σ : ℝ) :
    (F.dilate hc).exponentL σ = F.exponentL (c * σ) := by
  have hjump : (∫⁻ u in Ioi (0 : ℝ),
        ENNReal.ofReal ((1 - Real.exp (-(σ * u))) * F.k (u / c) / u))
      = ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-(c * σ * u))) * F.k u / u) := by
    rw [setLIntegral_Ioi_comp_mul hc]
    have hstep : ∀ x ∈ Ioi (0 : ℝ),
        ENNReal.ofReal ((1 - Real.exp (-(σ * (c * x)))) * F.k (c * x / c) / (c * x))
          = ENNReal.ofReal c⁻¹
            * ENNReal.ofReal ((1 - Real.exp (-(c * σ * x))) * F.k x / x) := by
      intro x hx
      have hx0 : (0 : ℝ) < x := hx
      have hcancel : c * x / c = x := by field_simp
      have harg : -(σ * (c * x)) = -(c * σ * x) := by ring
      rw [hcancel, harg, ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
      congr 1
      field_simp
    rw [setLIntegral_congr_fun measurableSet_Ioi hstep,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
      ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one, one_mul]
  have hgauss : ENNReal.ofReal (c * F.b₀ * σ) = ENNReal.ofReal (F.b₀ * (c * σ)) := by
    congr 1
    ring
  simp only [exponentL, dilate_b₀, dilate_k]
  rw [hgauss, hjump]

/-- The sum read at the real-valued exponent. -/
theorem exponent_add (F G : CausalAdmissible) {σ : ℝ} (hσ : 0 ≤ σ) :
    (F.add G).exponent σ = F.exponent σ + G.exponent σ := by
  rw [exponent, exponentL_add F G hσ,
    ENNReal.toReal_add (F.exponentL_ne_top hσ) (G.exponentL_ne_top hσ)]
  rfl

/-- The nonnegative multiple read at the real-valued exponent. -/
theorem exponent_smul (F : CausalAdmissible) {c : ℝ} (hc : 0 ≤ c) (σ : ℝ) :
    (F.smul hc).exponent σ = c * F.exponent σ := by
  rw [exponent, exponentL_smul F hc σ, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]
  rfl

/-- The dilation read at the real-valued exponent. -/
theorem exponent_dilate (F : CausalAdmissible) {c : ℝ} (hc : 0 < c) (σ : ℝ) :
    (F.dilate hc).exponent σ = F.exponent (c * σ) := by
  rw [exponent, exponentL_dilate F hc σ]
  rfl

end CausalAdmissible

end ScaleSpace
