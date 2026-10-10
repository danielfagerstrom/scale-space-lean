/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Vanishing odd power sums and the symmetry of a square-summable sequence

Home: line/selection:prop:polya-frequency

A real sequence `a` with `∑ a_j² < ∞` whose odd power sums `∑ a_j^{2k+3}` all vanish is
symmetric in distribution: the atomic measure `ν = ∑ a_j² δ_{a_j}` is invariant under
`y ↦ -y`. Consequently every even function `g` with `g 0 = 0` and `|g y| ≤ C y²` satisfies
`∑ g (a_j) = 2 ∑ g (a_j⁺)`.

The route is the characteristic function. The odd power sums are the Taylor coefficients of
`t ↦ ∑ a_j² sin (t a_j)`, so that function vanishes identically; hence `ν` and its reflection
have the same characteristic function and coincide (`Measure.ext_of_charFun`). No moment
problem and no analytic continuation is needed.

This is the symmetry reduction a Pólya-frequency exponent needs: the modulus of Karlin's
`E₂*` factor on the imaginary axis reads `½ ∑ log (1 + a_j² ω²)`, and the halving identity,
applied with `g y = log (1 + y² ω²)`, rewrites it as `∑ log (1 + (a_j⁺)² ω²)`.
-/

namespace ScaleSpace

open MeasureTheory Complex

/-- The atomic measure `∑ a_j² δ_{a_j}` of a real sequence: the mass `a_j²` at each point
`a_j`. Finite exactly when `∑ a_j² < ∞` (`isFiniteMeasure_squareWeightedAtoms`). -/
noncomputable def squareWeightedAtoms (a : ℕ → ℝ) : Measure ℝ :=
  Measure.sum fun j => ENNReal.ofReal (a j ^ 2) • Measure.dirac (a j)

theorem isFiniteMeasure_squareWeightedAtoms {a : ℕ → ℝ} (ha : Summable fun j => a j ^ 2) :
    IsFiniteMeasure (squareWeightedAtoms a) := by
  constructor
  simp only [squareWeightedAtoms, Measure.sum_apply_of_countable, Measure.smul_apply,
    Measure.dirac_apply, Set.indicator_univ, Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) ha]
  exact ENNReal.ofReal_lt_top

/-- The integral against `∑ a_j² δ_{a_j}` is the weighted sum, with no integrability
hypothesis (both sides take the junk value together). -/
theorem integral_squareWeightedAtoms {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (a : ℕ → ℝ) (f : ℝ → E) :
    ∫ y, f y ∂squareWeightedAtoms a = ∑' j, a j ^ 2 • f (a j) := by
  rw [squareWeightedAtoms, integral_sum_dirac (fun j => ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)]

/-- Vanishing odd power sums make `t ↦ ∑ a_j² sin (t a_j)` vanish identically: its Taylor
coefficients are the power sums `∑ a_j^{2k+3}`, and the double series converges absolutely. -/
theorem tsum_sq_mul_sin_eq_zero {a : ℕ → ℝ} (ha : Summable fun j => a j ^ 2)
    (hodd : ∀ k : ℕ, ∑' j, a j ^ (2 * k + 3) = 0) (t : ℝ) :
    ∑' j, a j ^ 2 * Real.sin (t * a j) = 0 := by
  set A := 1 + ∑' j, a j ^ 2
  have hA : ∀ j, |a j| ≤ A := fun j => by
    have h1 : a j ^ 2 ≤ ∑' j, a j ^ 2 := ha.le_tsum j (fun i _ => sq_nonneg _)
    nlinarith [abs_nonneg (a j), sq_abs (a j)]
  set f : ℕ × ℕ → ℝ := fun p =>
    a p.1 ^ 2 * ((-1) ^ p.2 * (t * a p.1) ^ (2 * p.2 + 1) / ((2 * p.2 + 1).factorial))
  have hf : Summable f := by
    refine Summable.of_norm_bounded
      (ha.mul_of_nonneg (Real.hasSum_sinh (|t| * A)).summable (fun j => sq_nonneg _)
        (fun k => by positivity)) fun p => ?_
    simp only [f, norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Real.norm_eq_abs, sq_abs, Nat.abs_cast]
    gcongr
    exact hA _
  calc ∑' j, a j ^ 2 * Real.sin (t * a j)
      = ∑' j, ∑' k, f (j, k) := by
        congr 1; ext j; exact ((Real.hasSum_sin _).mul_left (a j ^ 2)).tsum_eq.symm
    _ = ∑' k, ∑' j, f (j, k) :=
        (hf.tsum_comm' (fun j => hf.comp_injective (Prod.mk_right_injective j))
          (fun k => hf.comp_injective (Prod.mk_left_injective k))).symm
    _ = ∑' k, ((-1) ^ k * t ^ (2 * k + 1) / ((2 * k + 1).factorial)) *
          ∑' j, a j ^ (2 * k + 3) := by
        congr 1; ext k; rw [← tsum_mul_left]; congr 1; ext j; simp only [f]; ring
    _ = 0 := by simp [hodd]

/-- **Symmetry of the atomic measure.** Vanishing odd power sums make `∑ a_j² δ_{a_j}` equal
to its reflection `∑ a_j² δ_{-a_j}`. -/
theorem squareWeightedAtoms_neg {a : ℕ → ℝ} (ha : Summable fun j => a j ^ 2)
    (hodd : ∀ k : ℕ, ∑' j, a j ^ (2 * k + 3) = 0) :
    squareWeightedAtoms (fun j => -a j) = squareWeightedAtoms a := by
  have ha' : Summable fun j => (-a j) ^ 2 := by simpa using ha
  haveI := isFiniteMeasure_squareWeightedAtoms ha
  haveI := isFiniteMeasure_squareWeightedAtoms ha'
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have hs : ∀ b : ℕ → ℝ, Summable (fun j => b j ^ 2) →
      Summable fun j => b j ^ 2 • cexp (t * b j * I) := fun b hb =>
    Summable.of_norm_bounded hb fun j => by
      rw [norm_smul, ← ofReal_mul, norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg _)]
  have key : ∀ j, (-a j) ^ 2 • cexp (t * ↑(-a j) * I) =
      a j ^ 2 • cexp (t * a j * I) - (2 * I) * ↑(a j ^ 2 * Real.sin (t * a j)) := fun j => by
    have e : (t : ℂ) * ↑(-a j) * I = ↑(-(t * a j)) * I := by push_cast; ring
    have e' : (t : ℂ) * ↑(a j) * I = ↑(t * a j) * I := by push_cast; ring
    rw [e, e', exp_mul_I, exp_mul_I, ← ofReal_cos, ← ofReal_sin, ← ofReal_cos, ← ofReal_sin,
      Real.cos_neg, Real.sin_neg, real_smul, real_smul]
    push_cast; ring
  have hsin : Summable fun j => (2 * I) * ((a j ^ 2 * Real.sin (t * a j) : ℝ) : ℂ) :=
    (summable_ofReal.mpr (Summable.of_norm_bounded ha fun j => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_of_le_one_right (sq_nonneg _) (Real.abs_sin_le_one _))).mul_left _
  simp only [charFun_apply_real, integral_squareWeightedAtoms]
  rw [tsum_congr key, (hs a ha).tsum_sub hsin, tsum_mul_left, ← ofReal_tsum,
    tsum_sq_mul_sin_eq_zero ha hodd, ofReal_zero, mul_zero, sub_zero]

/-- **Symmetry of the atomic measure**, as invariance under the reflection `y ↦ -y`. -/
theorem squareWeightedAtoms_map_neg {a : ℕ → ℝ} (ha : Summable fun j => a j ^ 2)
    (hodd : ∀ k : ℕ, ∑' j, a j ^ (2 * k + 3) = 0) :
    (squareWeightedAtoms a).map (fun y => -y) = squareWeightedAtoms a := by
  conv_rhs => rw [← squareWeightedAtoms_neg ha hodd]
  simp only [squareWeightedAtoms, Measure.map_sum measurable_neg.aemeasurable,
    Measure.map_smul, Measure.map_dirac' measurable_neg, neg_sq]

/-- A quadratically bounded `g` is summable along a square-summable sequence. -/
theorem summable_comp_of_abs_le_sq {a : ℕ → ℝ} (ha : Summable fun j => a j ^ 2)
    {g : ℝ → ℝ} {C : ℝ} (hgC : ∀ y, |g y| ≤ C * y ^ 2) : Summable fun j => g (a j) :=
  Summable.of_norm_bounded (ha.mul_left C) fun j => hgC (a j)

/-- A quadratically bounded `g` is summable along the positive part of a square-summable
sequence. -/
theorem summable_comp_max_of_abs_le_sq {a : ℕ → ℝ} (ha : Summable fun j => a j ^ 2)
    {g : ℝ → ℝ} {C : ℝ} (hgC : ∀ y, |g y| ≤ C * y ^ 2) :
    Summable fun j => g (max (a j) 0) := by
  refine summable_comp_of_abs_le_sq (a := fun j => max (a j) 0) ?_ hgC
  refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_) ha
  rcases le_total (a j) 0 with h | h
  · simp [max_eq_right h, sq_nonneg]
  · simp [max_eq_left h]

/-- **The halving identity.** If the odd power sums `∑ a_j^{2k+3}` of a square-summable real
sequence all vanish, then every even, quadratically bounded `g` with `g 0 = 0` satisfies
`∑ g (a_j) = 2 ∑ g (a_j⁺)`: the negative terms contribute exactly what the positive ones do.

No measurability of `g` is asked: the integral against a countable sum of Dirac masses is a
weighted sum for every `g`. -/
theorem tsum_eq_two_mul_tsum_posPart {a : ℕ → ℝ} (ha : Summable fun j => a j ^ 2)
    (hodd : ∀ k : ℕ, ∑' j, a j ^ (2 * k + 3) = 0) {g : ℝ → ℝ}
    (hge : ∀ y, g (-y) = g y) (hg0 : g 0 = 0) {C : ℝ} (hgC : ∀ y, |g y| ≤ C * y ^ 2) :
    ∑' j, g (a j) = 2 * ∑' j, g (max (a j) 0) := by
  -- `h y = g y / y²` on the positive axis, `0` elsewhere, so `y² h y = g (max y 0)`.
  set h : ℝ → ℝ := fun y => if 0 < y then g y / y ^ 2 else 0
  have hh : ∀ y, y ^ 2 * h y = g (max y 0) := fun y => by
    by_cases hy : 0 < y
    · simp [h, hy, max_eq_left hy.le, mul_div_cancel₀ _ (pow_ne_zero 2 hy.ne')]
    · simp [h, hy, max_eq_right (not_lt.mp hy), hg0]
  have hneg : ∑' j, g (max (-a j) 0) = ∑' j, g (max (a j) 0) := by
    have := congrArg (fun μ => ∫ y, h y ∂μ) (squareWeightedAtoms_neg ha hodd)
    simpa only [integral_squareWeightedAtoms, smul_eq_mul, hh] using this
  have hsplit : ∀ y, g y = g (max y 0) + g (max (-y) 0) := fun y => by
    rcases le_total y 0 with hy | hy
    · rw [max_eq_right hy, max_eq_left (neg_nonneg.mpr hy), hge, hg0, zero_add]
    · rw [max_eq_left hy, max_eq_right (neg_nonpos.mpr hy), hg0, add_zero]
  have hsn : Summable fun j => (-a j) ^ 2 := by simpa using ha
  rw [tsum_congr fun j => hsplit (a j),
    (summable_comp_max_of_abs_le_sq ha hgC).tsum_add (summable_comp_max_of_abs_le_sq hsn hgC),
    hneg, two_mul]

end ScaleSpace
