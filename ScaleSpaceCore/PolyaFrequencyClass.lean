/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Karlin's class `E₂*` and the bilateral Laplace transform

Karlin (*Total Positivity* I, 1968) characterises Pólya-frequency densities on the line through
the reciprocal of their bilateral Laplace transform `φ(s) = ∫ e^{-su} f(u) du`:

* Prop. 1.4, p. 333: the Laplace transform of a PF density exists in an open strip containing
  the imaginary axis;
* (2.2), p. 336: the class `E₂` of entire functions
  `e^{-γs² + δs} s^k ∏ (1 + a_i s) e^{-a_i s}` with `γ ≥ 0`, `δ` and `a_i` real and
  `∑ a_i² < ∞`; `E₂*` is the subclass with `ψ(0) = 1`, so `k = 0` and there is no constant;
* Thm. 3.2(a), p. 345: a density is PF if and only if `1/φ` is of class `E₂*` with
  `γ + ∑ a_i² > 0`.

This module states Karlin's two objects with his sign convention and proves the facts a
consumer needs to read an `E₂*` function as an exponent on the imaginary axis, all from Mathlib
alone:

* `bilateralLaplace`, with its bridges to `ProbabilityTheory.complexMGF`, to `charFun` on the
  imaginary axis, and to the real integral on the real axis;
* `polyaE2`, the `E₂*` function as a map `ℂ → ℂ`, whose defining product is multipliable at
  every point once `∑ a_j² < ∞` (`multipliable_polyaE2_factor`);
* `pairSeq`, the `±` pairing of a parameter sequence, and the value of `polyaE2` on the
  imaginary axis at a paired sequence (`polyaE2_pairSeq_mul_I`) — the sufficiency direction;
* the real-axis logarithmic form (`polyaE2_ofReal`), the modulus on the imaginary axis
  (`norm_polyaE2_mul_I`), and the symmetry reduction: evenness of `polyaE2` near `0` forces
  `δ = 0` and the vanishing of every odd power sum `∑ a_j^{2k+3}`
  (`polyaE2_even_imp_oddPowerSums`) — the necessity direction.

Nothing here is holomorphic. The real axis and the imaginary axis are treated separately, and
the symmetry reduction is read off a real power series, so no analytic continuation is used.
-/

namespace ScaleSpace

open Complex MeasureTheory

/-! ### The bilateral Laplace transform -/

/-- Karlin's bilateral Laplace transform of a measure on the line, with his sign:
`∫ e^{-su} dμ(u)` (*Total Positivity* I, Prop. 1.4, p. 333). Off the strip where the integrand
is integrable the value is Mathlib's junk value `0`. -/
noncomputable def bilateralLaplace (μ : Measure ℝ) (s : ℂ) : ℂ := ∫ x, cexp (-s * x) ∂μ

/-- The bilateral Laplace transform is Mathlib's complex moment generating function of the
identity, evaluated at `-s`. -/
theorem bilateralLaplace_eq_complexMGF (μ : Measure ℝ) (s : ℂ) :
    bilateralLaplace μ s = ProbabilityTheory.complexMGF id μ (-s) := rfl

/-- On the imaginary axis the bilateral Laplace transform is the characteristic function at the
reflected frequency: `L(iω) = charFun μ (-ω)`. -/
theorem bilateralLaplace_ofReal_mul_I (μ : Measure ℝ) (ω : ℝ) :
    bilateralLaplace μ (ω * I) = charFun μ (-ω) := by
  rw [bilateralLaplace_eq_complexMGF, ← ProbabilityTheory.complexMGF_id_mul_I]
  congr 1; push_cast; ring

/-- On the real axis the bilateral Laplace transform is the real integral `∫ e^{-xy} dμ(y)`. -/
theorem bilateralLaplace_ofReal (μ : Measure ℝ) (x : ℝ) :
    bilateralLaplace μ x = ((∫ y, Real.exp (-x * y) ∂μ : ℝ) : ℂ) := by
  rw [bilateralLaplace, ← integral_complex_ofReal]
  congr 1 with y
  simp [ofReal_exp]

/-- A reflection-invariant measure has an even bilateral Laplace transform. -/
theorem bilateralLaplace_neg_of_map_neg {μ : Measure ℝ} (h : μ.map (fun x => -x) = μ)
    (s : ℂ) : bilateralLaplace μ (-s) = bilateralLaplace μ s := by
  conv_rhs => rw [bilateralLaplace, ← h]
  rw [integral_map measurable_neg.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
  simp only [bilateralLaplace]
  congr 1 with x
  push_cast; ring_nf

/-! ### The class `E₂*` -/

/-- Karlin's class `E₂*` as a function `ℂ → ℂ` (*Total Positivity* I, (2.2), p. 336):
`ψ(s) = e^{-γs² + δs} ∏_j (1 + a_j s) e^{-a_j s}`. The normalisation `ψ(0) = 1` of `E₂*` is
what removes the factor `s^k` and the constant of `E₂`; a finite parameter family is padded
by zeros. The product is multipliable at every `s` once `∑ a_j² < ∞`
(`multipliable_polyaE2_factor`), so the `tprod` is not a junk value there. -/
noncomputable def polyaE2 (γ δ : ℝ) (a : ℕ → ℝ) (s : ℂ) : ℂ :=
  cexp (-(γ : ℂ) * s ^ 2 + δ * s) * ∏' j, (1 + (a j : ℂ) * s) * cexp (-((a j : ℂ) * s))

/-- The Weierstrass factor estimate: `‖(1 + w) e^{-w} - 1‖ ≤ e ‖w‖²` for `‖w‖ ≤ 1`. -/
theorem norm_one_add_mul_cexp_neg_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖(1 + w) * cexp (-w) - 1‖ ≤ Real.exp 1 * ‖w‖ ^ 2 := by
  have h1 : (1 + w) * cexp (-w) - 1 = -(cexp (-w) * (cexp w - 1 - w)) := by
    have : cexp (-w) * cexp w = 1 := by rw [← Complex.exp_add]; simp
    linear_combination this
  rw [h1, norm_neg, norm_mul]
  have h2 : ‖cexp (-w)‖ ≤ Real.exp 1 := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (by rw [norm_neg]; exact hw))
  exact mul_le_mul h2 (Complex.norm_exp_sub_one_sub_id_le hw) (norm_nonneg _)
    (Real.exp_pos 1).le

/-- The factors of `polyaE2` are summably close to `1` when `∑ a_j² < ∞`. -/
theorem summable_norm_polyaE2_factor_sub_one {a : ℕ → ℝ} (ha : Summable fun j => a j ^ 2)
    (s : ℂ) : Summable fun j => ‖(1 + (a j : ℂ) * s) * cexp (-((a j : ℂ) * s)) - 1‖ := by
  have hev : ∀ᶠ j in Filter.cofinite, a j ^ 2 * ‖s‖ ^ 2 ≤ 1 :=
    (ha.mul_right (‖s‖ ^ 2)).tendsto_cofinite_zero.eventually_le_const one_pos
  refine Summable.of_norm_bounded_eventually (ha.mul_left (Real.exp 1 * ‖s‖ ^ 2)) ?_
  filter_upwards [hev] with j hj
  have hn : ‖(a j : ℂ) * s‖ ^ 2 = a j ^ 2 * ‖s‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hle : ‖(a j : ℂ) * s‖ ≤ 1 := by
    rw [← hn] at hj
    exact (sq_le_one_iff₀ (norm_nonneg _)).mp hj
  rw [norm_norm]
  calc _ ≤ Real.exp 1 * ‖(a j : ℂ) * s‖ ^ 2 := norm_one_add_mul_cexp_neg_sub_one_le hle
    _ = _ := by rw [hn]; ring

/-- **Multipliability of the `E₂*` product.** For `∑ a_j² < ∞` the product defining `polyaE2`
converges at every complex `s` (*Total Positivity* I, (2.2), p. 336). -/
theorem multipliable_polyaE2_factor {a : ℕ → ℝ} (ha : Summable fun j => a j ^ 2) (s : ℂ) :
    Multipliable fun j => (1 + (a j : ℂ) * s) * cexp (-((a j : ℂ) * s)) := by
  simpa only [add_sub_cancel] using
    multipliable_one_add_of_summable (summable_norm_polyaE2_factor_sub_one ha s)

/-- A multipliable real product is carried to `ℂ` factor by factor. -/
theorem ofReal_tprod_of_multipliable {f : ℕ → ℝ} (hf : Multipliable f) :
    ((∏' j, f j : ℝ) : ℂ) = ∏' j, (f j : ℂ) :=
  ((hf.hasProd.map Complex.ofRealHom Complex.continuous_ofReal).tprod_eq).symm

/-! ### The `±` pairing (sufficiency) -/

/-- The `±` pairing of a parameter sequence: `pairSeq lam (2k) = lam k` and
`pairSeq lam (2k+1) = -lam k`. An `E₂*` function with these parameters and `δ = 0` is real and
even, and on the imaginary axis it is the exponential of a Pólya-frequency exponent
(`polyaE2_pairSeq_mul_I`). -/
def pairSeq (lam : ℕ → ℝ) : ℕ → ℝ := fun n => if Even n then lam (n / 2) else -lam (n / 2)

@[simp] theorem pairSeq_two_mul (lam : ℕ → ℝ) (k : ℕ) : pairSeq lam (2 * k) = lam k := by
  have h2 : 2 * k / 2 = k := by omega
  change (if Even (2 * k) then lam (2 * k / 2) else -lam (2 * k / 2)) = lam k
  rw [if_pos (even_two_mul k), h2]

@[simp] theorem pairSeq_two_mul_add_one (lam : ℕ → ℝ) (k : ℕ) :
    pairSeq lam (2 * k + 1) = -lam k := by
  have h2 : (2 * k + 1) / 2 = k := by omega
  change (if Even (2 * k + 1) then lam ((2 * k + 1) / 2) else -lam ((2 * k + 1) / 2)) = -lam k
  rw [if_neg (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one k)), h2]

/-- The squares of a paired sequence sum to twice the squares of the original. -/
theorem hasSum_pairSeq_sq {lam : ℕ → ℝ} (hl : Summable fun i => lam i ^ 2) :
    HasSum (fun n => pairSeq lam n ^ 2) (2 * ∑' i, lam i ^ 2) := by
  have he : HasSum (fun k => pairSeq lam (2 * k) ^ 2) (∑' i, lam i ^ 2) := by
    simpa using hl.hasSum
  have ho : HasSum (fun k => pairSeq lam (2 * k + 1) ^ 2) (∑' i, lam i ^ 2) := by
    simpa [neg_sq] using hl.hasSum
  rw [two_mul]
  exact HasSum.even_add_odd (f := fun n => pairSeq lam n ^ 2) he ho

/-- The paired sequence is square-summable. -/
theorem summable_pairSeq_sq {lam : ℕ → ℝ} (hl : Summable fun i => lam i ^ 2) :
    Summable fun n => pairSeq lam n ^ 2 :=
  (hasSum_pairSeq_sq hl).summable

/-- `∑ (pairSeq lam)² = 2 ∑ lam²`: the nondegeneracy `γ + ∑ a_j² > 0` of Thm. 3.2(a), p. 345,
at a paired sequence. -/
theorem tsum_pairSeq_sq {lam : ℕ → ℝ} (hl : Summable fun i => lam i ^ 2) :
    ∑' n, pairSeq lam n ^ 2 = 2 * ∑' i, lam i ^ 2 :=
  (hasSum_pairSeq_sq hl).tsum_eq

/-- **The `E₂*` function of a paired sequence on the imaginary axis.** With `δ = 0` and
parameters `pairSeq lam`, each pair of factors multiplies to `1 + lam_i² ω²`, so
`ψ(iω) = exp (γ ω² + ∑ log (1 + lam_i² ω²))` — real, positive, and the exponential of a
Pólya-frequency exponent (*Total Positivity* I, (2.2), p. 336). -/
theorem polyaE2_pairSeq_mul_I {lam : ℕ → ℝ} (hl : Summable fun i => lam i ^ 2) (γ ω : ℝ) :
    polyaE2 γ 0 (pairSeq lam) (ω * I) =
      ((Real.exp (γ * ω ^ 2 + ∑' i, Real.log (1 + lam i ^ 2 * ω ^ 2)) : ℝ) : ℂ) := by
  unfold polyaE2
  set f : ℕ → ℂ := fun n =>
    (1 + (pairSeq lam n : ℂ) * (ω * I)) * cexp (-((pairSeq lam n : ℂ) * (ω * I))) with hf
  have hl' : Summable fun i => (-lam i) ^ 2 := by simpa [neg_sq] using hl
  have he : Multipliable fun k => f (2 * k) := by
    refine (multipliable_polyaE2_factor hl ((ω : ℂ) * I)).congr fun k => ?_
    simp only [hf, pairSeq_two_mul]
  have ho : Multipliable fun k => f (2 * k + 1) := by
    refine (multipliable_polyaE2_factor hl' ((ω : ℂ) * I)).congr fun k => ?_
    simp only [hf, pairSeq_two_mul_add_one]
  have hpair : ∀ k, f (2 * k) * f (2 * k + 1) = ((1 + lam k ^ 2 * ω ^ 2 : ℝ) : ℂ) := by
    intro k
    simp only [hf, pairSeq_two_mul, pairSeq_two_mul_add_one, ofReal_neg]
    have hexp : cexp (-((lam k : ℂ) * (ω * I))) * cexp (-(-(lam k : ℂ) * (ω * I))) = 1 := by
      rw [← Complex.exp_add,
        show -((lam k : ℂ) * (ω * I)) + -(-(lam k : ℂ) * (ω * I)) = 0 by ring, Complex.exp_zero]
    rw [ofReal_add, ofReal_one, ofReal_mul, ofReal_pow, ofReal_pow]
    linear_combination (1 - (lam k : ℂ) ^ 2 * (ω : ℂ) ^ 2 * I ^ 2) * hexp
      - (lam k : ℂ) ^ 2 * (ω : ℂ) ^ 2 * I_sq
  have hreal : Multipliable fun k => (1 + lam k ^ 2 * ω ^ 2) :=
    Real.multipliable_one_add_of_summable (hl.mul_right _)
  have hsumlog : Summable fun k => Real.log (1 + lam k ^ 2 * ω ^ 2) :=
    Real.summable_log_one_add_of_summable (hl.mul_right _)
  have h1 : (∏' k, f (2 * k)) * ∏' k, f (2 * k + 1) = ∏' n, f n := tprod_even_mul_odd he ho
  have h2 : ∏' k, f (2 * k) * f (2 * k + 1) = (∏' k, f (2 * k)) * ∏' k, f (2 * k + 1) :=
    he.tprod_mul ho
  have hprod : ∏' n, f n = ((∏' k, (1 + lam k ^ 2 * ω ^ 2) : ℝ) : ℂ) := by
    rw [← h1, ← h2, tprod_congr hpair, ofReal_tprod_of_multipliable hreal]
  have hlog : Real.exp (∑' i, Real.log (1 + lam i ^ 2 * ω ^ 2)) =
      ∏' k, (1 + lam k ^ 2 * ω ^ 2) :=
    Real.rexp_tsum_eq_tprod (fun k => by positivity) hsumlog
  rw [hprod, ← hlog, Real.exp_add, ofReal_mul]
  congr 1
  rw [ofReal_exp]
  congr 1
  push_cast
  linear_combination (-(γ : ℂ) * (ω : ℂ) ^ 2) * I_sq


/-! ### The real axis, the imaginary axis, and the symmetry reduction (necessity) -/

/-- **`E₂*` on the real axis.** For real `x` with `|a_j x| ≤ 1/2` every factor is positive, the
logarithms converge, and
`ψ(x) = exp (-γx² + δx + ∑ (log (1 + a_j x) - a_j x))`
(*Total Positivity* I, (2.2), p. 336). -/
theorem polyaE2_ofReal {γ δ : ℝ} {a : ℕ → ℝ} (ha : Summable fun j => a j ^ 2) {x : ℝ}
    (hx : ∀ j, |a j * x| ≤ 1 / 2) :
    Summable (fun j => Real.log (1 + a j * x) - a j * x) ∧
    polyaE2 γ δ a x =
      ((Real.exp (-γ * x ^ 2 + δ * x + ∑' j, (Real.log (1 + a j * x) - a j * x)) : ℝ) : ℂ) := by
  set g : ℕ → ℝ := fun j => (1 + a j * x) * Real.exp (-(a j * x)) with hg
  have hpos1 : ∀ j, 0 < 1 + a j * x := fun j => by
    have := (abs_le.mp (hx j)).1; linarith
  have hgpos : ∀ j, 0 < g j := fun j => mul_pos (hpos1 j) (Real.exp_pos _)
  have hgc : ∀ j, ((g j : ℝ) : ℂ) = (1 + (a j : ℂ) * x) * cexp (-((a j : ℂ) * x)) :=
    fun j => by simp only [hg]; push_cast; try ring_nf
  have hlog : ∀ j, Real.log (g j) = Real.log (1 + a j * x) - a j * x := fun j => by
    simp only [hg]
    rw [Real.log_mul (hpos1 j).ne' (Real.exp_pos _).ne', Real.log_exp]; ring
  have hsg : Summable fun j => g j - 1 := by
    refine Summable.of_norm ?_
    refine (summable_norm_polyaE2_factor_sub_one ha (x : ℂ)).congr fun j => ?_
    rw [← hgc j, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real]
  have hsumlog_g : Summable fun j => Real.log (g j) := by
    simpa using Real.summable_log_one_add_of_summable hsg
  have hsum : Summable (fun j => Real.log (1 + a j * x) - a j * x) := hsumlog_g.congr hlog
  refine ⟨hsum, ?_⟩
  have hmult : Multipliable g := Real.multipliable_of_summable_log hgpos hsumlog_g
  have htp : ∏' j, g j = Real.exp (∑' j, (Real.log (1 + a j * x) - a j * x)) := by
    rw [← Real.rexp_tsum_eq_tprod hgpos hsumlog_g, tsum_congr hlog]
  unfold polyaE2
  rw [tprod_congr fun j => (hgc j).symm, ← ofReal_tprod_of_multipliable hmult, htp,
    Real.exp_add, ofReal_mul]
  congr 1
  rw [ofReal_exp]
  congr 1
  push_cast; ring

/-- **The modulus of `E₂*` on the imaginary axis.**
`‖ψ(iω)‖ = exp (γω² + ½ ∑ log (1 + a_j² ω²))`, for every `δ`. The modulus does not see the signs
of the parameters; which exponents are Pólya-frequency exponents is decided by the symmetry
reduction `polyaE2_even_imp_oddPowerSums`. -/
theorem norm_polyaE2_mul_I {γ δ : ℝ} {a : ℕ → ℝ} (ha : Summable fun j => a j ^ 2) (ω : ℝ) :
    ‖polyaE2 γ δ a (ω * I)‖ =
      Real.exp (γ * ω ^ 2 + (1 / 2) * ∑' j, Real.log (1 + a j ^ 2 * ω ^ 2)) := by
  have hnorm : ∀ j, ‖(1 + (a j : ℂ) * (ω * I)) * cexp (-((a j : ℂ) * (ω * I)))‖ =
      √(1 + a j ^ 2 * ω ^ 2) := by
    intro j
    rw [norm_mul, Complex.norm_exp]
    have h1 : (1 + (a j : ℂ) * (ω * I)) = ((1 : ℝ) : ℂ) + ((a j * ω : ℝ) : ℂ) * I := by
      push_cast; ring
    have h2 : (-((a j : ℂ) * (ω * I))).re = 0 := by simp
    rw [h1, Complex.norm_add_mul_I, h2, Real.exp_zero, mul_one]
    congr 1; ring
  have hlogsum : Summable fun j => Real.log (1 + a j ^ 2 * ω ^ 2) :=
    Real.summable_log_one_add_of_summable (ha.mul_right _)
  have hsqrt_pos : ∀ j, 0 < √(1 + a j ^ 2 * ω ^ 2) := fun j =>
    Real.sqrt_pos.mpr (by positivity)
  have hlog_sqrt : ∀ j, Real.log √(1 + a j ^ 2 * ω ^ 2) =
      (1 / 2) * Real.log (1 + a j ^ 2 * ω ^ 2) := fun j => by
    rw [Real.log_sqrt (by positivity)]; ring
  have hs2 : Summable fun j => Real.log √(1 + a j ^ 2 * ω ^ 2) :=
    (hlogsum.mul_left (1 / 2)).congr fun j => (hlog_sqrt j).symm
  have hre : (-(γ : ℂ) * ((ω : ℂ) * I) ^ 2 + (δ : ℂ) * ((ω : ℂ) * I)) =
      ((γ * ω ^ 2 : ℝ) : ℂ) + ((δ * ω : ℝ) : ℂ) * I := by
    push_cast
    linear_combination (-(γ : ℂ) * (ω : ℂ) ^ 2) * I_sq
  unfold polyaE2
  rw [norm_mul, Multipliable.norm_tprod (multipliable_polyaE2_factor ha ((ω : ℂ) * I)),
    tprod_congr hnorm, ← Real.rexp_tsum_eq_tprod hsqrt_pos hs2, tsum_congr hlog_sqrt,
    tsum_mul_left, Complex.norm_exp, ← Real.exp_add, hre]
  congr 2
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  ring

/-- **Coefficient extraction.** A real power series that sums to `0` at every point of an open
interval around `0` has every coefficient `0`. -/
theorem eq_zero_of_hasSum_mul_pow_eq_zero {b : ℕ → ℝ} {r : ℝ} (hr : 0 < r)
    (h : ∀ x ∈ Set.Ioo (-r) r, HasSum (fun n => b n * x ^ n) 0) (n : ℕ) : b n = 0 := by
  set ρ : NNReal := ⟨r / 2, by positivity⟩ with hρdef
  have hρ : (ρ : ℝ) = r / 2 := rfl
  set p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ b with hp
  have hsum : Summable fun n => ‖p n‖ * (ρ : ℝ) ^ n := by
    have h0 := (h (r / 2) ⟨by linarith, by linarith⟩).summable
    have h1 : Summable fun n => ‖b n * (r / 2) ^ n‖ := h0.norm
    refine h1.congr fun n => ?_
    rw [norm_mul, norm_pow, hp, FormalMultilinearSeries.ofScalars_norm, hρ,
      Real.norm_of_nonneg (half_pos hr).le]
  have hpos : 0 < p.radius :=
    lt_of_lt_of_le (ENNReal.coe_pos.mpr (NNReal.coe_pos.mp (by rw [hρ]; exact half_pos hr)))
      (p.le_radius_of_summable hsum)
  have hfp := (p.hasFPowerSeriesOnBall hpos).hasFPowerSeriesAt
  have hev : p.sum =ᶠ[nhds 0] 0 := by
    have hmem : Set.Ioo (-r) r ∈ nhds (0 : ℝ) := Ioo_mem_nhds (by linarith) hr
    filter_upwards [hmem] with y hy
    simp only [Pi.zero_apply, FormalMultilinearSeries.sum, hp,
      FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
    exact (h y hy).tsum_eq
  have hp0 : p = 0 := hfp.eq_zero_of_eventually hev
  rw [hp, FormalMultilinearSeries.ofScalars_series_eq_zero] at hp0
  exact congrFun hp0 n

/-- **The symmetry reduction, on the logarithm.** If
`2δx + ∑ (log (1 + a_j x) - log (1 - a_j x) - 2 a_j x)` vanishes for every `x ∈ (-r, r)`, and
`|a_j x| ≤ 1/2` there, then `δ = 0` and every odd power sum `∑ a_j^{2k+3}` vanishes.

The artanh series expands each term as `∑_k 2 (a_j x)^{2k+3} / (2k+3)`; the double series is
dominated by `2x² a_j² 2^{-k}`, so it can be summed in the other order, into a power series in
`x` with coefficients `2δ` and `2 ∑_j a_j^{2k+3} / (2k+3)`; and a power series vanishing on an
interval has no nonzero coefficient (`eq_zero_of_hasSum_mul_pow_eq_zero`). -/
theorem oddPowerSums_eq_zero {δ : ℝ} {a : ℕ → ℝ} (ha : Summable fun j => a j ^ 2)
    {r : ℝ} (hr : 0 < r) (hra : ∀ j, ∀ x ∈ Set.Ioo (-r) r, |a j * x| ≤ 1 / 2)
    (h : ∀ x ∈ Set.Ioo (-r) r,
      2 * δ * x + ∑' j, (Real.log (1 + a j * x) - Real.log (1 - a j * x) - 2 * (a j * x)) = 0) :
    δ = 0 ∧ ∀ k : ℕ, ∑' j, a j ^ (2 * k + 3) = 0 := by
  -- The odd coefficients `e k` of the power series, and the full coefficient sequence `b`.
  set e : ℕ → ℝ := fun k => if k = 0 then 2 * δ else
    2 * (1 / (2 * (k : ℝ) + 1)) * ∑' j, a j ^ (2 * k + 1) with he
  have he0 : e 0 = 2 * δ := by simp [he]
  set b : ℕ → ℝ := fun n => if Even n then 0 else e (n / 2) with hb
  have hb_even : ∀ k, b (2 * k) = 0 := fun k => by
    change (if Even (2 * k) then 0 else e (2 * k / 2)) = 0
    rw [if_pos (even_two_mul k)]
  have hb_odd : ∀ k, b (2 * k + 1) = e k := fun k => by
    have h2 : (2 * k + 1) / 2 = k := by omega
    change (if Even (2 * k + 1) then 0 else e ((2 * k + 1) / 2)) = e k
    rw [if_neg (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one k)), h2]
  have hser : ∀ x ∈ Set.Ioo (-r) r, HasSum (fun n => b n * x ^ n) 0 := by
    intro x hx
    set T : ℕ × ℕ → ℝ := fun q =>
      2 * (1 / (2 * ((q.2 + 1 : ℕ) : ℝ) + 1)) * (a q.1 * x) ^ (2 * (q.2 + 1) + 1) with hT
    -- Rows: the artanh series of each term, less its linear term.
    have hrow : ∀ j, HasSum (fun k => T (j, k))
        (Real.log (1 + a j * x) - Real.log (1 - a j * x) - 2 * (a j * x)) := by
      intro j
      have hy : |a j * x| < 1 := lt_of_le_of_lt (hra j x hx) (by norm_num)
      have h1 := (hasSum_nat_add_iff' 1).mpr (Real.hasSum_log_sub_log_of_abs_lt_one hy)
      have h2 : Real.log (1 + a j * x) - Real.log (1 - a j * x) - ∑ i ∈ Finset.range 1,
          (2 : ℝ) * (1 / (2 * (i : ℝ) + 1)) * (a j * x) ^ (2 * i + 1) =
          Real.log (1 + a j * x) - Real.log (1 - a j * x) - 2 * (a j * x) := by
        simp
      rw [h2] at h1; exact h1
    -- The double series is absolutely summable.
    have hbound : ∀ q : ℕ × ℕ, ‖T q‖ ≤ (2 * x ^ 2 * a q.1 ^ 2) * (1 / 2 : ℝ) ^ q.2 := by
      intro q
      have hy := hra q.1 x hx
      have hy0 : 0 ≤ |a q.1 * x| := abs_nonneg _
      have hc1 : 0 ≤ 1 / (2 * ((q.2 + 1 : ℕ) : ℝ) + 1) := by positivity
      have hc2 : 1 / (2 * ((q.2 + 1 : ℕ) : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; push_cast
        linarith [(Nat.cast_nonneg q.2 : (0 : ℝ) ≤ q.2)]
      have hpow : |a q.1 * x| ^ (2 * (q.2 + 1) + 1) ≤ (a q.1 * x) ^ 2 * (1 / 2) ^ q.2 := by
        have e1 : |a q.1 * x| ^ (2 * (q.2 + 1) + 1) =
            |a q.1 * x| ^ 2 * |a q.1 * x| ^ (2 * q.2 + 1) := by ring
        rw [e1, sq_abs]
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        calc |a q.1 * x| ^ (2 * q.2 + 1)
            ≤ (1 / 2) ^ (2 * q.2 + 1) := pow_le_pow_left₀ hy0 hy _
          _ ≤ (1 / 2) ^ q.2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      calc ‖T q‖ = 2 * (1 / (2 * ((q.2 + 1 : ℕ) : ℝ) + 1)) *
            |a q.1 * x| ^ (2 * (q.2 + 1) + 1) := by
            simp only [hT, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hc1, abs_two]
        _ ≤ (2 * 1) * ((a q.1 * x) ^ 2 * (1 / 2) ^ q.2) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hc2 (by norm_num)) hpow (by positivity)
              (by norm_num)
        _ = _ := by ring
    have hsumT : Summable T := by
      refine Summable.of_norm_bounded ?_ hbound
      exact (ha.mul_left (2 * x ^ 2)).mul_of_nonneg summable_geometric_two
        (fun j => mul_nonneg (by positivity) (sq_nonneg _)) (fun k => pow_nonneg (by norm_num) k)
    -- Columns: the `k`-th column sums to the coefficient of `x^{2k+3}`.
    have hcol : ∀ k, HasSum (fun j => T (j, k)) (e (k + 1) * x ^ (2 * (k + 1) + 1)) := by
      intro k
      have hs : Summable fun j => T (j, k) := hsumT.comp_injective (Prod.mk_left_injective k)
      have hterm : ∀ j, T (j, k) = (2 * (1 / (2 * ((k + 1 : ℕ) : ℝ) + 1)) *
          x ^ (2 * (k + 1) + 1)) * a j ^ (2 * (k + 1) + 1) := fun j => by
        simp only [hT]; ring
      have hval : ∑' j, T (j, k) = e (k + 1) * x ^ (2 * (k + 1) + 1) := by
        rw [tsum_congr hterm, tsum_mul_left]
        simp only [he]
        rw [if_neg (Nat.succ_ne_zero k)]
        ring
      rw [← hval]; exact hs.hasSum
    have hrows : HasSum (fun j => Real.log (1 + a j * x) - Real.log (1 - a j * x) -
        2 * (a j * x)) (∑' q, T q) := hsumT.hasSum.prod_fiberwise hrow
    have htswap : ∑' q : ℕ × ℕ, T q.swap = ∑' q, T q := (Equiv.prodComm ℕ ℕ).tsum_eq T
    have hcols : HasSum (fun k => e (k + 1) * x ^ (2 * (k + 1) + 1)) (∑' q, T q) := by
      rw [← htswap]
      exact hsumT.prod_symm.hasSum.prod_fiberwise fun k => hcol k
    have hS : ∑' q, T q = -(2 * δ * x) := by
      have := h x hx; rw [hrows.tsum_eq] at this; linarith
    have hodd : HasSum (fun k => b (2 * k + 1) * x ^ (2 * k + 1)) 0 := by
      have h0 : (0 : ℝ) - ∑ i ∈ Finset.range 1, e i * x ^ (2 * i + 1) = ∑' q, T q := by
        rw [hS, Finset.sum_range_one, he0]; ring
      have hshift : HasSum (fun n => e (n + 1) * x ^ (2 * (n + 1) + 1))
          ((0 : ℝ) - ∑ i ∈ Finset.range 1, e i * x ^ (2 * i + 1)) := by
        rw [h0]; exact hcols
      have := (hasSum_nat_add_iff' (f := fun k => e k * x ^ (2 * k + 1)) 1).mp hshift
      simpa only [hb_odd] using this
    have heven : HasSum (fun k => b (2 * k) * x ^ (2 * k)) 0 := by
      simpa only [hb_even, zero_mul] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
    simpa only [add_zero] using HasSum.even_add_odd (f := fun n => b n * x ^ n) heven hodd
  have hb0 := eq_zero_of_hasSum_mul_pow_eq_zero hr hser
  have hez : ∀ k, e k = 0 := fun k => by rw [← hb_odd]; exact hb0 _
  refine ⟨?_, fun k => ?_⟩
  · have := hez 0
    rw [he0] at this
    linarith
  · have h1 := hez (k + 1)
    simp only [he] at h1
    rw [if_neg (Nat.succ_ne_zero k)] at h1
    have hne : (2 : ℝ) * (1 / (2 * ((k + 1 : ℕ) : ℝ) + 1)) ≠ 0 := by positivity
    have h2 := (mul_eq_zero.mp h1).resolve_left hne
    have h3 : 2 * (k + 1) + 1 = 2 * k + 3 := by ring
    rwa [h3] at h2

/-- **Evenness of an `E₂*` function forces symmetric parameters.** If `ψ(x) = ψ(-x)` for every
real `x` in some interval `(-r, r)`, then `δ = 0` and every odd power sum `∑ a_j^{2k+3}`
vanishes.

This is the step Karlin's Thm. 3.2(a), p. 345, leaves to a consumer with a symmetric density:
the Laplace transform of a symmetric PF density is even on the real part `(-r, r)` of the strip
of Prop. 1.4, p. 333, and so is its reciprocal `ψ`. The interval is shrunk until
`|a_j x| ≤ 1/2`, the real-axis form `polyaE2_ofReal` turns evenness into the hypothesis of
`oddPowerSums_eq_zero`, and that theorem concludes. With vanishing odd power sums, the halving
identity for even quadratically bounded functions reads the modulus `norm_polyaE2_mul_I` as a
Pólya-frequency exponent in the positive parts of the parameters. -/
theorem polyaE2_even_imp_oddPowerSums {γ δ : ℝ} {a : ℕ → ℝ} (ha : Summable fun j => a j ^ 2)
    {r : ℝ} (hr : 0 < r)
    (heven : ∀ x ∈ Set.Ioo (-r) r, polyaE2 γ δ a x = polyaE2 γ δ a (-x)) :
    δ = 0 ∧ ∀ k : ℕ, ∑' j, a j ^ (2 * k + 3) = 0 := by
  obtain ⟨M, hMpos, hA⟩ : ∃ M : ℝ, 0 < M ∧ ∀ j, |a j| ≤ M := by
    refine ⟨1 + ∑' j, a j ^ 2, ?_, fun j => ?_⟩
    · have := (tsum_nonneg fun j => sq_nonneg (a j) : (0 : ℝ) ≤ ∑' j, a j ^ 2); linarith
    · nlinarith [abs_nonneg (a j), sq_abs (a j), sq_nonneg (|a j| - 1),
        ha.le_tsum j (fun i _ => sq_nonneg (a i))]
  obtain ⟨r', hr'pos, hr'r, hr'M⟩ : ∃ r', 0 < r' ∧ r' ≤ r ∧ r' ≤ 1 / (2 * M) :=
    ⟨min r (1 / (2 * M)), lt_min hr (by positivity), min_le_left _ _, min_le_right _ _⟩
  have hbd : ∀ j, ∀ x ∈ Set.Ioo (-r') r', |a j * x| ≤ 1 / 2 := by
    intro j x hx
    have hx' : |x| ≤ 1 / (2 * M) := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [abs_mul]
    have hM0 : M ≠ 0 := hMpos.ne'
    calc |a j| * |x| ≤ M * (1 / (2 * M)) := mul_le_mul (hA j) hx' (abs_nonneg _) hMpos.le
      _ = 1 / 2 := by field_simp
  refine oddPowerSums_eq_zero ha hr'pos hbd fun x hx => ?_
  have hbd' : ∀ j, |a j * (-x)| ≤ 1 / 2 := fun j => by
    rw [mul_neg, abs_neg]; exact hbd j x hx
  obtain ⟨hs1, hp1⟩ := polyaE2_ofReal (γ := γ) (δ := δ) ha (fun j => hbd j x hx)
  obtain ⟨hs2, hp2⟩ := polyaE2_ofReal (γ := γ) (δ := δ) ha hbd'
  have hxr : x ∈ Set.Ioo (-r) r := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hev := heven x hxr
  rw [hp1, ← Complex.ofReal_neg, hp2, Complex.ofReal_inj] at hev
  have hev2 := Real.exp_injective hev
  have hS : ∑' j, (Real.log (1 + a j * x) - Real.log (1 - a j * x) - 2 * (a j * x)) =
      (∑' j, (Real.log (1 + a j * x) - a j * x)) -
        ∑' j, (Real.log (1 + a j * -x) - a j * -x) := by
    rw [← hs1.tsum_sub hs2]
    exact tsum_congr fun j => by rw [mul_neg, ← sub_eq_add_neg]; ring
  rw [hS]
  linear_combination hev2

end ScaleSpace
