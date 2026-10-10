/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Mathlib.Analysis.Matrix.Order

/-!
# A real positive semidefinite matrix as a double sum, and as a positive definite kernel

Home: none (standard analysis in Mathlib's types: four facts about real matrices, stated in
Mathlib's types only)

Four facts about real matrices over `Fin n`, all stated in Mathlib's types only.

* `star_dotProduct_mulVec_eq_sum`: the quadratic form `x ↦ x⋆ A x` of a real matrix, written out
  as a double sum.
* `posSemidef_iff_sum`: a real matrix is positive semidefinite exactly when it is symmetric and
  its quadratic form, written as a double sum, is nonnegative.
* `sum_sum_mul`: a double sum of products is a product of sums.
* `sum_mul_conj_nonneg_of_posSemidef`: **a real symmetric positive semidefinite matrix is a
  positive definite kernel**: the complex double sum `∑_{j,k} c_j conj(c_k) A_{jk}` is a
  nonnegative real.

Moved by Q-0364 from Paper V's development repository, `Formalization/SpatialLine/
PositiveDefinite.lean` (`spatial-hemigroup-scale-space`, main at `387424ad8f9476af282b1fe9618aab2e9334bbd7`;
the file is on development main only, not at a release tag), statements and proofs verbatim up to
the namespace. Second demand: Paper V's `sum_mul_conj_exp_neg_nonneg` (Schoenberg's easy half),
and Paper VII's `complex_kernel_nonneg` (`Formalization/AffineHemigroup/LevyKhintchineNegDef.lean`),
which is the composite of the first two statements (`spatial-hemigroup-affine`,
`records/formalization/SECOND-DEMAND-candidates.md` § A6). The rest of the file (conditionally
negative definite functions and the Schoenberg route) has no second demand and stays in Paper V.
-/

namespace ScaleSpace

open Finset Matrix
open scoped ComplexOrder

section Matrices

variable {n : ℕ}

/-- The quadratic form `x ↦ x⋆ A x` of a real matrix, written out as a double sum. -/
theorem star_dotProduct_mulVec_eq_sum (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    star x ⬝ᵥ A *ᵥ x = ∑ j, ∑ k, x j * x k * A j k := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- A real matrix is positive semidefinite exactly when it is symmetric and its quadratic form,
written as a double sum, is nonnegative. -/
theorem posSemidef_iff_sum (A : Matrix (Fin n) (Fin n) ℝ) :
    A.PosSemidef ↔ (∀ j k, A k j = A j k) ∧
      ∀ x : Fin n → ℝ, 0 ≤ ∑ j, ∑ k, x j * x k * A j k := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨hherm, hpos⟩
    refine ⟨fun j k => ?_, fun x => ?_⟩
    · have := congrFun (congrFun hherm j) k
      simpa [Matrix.conjTranspose_apply] using this
    · rw [← star_dotProduct_mulVec_eq_sum]
      exact hpos x
  · rintro ⟨hsymm, hpos⟩
    refine ⟨?_, fun x => ?_⟩
    · ext j k
      simpa [Matrix.conjTranspose_apply] using hsymm j k
    · rw [star_dotProduct_mulVec_eq_sum]
      exact hpos x

/-- A double sum of products is a product of sums. -/
theorem sum_sum_mul (f g : Fin n → ℝ) : ∑ j, ∑ k, f j * g k = (∑ j, f j) * (∑ k, g k) :=
  (Finset.sum_mul_sum _ _ _ _).symm

/-- **A real symmetric positive semidefinite matrix is a positive definite kernel**: the complex
double sum `∑_{j,k} c_j conj(c_k) A_{jk}` is a nonnegative real.

Writing `c = u + iv`, the real part is `u ⬝ A u + v ⬝ A v` and the imaginary part is a sum
antisymmetric in `(j,k)` against a symmetric matrix, hence zero. -/
theorem sum_mul_conj_nonneg_of_posSemidef {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (c : Fin n → ℂ) : 0 ≤ ∑ j, ∑ k, c j * (starRingEnd ℂ) (c k) * ((A j k : ℝ) : ℂ) := by
  obtain ⟨hsymm, hpos⟩ := (posSemidef_iff_sum A).1 hA
  set u : Fin n → ℝ := fun j => (c j).re with hu
  set v : Fin n → ℝ := fun j => (c j).im with hv
  -- The imaginary part vanishes because `A` is symmetric.
  have hanti : ∑ j, ∑ k, (v j * u k - u j * v k) * A j k = 0 := by
    have hswap : ∀ j k : Fin n,
        (v k * u j - u k * v j) * A k j = -((v j * u k - u j * v k) * A j k) := by
      intro j k
      rw [hsymm j k]
      ring
    have hself : (∑ j, ∑ k, (v j * u k - u j * v k) * A j k)
        = -∑ j, ∑ k, (v j * u k - u j * v k) * A j k := by
      calc ∑ j, ∑ k, (v j * u k - u j * v k) * A j k
          = ∑ j, ∑ k, (v k * u j - u k * v j) * A k j := Finset.sum_comm
        _ = ∑ j, ∑ k, -((v j * u k - u j * v k) * A j k) :=
            Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hswap j k
        _ = -∑ j, ∑ k, (v j * u k - u j * v k) * A j k := by
            simp only [Finset.sum_neg_distrib]
    linarith
  -- The double sum is the real number `u ⬝ A u + v ⬝ A v`.
  have hterm : ∀ j k : Fin n, c j * (starRingEnd ℂ) (c k) * ((A j k : ℝ) : ℂ)
      = (((u j * u k + v j * v k) * A j k : ℝ) : ℂ)
        + Complex.I * (((v j * u k - u j * v k) * A j k : ℝ) : ℂ) := by
    intro j k
    refine Complex.ext ?_ ?_ <;>
      simp only [hu, hv, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im] <;> ring
  have hsum : ∑ j, ∑ k, c j * (starRingEnd ℂ) (c k) * ((A j k : ℝ) : ℂ)
      = (((∑ j, ∑ k, (u j * u k + v j * v k) * A j k : ℝ) : ℂ)) := by
    simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Complex.ofReal_sum, hanti]
    simp
  rw [hsum]
  refine Complex.zero_le_real.2 ?_
  have hsplit : ∑ j, ∑ k, (u j * u k + v j * v k) * A j k
      = (∑ j, ∑ k, u j * u k * A j k) + ∑ j, ∑ k, v j * v k * A j k := by
    simp only [add_mul, Finset.sum_add_distrib]
  rw [hsplit]
  exact add_nonneg (hpos u) (hpos v)

end Matrices

end ScaleSpace
