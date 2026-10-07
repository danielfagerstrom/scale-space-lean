/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import ScaleSpaceCore.L1OperatorsSpace
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The matrix dilation on `L¹(ℝ^d)`

Q-0332 (SSL-5). `ScaleSpaceCore.L1OperatorsSpace` indexes the dilation by `A : E ≃L[ℝ] E`; Paper VII
writes its operators with matrices, `A : Matrix (Fin d) (Fin d) ℝ` acting on
`EuclideanSpace ℝ (Fin d)` through `Matrix.toEuclideanCLM`, with the representative
`|det A|⁻¹ f(A⁻¹ x)` read with the matrix inverse and the matrix determinant. This file is that
reading: `matEquiv A` is the equivalence of an invertible matrix, its inverse is
`toEuclideanCLM A⁻¹` and its determinant is `A.det`, so `D_A`'s representative and the relational
intertwining of `intertwines_iff_dilL1E` are stated on the nose in Paper VII's terms.
-/

namespace ScaleSpace

open MeasureTheory Matrix

variable {d : ℕ}

/-- The continuous linear equivalence of `ℝ^d` given by an invertible matrix, acting through
`Matrix.toEuclideanCLM`. -/
noncomputable def matEquiv (A : Matrix (Fin d) (Fin d) ℝ) (hA : IsUnit A.det) :
    EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
  ContinuousLinearEquiv.equivOfInverse (toEuclideanCLM (𝕜 := ℝ) A)
    (toEuclideanCLM (𝕜 := ℝ) A⁻¹)
    (fun x => by
      change (toEuclideanCLM (𝕜 := ℝ) A⁻¹ * toEuclideanCLM (𝕜 := ℝ) A) x = x
      rw [← map_mul, nonsing_inv_mul A hA, map_one]
      rfl)
    (fun x => by
      change (toEuclideanCLM (𝕜 := ℝ) A * toEuclideanCLM (𝕜 := ℝ) A⁻¹) x = x
      rw [← map_mul, mul_nonsing_inv A hA, map_one]
      rfl)

@[simp] lemma matEquiv_apply (A : Matrix (Fin d) (Fin d) ℝ) (hA : IsUnit A.det)
    (x : EuclideanSpace ℝ (Fin d)) : matEquiv A hA x = toEuclideanCLM (𝕜 := ℝ) A x := rfl

@[simp] lemma matEquiv_symm_apply (A : Matrix (Fin d) (Fin d) ℝ) (hA : IsUnit A.det)
    (x : EuclideanSpace ℝ (Fin d)) :
    (matEquiv A hA).symm x = toEuclideanCLM (𝕜 := ℝ) A⁻¹ x := rfl

/-- The determinant of `matEquiv A` is the matrix determinant. -/
lemma det_matEquiv (A : Matrix (Fin d) (Fin d) ℝ) (hA : IsUnit A.det) :
    LinearMap.det ((matEquiv A hA : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d)) :
      EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) = A.det := by
  change LinearMap.det (Matrix.toLin (PiLp.basisFun _ _ _) (PiLp.basisFun _ _ _) A) = A.det
  exact LinearMap.det_toLin _ A

/-- `matEquiv (A B) = matEquiv A ∘ matEquiv B`. -/
lemma matEquiv_mul (A B : Matrix (Fin d) (Fin d) ℝ) (hA : IsUnit A.det) (hB : IsUnit B.det) :
    matEquiv (A * B) (by rw [det_mul]; exact hA.mul hB)
      = (matEquiv B hB).trans (matEquiv A hA) := by
  refine ContinuousLinearEquiv.ext (funext fun x => ?_)
  change toEuclideanCLM (𝕜 := ℝ) (A * B) x
    = toEuclideanCLM (𝕜 := ℝ) A (toEuclideanCLM (𝕜 := ℝ) B x)
  rw [map_mul]
  rfl

/-- **The matrix dilation** `D_A f = |det A|⁻¹ f(A⁻¹ ·)`, with the matrix inverse and determinant.
-/
theorem coeFn_dilL1E_matEquiv (A : Matrix (Fin d) (Fin d) ℝ) (hA : IsUnit A.det)
    (f : EuclideanSpace ℝ (Fin d) →₁[volume] ℝ) :
    dilL1E (matEquiv A hA) f =ᵐ[volume]
      fun x => |A.det|⁻¹ *
        (f : EuclideanSpace ℝ (Fin d) → ℝ) (toEuclideanCLM (𝕜 := ℝ) A⁻¹ x) := by
  filter_upwards [coeFn_dilL1E (matEquiv A hA) f] with x hx
  rw [hx, dilateE_apply, det_matEquiv]
  rfl

/-- **The relational form of the matrix dilation.** -/
theorem eq_dilL1E_matEquiv_iff (A : Matrix (Fin d) (Fin d) ℝ) (hA : IsUnit A.det)
    (f g : EuclideanSpace ℝ (Fin d) →₁[volume] ℝ) :
    g = dilL1E (matEquiv A hA) f ↔ (g : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[volume]
      fun x => |A.det|⁻¹ *
        (f : EuclideanSpace ℝ (Fin d) → ℝ) (toEuclideanCLM (𝕜 := ℝ) A⁻¹ x) := by
  rw [eq_dilL1E_iff, det_matEquiv]
  rfl

/-- **Paper VII's relational intertwining is the operator identity**: for `c ≠ 0`,
"`g = c · f(A⁻¹ ·)` a.e. implies `Ψ g = c · (Φ f)(A⁻¹ ·)` a.e." says `Ψ D_A = D_A Φ`. -/
theorem intertwines_iff_dilL1E_matEquiv (c : ℝ) (hc : c ≠ 0) (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : IsUnit A.det)
    (Φ Ψ : (EuclideanSpace ℝ (Fin d) →₁[volume] ℝ) →L[ℝ]
      (EuclideanSpace ℝ (Fin d) →₁[volume] ℝ)) :
    (∀ f g : EuclideanSpace ℝ (Fin d) →₁[volume] ℝ,
      ((g : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[volume]
        fun x => c * (f : EuclideanSpace ℝ (Fin d) → ℝ) (toEuclideanCLM (𝕜 := ℝ) A⁻¹ x)) →
      ((Ψ g : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[volume]
        fun x => c * (Φ f : EuclideanSpace ℝ (Fin d) → ℝ) (toEuclideanCLM (𝕜 := ℝ) A⁻¹ x))) ↔
    Ψ.comp (dilL1E (matEquiv A hA)) = (dilL1E (matEquiv A hA)).comp Φ :=
  intertwines_iff_dilL1E c hc (matEquiv A hA) Φ Ψ

/-- `D_A D_B = D_{AB}` for matrices. -/
theorem dilL1E_matEquiv_comp (A B : Matrix (Fin d) (Fin d) ℝ) (hA : IsUnit A.det)
    (hB : IsUnit B.det) :
    (dilL1E (matEquiv A hA)).comp (dilL1E (matEquiv B hB))
      = dilL1E (matEquiv (A * B) (by rw [det_mul]; exact hA.mul hB)) := by
  rw [dilL1E_comp, matEquiv_mul]

/-- An orthogonal matrix has `|det Q| = 1`. -/
lemma abs_det_of_transpose_mul_self {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Qᵀ * Q = 1) :
    |Q.det| = 1 := by
  have h : Q.det * Q.det = 1 := by
    have := congrArg Matrix.det hQ
    rwa [det_mul, det_transpose, det_one] at this
  have h2 : |Q.det| * |Q.det| = 1 := by rw [← abs_mul, h, abs_one]
  nlinarith [abs_nonneg Q.det]

lemma isUnit_det_of_transpose_mul_self {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Qᵀ * Q = 1) :
    IsUnit Q.det :=
  isUnit_iff_ne_zero.mpr fun h0 => by
    have := abs_det_of_transpose_mul_self hQ
    rw [h0, abs_zero] at this
    exact zero_ne_one this

/-- **A rotation** `R_Q f = f(Q⁻¹ ·)`, `Q` orthogonal, is the matrix dilation `D_Q`. -/
theorem coeFn_dilL1E_matEquiv_orthogonal {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Qᵀ * Q = 1)
    (f : EuclideanSpace ℝ (Fin d) →₁[volume] ℝ) :
    dilL1E (matEquiv Q (isUnit_det_of_transpose_mul_self hQ)) f =ᵐ[volume]
      fun x => (f : EuclideanSpace ℝ (Fin d) → ℝ) (toEuclideanCLM (𝕜 := ℝ) Q⁻¹ x) := by
  filter_upwards [coeFn_dilL1E_matEquiv Q (isUnit_det_of_transpose_mul_self hQ) f] with x hx
  rw [hx, abs_det_of_transpose_mul_self hQ, inv_one, one_mul]

/-- The scalar matrix `λ • 1` gives the homothety. -/
lemma matEquiv_smul_one {lam : ℝ} (hlam : lam ≠ 0) :
    matEquiv (lam • (1 : Matrix (Fin d) (Fin d) ℝ))
      (by rw [det_smul, det_one, mul_one]; exact (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hlam)))
      = homothety lam hlam := by
  refine ContinuousLinearEquiv.ext (funext fun x => ?_)
  change toEuclideanCLM (𝕜 := ℝ) (lam • (1 : Matrix (Fin d) (Fin d) ℝ)) x = lam • x
  rw [map_smul, map_one]
  rfl

end ScaleSpace
