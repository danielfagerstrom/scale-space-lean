import ScaleSpaceCore.BoostBracket
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Grounding the Galilean structure constants in the Weyl algebra

`ScaleSpace.BoostBracket` derives the boost bracket from *posited* Galilean structure constants
(as `drift_forced` does). Here those constants are **proved**, by realizing the generators as
differential operators on `MvPolynomial (Fin 3) ℝ` (variables `t = 0`, spatial `x = 1`, memory
`τ = 2`) — the Weyl algebra, a faithful representation, so the relations are not vacuous.

The operators are endomorphisms `Module.End ℝ M`: `Dt = ∂_t`, `Dj = ∂_x`, `Bmem = ∂_τ` (a memory
generator), `Boost = γ = X_t · ∂_x`. We prove `[Boost, Dt] = −Dj`, `[Boost, Dj] = 0`,
`[Boost, Bmem] = 0` from `pderiv` calculus (Leibniz + `pderiv_comm`, mixed-partial symmetry got
from the Lie bracket of derivations), then feed them to the abstract `boost_comm_Lop` to get the
boost bracket for the concrete operators (`boost_bracket_concrete`). No relation is posited.
-/

namespace ScaleSpace.BoostBracket.Concrete

open MvPolynomial

/-- **Mixed partials commute** (Clairaut, algebraically for polynomials): the Lie bracket of the
derivations `pderiv i`, `pderiv j` vanishes on the generators `X k`, hence is `0`. -/
theorem pderiv_comm {σ : Type*} (i j : σ) (p : MvPolynomial σ ℝ) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  have hz : ∀ a b c : σ, (pderiv a) ((pderiv b) (X c : MvPolynomial σ ℝ)) = 0 := by
    intro a b c
    rcases eq_or_ne c b with rfl | h
    · rw [pderiv_X_self, pderiv_one]
    · rw [pderiv_X_of_ne h, map_zero]
  have h0 : ⁅(pderiv i : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ)),
      (pderiv j : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ))⁆ = 0 := by
    apply derivation_ext
    intro k
    simp [Derivation.commutator_apply, hz]
  have hp := DFunLike.congr_fun h0 p
  rw [Derivation.commutator_apply] at hp
  simpa [sub_eq_zero] using hp

/-- The polynomial algebra in variables `t = 0`, spatial `x = 1`, memory `τ = 2`. -/
abbrev M := MvPolynomial (Fin 3) ℝ

/-- `∂_t` as an operator. -/
noncomputable def Dt : Module.End ℝ M := (pderiv (0 : Fin 3)).toLinearMap
/-- `∂_x` (spatial translation) as an operator. -/
noncomputable def Dj : Module.End ℝ M := (pderiv (1 : Fin 3)).toLinearMap
/-- `∂_τ` — a memory generator, on the memory variable `τ = 2`. -/
noncomputable def Bmem : Module.End ℝ M := (pderiv (2 : Fin 3)).toLinearMap
/-- The Galilean boost `γ = t · ∂_x`, as multiplication by `X_t` after `∂_x`. -/
noncomputable def Boost : Module.End ℝ M := LinearMap.mulLeft ℝ (X (0 : Fin 3)) * Dj

theorem struct_Boost_Dt : Boost * Dt - Dt * Boost = - Dj := by
  apply LinearMap.ext; intro p
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply, Boost, Dt, Dj,
    LinearMap.mulLeft_apply, Derivation.coeFn_coe]
  rw [pderiv_mul, pderiv_X_self, pderiv_comm 1 0 p]
  ring

theorem struct_Boost_Dj : Boost * Dj - Dj * Boost = 0 := by
  apply LinearMap.ext; intro p
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply, Boost, Dj,
    LinearMap.mulLeft_apply, Derivation.coeFn_coe]
  rw [pderiv_mul, pderiv_X_of_ne (by decide : (0 : Fin 3) ≠ 1)]
  ring

theorem struct_Boost_Bmem : Boost * Bmem - Bmem * Boost = 0 := by
  apply LinearMap.ext; intro p
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply, Boost, Bmem, Dj,
    LinearMap.mulLeft_apply, Derivation.coeFn_coe]
  rw [pderiv_mul, pderiv_X_of_ne (by decide : (0 : Fin 3) ≠ 2), pderiv_comm 1 2 p]
  ring

/-- **The boost bracket for genuine differential operators.** Instantiating the abstract
`boost_comm_Lop` at the Weyl-algebra realization: with `Lop v = ∂_t + v·∂_x − ∂_τ`,
`[γ, L_t^{(v)}] = −∂_x`. No structure constant is posited — all three are proved above. -/
theorem boost_bracket_concrete (v : ℝ) :
    Boost * ScaleSpace.BoostBracket.Lop Dt Dj Bmem v
      - ScaleSpace.BoostBracket.Lop Dt Dj Bmem v * Boost = - Dj :=
  ScaleSpace.BoostBracket.boost_comm_Lop Dt Dj Bmem Boost
    struct_Boost_Dt struct_Boost_Dj struct_Boost_Bmem v

end ScaleSpace.BoostBracket.Concrete
