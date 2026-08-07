import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NoncommRing

/-!
# The Galilean boost bracket — the space-and-memory resolution as an operator identity

Wiki `covariant-memory-evolution` (the joint space × memory × boost system); the research-direction
note in the finite-domain section of the blueprint. This is the **resolution-side** companion to
`ScaleSpace.drift_forced` (the *obstruction* side).

In the velocity-adapted memory formulation the temporal evolution operator is
`L_t^{(v)} = ∂_t + v · ∇_x − 𝓑` (`Lop`), with `𝓑` the memory generator and `v` the velocity, along
one spatial direction. Writing the Galilean generators as elements of the operator algebra `L` —
`dt = ∂_t`, `dj = ∂_x` (spatial translation), `boost = γ = t∂_x`, `B = 𝓑` — their commutators are
the Galilean structure constants (the same ones `drift_forced` posits):

* `[γ, ∂_t] = −∂_x`   (`boost * dt − dt * boost = −dj`),
* `[γ, ∂_x] = 0`,
* `[γ, 𝓑] = 0`        (the boost touches only `t, x`, not the memory).

From these the **boost bracket** is `[γ, L_t^{(v)}] = −∂_x = −∂_v L_t^{(v)}` (`boost_bracket`): the
boost acts on the velocity-indexed family as a *translation in `v`*. This is why space-and-memory
carries no obstruction — unlike a single space-time generator, whose `ad(γ)` cascade must close in a
finite basis and forces an integer temporal order (`drift_forced`, `thm:galilean-nonexistence`).
Here `[γ, L^{(v)}]` lands on `−∂_v L^{(v)}`, along the *continuous* `v` direction. That term is a
genuine Mathlib `deriv` (`hasDerivAt_Lop`: affine in `v`), so the bracket is a proved identity.

The structure constants are posited here (as in `drift_forced`); they are **proved** for genuine
differential operators (the Weyl algebra) in `ScaleSpace.BoostBracket.Concrete`, which instantiates
this file's `boost_comm_Lop` to give `boost_bracket_concrete` — the boost bracket with no posited
relation, `#print axioms` Lean-core only.
-/

namespace ScaleSpace.BoostBracket

variable {L : Type*}

/-- The velocity-adapted temporal evolution operator `L_t^{(v)} = ∂_t + v · ∂_x − 𝓑`, as an element
of the operator algebra, for scalar velocity `v` along one spatial direction. -/
def Lop [Ring L] [Module ℝ L] (dt dj B : L) (v : ℝ) : L := dt + v • dj - B

/-- `∂_v L_t^{(v)} = ∂_x`: the evolution is affine in the velocity, with slope the spatial
translation `dj`. -/
theorem hasDerivAt_Lop [NormedRing L] [NormedAlgebra ℝ L] (dt dj B : L) (v : ℝ) :
    HasDerivAt (Lop dt dj B) dj v := by
  have hs : HasDerivAt (fun w : ℝ => w • dj) dj v := by
    simpa using (hasDerivAt_id v).smul_const dj
  unfold Lop
  exact (hs.const_add dt).sub_const B

/-- The commutator `[γ, L_t^{(v)}] = −∂_x`, from the Galilean structure constants. Stated over a
general `ℝ`-algebra so a concrete operator algebra (e.g. `Module.End ℝ (MvPolynomial …)`) can
instantiate it — see `ScaleSpace.BoostBracket.Concrete`. -/
theorem boost_comm_Lop [Ring L] [Algebra ℝ L]
    (dt dj B boost : L)
    (h_dt : boost * dt - dt * boost = -dj)
    (h_dj : boost * dj - dj * boost = 0)
    (h_B : boost * B - B * boost = 0) (v : ℝ) :
    boost * Lop dt dj B v - Lop dt dj B v * boost = -dj := by
  have hdj : boost * (v • dj) - (v • dj) * boost = 0 := by
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, h_dj, smul_zero]
  have expand : boost * Lop dt dj B v - Lop dt dj B v * boost
      = (boost * dt - dt * boost) + (boost * (v • dj) - (v • dj) * boost)
        - (boost * B - B * boost) := by
    unfold Lop; noncomm_ring
  rw [expand, hdj, h_dt, h_B]
  simp

/-- **The boost bracket.** The Galilean boost `γ = t∂_x` acts on the velocity-adapted temporal
evolution `L_t^{(v)}` as a translation in the velocity parameter: `[γ, L_t^{(v)}] = −∂_v L_t^{(v)}`.
The space-and-memory resolution of the non-existence theorem as one operator identity. -/
theorem boost_bracket [NormedRing L] [NormedAlgebra ℝ L]
    (dt dj B boost : L)
    (h_dt : boost * dt - dt * boost = -dj)
    (h_dj : boost * dj - dj * boost = 0)
    (h_B : boost * B - B * boost = 0) (v : ℝ) :
    boost * Lop dt dj B v - Lop dt dj B v * boost = -deriv (Lop dt dj B) v := by
  rw [boost_comm_Lop dt dj B boost h_dt h_dj h_B v, (hasDerivAt_Lop dt dj B v).deriv]

end ScaleSpace.BoostBracket
