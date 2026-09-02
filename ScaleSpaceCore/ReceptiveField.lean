/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Receptive-field level: derivatives of a scale-space are scale-spaces, and the temporal jet
is memory-axis powers of the generator

`blueprint: thm:receptive-field`. Two structural facts the receptive-field / N-jet chapter rests
on, both consequences of **differentiation commuting with the (constant-coefficient) generator**.

We model the evolution abstractly: a curve `u : ℝ → M` in a normed state space `M` solves
`∂_s u = A u` for a (bounded) generator `A : M →L[ℝ] M` (`Solves A u`). This is the algebraic
skeleton — the concrete generator is an unbounded differential operator, but the two facts below are
purely algebraic (commutation of operators) and hold verbatim here, exactly as
`ScaleSpace.BoostBracket` works with abstract operators.

* **`Solves.clm_comp`** — if a derivative operator `D` commutes with the generator `A`, then `D`
  maps a solution to a solution. Reading `D = ∂_x` (a receptive-field-forming derivative): *a
  spatial derivative of a scale-space is itself a scale-space*, so the Gaussian-derivative
  receptive fields are legitimate scale-space measurements.
* **`iteratedDeriv_solves`** — the temporal jet lives on the memory axis: the `k`-th time
  derivative of a solution is the `k`-th power of the generator, `∂_t^k u = A^k u`. Every temporal
  derivative in the jet is therefore a memory-axis operation (a power of `A`), never a `∂_t` of the
  raw signal — the framework-consistency constraint of the chapter.

Both reduce to `hasDerivAt_clm_comp`: a continuous linear map commutes with differentiation of a
curve. `#print axioms` on the results is Lean core only.
-/

namespace ScaleSpace.ReceptiveField

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]

/-- A continuous linear map commutes with differentiation of a curve:
`d/ds (L (u s)) = L (u' )`. -/
theorem hasDerivAt_clm_comp (L : M →L[ℝ] M) {u : ℝ → M} {u' : M} {t : ℝ}
    (h : HasDerivAt u u' t) : HasDerivAt (fun s => L (u s)) (L u') t := by
  simpa [Function.comp_def] using (L.hasFDerivAt.comp t h.hasFDerivAt).hasDerivAt

/-- `deriv`-form of `hasDerivAt_clm_comp`. -/
theorem deriv_clm_comp (L : M →L[ℝ] M) {g : ℝ → M} {t : ℝ} (hg : DifferentiableAt ℝ g t) :
    deriv (fun s => L (g s)) t = L (deriv g t) :=
  (hasDerivAt_clm_comp L hg.hasDerivAt).deriv

/-- A curve `u` solves the abstract scale-space evolution `∂_s u = A u`. -/
def Solves (A : M →L[ℝ] M) (u : ℝ → M) : Prop := ∀ s, HasDerivAt u (A (u s)) s

/-- **Receptive fields are scale-spaces.** If a derivative operator `D` commutes with the
generator `A`, then `D` carries a solution to a solution: `∂_x` of a scale-space solves the same
evolution, so a Gaussian-derivative receptive field is a legitimate scale-space measurement. -/
theorem Solves.clm_comp {A D : M →L[ℝ] M} (hAD : D.comp A = A.comp D)
    {u : ℝ → M} (hu : Solves A u) : Solves A (fun s => D (u s)) := by
  intro s
  have h1 : HasDerivAt (fun r => D (u r)) (D (A (u s))) s := hasDerivAt_clm_comp D (hu s)
  have h2 : D (A (u s)) = A (D (u s)) := congrArg (fun T : M →L[ℝ] M => T (u s)) hAD
  rw [h2] at h1
  exact h1

/-- **The temporal jet is memory-axis powers of the generator.** For a solution of
`∂_t u = A u`, the `k`-th time derivative is `∂_t^k u = A^k u` — a memory-axis operation (a power of
the generator), not a derivative of the signal in time. This is the framework-consistency
constraint: the temporal part of the N-jet stays inside the causal, memory-based account of time. -/
theorem iteratedDeriv_solves (A : M →L[ℝ] M) {u : ℝ → M} (hu : Solves A u) (k : ℕ) :
    iteratedDeriv k u = fun t => (A ^ k) (u t) := by
  induction k with
  | zero => funext t; simp [iteratedDeriv_zero]
  | succ k ih =>
      funext t
      rw [iteratedDeriv_succ, ih, deriv_clm_comp (A ^ k) (hu t).differentiableAt, (hu t).deriv,
          pow_succ, ContinuousLinearMap.mul_apply]

end ScaleSpace.ReceptiveField
