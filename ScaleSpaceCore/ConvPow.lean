/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The `n`-fold convolution power of a measure

`convPow ν n = ν^{n*}`, the `n`-fold additive convolution of `ν` with itself (`ν^{0*} = δ₀`), on
any additive monoid. Second demand (Q-0361; Paper VII's formalisation session notes,
`spatial-hemigroup-affine/records/formalization/SKELETON.md`, Group E and the
`prop:origin-lower-bound-d` second-demand candidates): Paper VII's `Defs.Divisibility` states
`convPow` at this generality and eight of its modules read it; `MaternOrbit` and `SeparableMatern`
need it finite resp. a probability measure on `ℝ`, `OriginLowerBound` on `ℝ^d`.

Moved from Paper VII's `Formalization/AffineHemigroup/Defs/Divisibility.lean`,
`MaternOrbit.lean`, `SeparableMatern.lean` and `OriginLowerBound.lean`, statements unchanged
(`Rd d` there is `EuclideanSpace ℝ (Fin d)` here, an abbreviation, not a different type).
Generalizing `isFiniteMeasure_convPow` and `isProbabilityMeasure_convPow_real` to an arbitrary `E`
is left to the promotion cycle, not done here. `convList`, `IsInfinitelyDivisible`,
`compoundPoisson` and `cpLaw` have one live consumer each and stay behind.
-/

namespace ScaleSpace

open MeasureTheory

variable {E : Type*} [MeasurableSpace E]

/-- **The `n`-fold convolution power** `ν^{n*}`, with `ν^{0*} = δ₀`. -/
noncomputable def convPow [AddMonoid E] (ν : Measure E) : ℕ → Measure E
  | 0 => Measure.dirac 0
  | n + 1 => convPow ν n ∗ ν

/-- A convolution power of a finite measure is finite. -/
theorem isFiniteMeasure_convPow (L : Measure ℝ) [IsFiniteMeasure L] (n : ℕ) :
    IsFiniteMeasure (convPow L n) := by
  induction n with
  | zero => rw [convPow]; infer_instance
  | succ n ih => rw [convPow]; infer_instance

/-- A convolution power of a probability measure on the line is a probability measure. -/
theorem isProbabilityMeasure_convPow_real (L : Measure ℝ) [IsProbabilityMeasure L] (n : ℕ) :
    IsProbabilityMeasure (convPow L n) := by
  induction n with
  | zero => rw [convPow]; infer_instance
  | succ n ih => haveI := ih; rw [convPow]; infer_instance

variable {d : ℕ}

/-- A convolution power of a finite measure on `ℝ^d` is finite. -/
theorem isFiniteMeasure_convPow_Rd (L : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure L]
    (n : ℕ) : IsFiniteMeasure (convPow L n) := by
  induction n with
  | zero => rw [convPow]; infer_instance
  | succ n ih => rw [convPow]; infer_instance

end ScaleSpace
