/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import ScaleSpaceCore.SDProfile

/-!
# The function classes: positive definiteness, `NDₛ` and `LEₛ`

Blueprint (Paper V): `def:positive-definite` (2.1), `def:symmetric-negdef` (2.2), and the class
`LEₛ` of exponents of the form `eq:levy-khintchine`. The representation's data, `SymLevyPair`,
and the profile form, `SDProfile`, are in `SDProfile`; this module adds the three predicates the
line classification states its interfaces and its increments in.

`prop:fourier-toolbox`(3) is the statement that `LEₛ = NDₛ`. It is cited, not proved, so the
two directions the classification spends are hypotheses (`LineInterfaces`), not theorems here.

## Provenance

Moved by Q-0305 from Paper V's `SpatialLine/Exponent.lean` (the public cone export, `cone-v0.1`,
commit `f28c066e`) for the line classification (`MainAnalysis`, `MainConstruction`): only
`IsPositiveDefinite`, `IsSymNegDef` and `IsSymLevyExponent`, unchanged up to the namespace.
`IsNegDefKernel` stayed behind; the rest of that file had already moved into `SDProfile`.
-/

namespace ScaleSpace

open MeasureTheory Set
open scoped ENNReal ComplexOrder

/-! ## `def:positive-definite` and `def:symmetric-negdef` -/

/-- **`def:positive-definite`.** `∑_{j,k} c_j conj(c_k) φ(ω_j - ω_k) ≥ 0` for every finite
family.

Reading: the double sum is asserted to be a *nonnegative real*, which is what `0 ≤ z` means for
`z : ℂ` under `ComplexOrder` (`0 ≤ z.re` and `z.im = 0`). The blueprint writes `≥ 0` of a
complex expression and means exactly that; Hermitian symmetry of `φ` is thereby part of the
assertion rather than a separate consequence, which is the standard convention. Finite families
are indexed by `Fin n`, which loses nothing. -/
def IsPositiveDefinite (φ : ℝ → ℂ) : Prop :=
  ∀ (n : ℕ) (ω : Fin n → ℝ) (c : Fin n → ℂ),
    0 ≤ ∑ j, ∑ k, c j * (starRingEnd ℂ) (c k) * φ (ω j - ω k)

/-- **`def:symmetric-negdef`**, the class `NDₛ`: continuous, even, nonnegative, vanishing at the
origin, with `e^{-τψ}` positive definite for every `τ > 0`.

The exponential form is primitive, as the blueprint's status annotation insists, so that the
class is defined with no derivative and Schoenberg's theorem (`prop:fourier-toolbox`(2)) is
needed only to import results stated for the kernel form.

twin: `Hemigroup.levyExponent`'s defining node `def:bernstein-function` — same structural role,
opposite defining device. -/
structure IsSymNegDef (ψ : ℝ → ℝ) : Prop where
  /-- `ψ` is continuous. -/
  continuous : Continuous ψ
  /-- `ψ` is even. -/
  even : ∀ ω, ψ (-ω) = ψ ω
  /-- `ψ` takes values in `[0,∞)`. -/
  nonneg : ∀ ω, 0 ≤ ψ ω
  /-- `ψ(0) = 0`. -/
  map_zero : ψ 0 = 0
  /-- `e^{-τψ}` is positive definite for every `τ > 0`. -/
  exp_posDef : ∀ τ : ℝ, 0 < τ → IsPositiveDefinite fun ω => (Real.exp (-(τ * ψ ω)) : ℂ)

/-! ## `LEₛ`: the symmetric Lévy–Khintchine form (2.2) -/

/-- **The class `LEₛ`**: the functions of the form `eq:levy-khintchine`.

`prop:fourier-toolbox`(3) is the statement that `LEₛ = NDₛ`; this article's proofs manipulate
`LEₛ`, and `NDₛ` appears only where the blueprint's text does. -/
def IsSymLevyExponent (ψ : ℝ → ℝ) : Prop := ∃ P : SymLevyPair, ∀ ω, ψ ω = P.exponent ω

end ScaleSpace
