/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import ScaleSpaceCore.SDProfile

/-!
# The function classes: positive definiteness, `NDₛ`, `LEₛ`, and the self-decomposable profile

Blueprint: `blueprint/src/parts/02-preliminaries.tex` — `def:positive-definite` (2.1),
`def:symmetric-negdef` (2.2), the representation (2.2)/`eq:levy-khintchine`, and the profile
form (2.5)/`eq:sd-profile`.

## Representation first

`prop:fourier-toolbox`'s status annotation says it: "The classes `NDₛ` and `LEₛ` are the same
class, named by the definition and by the representation respectively; this article's proofs
manipulate the representation, and the machine-checked development is expected to define `LEₛ`
alone." Both are defined here, because `def:positive-definite` and `def:symmetric-negdef` are
blueprint nodes and a node needs a faithful Lean twin; but `SymLevyPair` is the object every
later chapter works with, and `prop:fourier-toolbox`(3) is the only place the two meet.

This is Paper I's rule (`def:bernstein-function` ⇄ `Hemigroup.levyExponent`) with the Laplace
side replaced by the Fourier side.

## Two `ℝ≥0∞`-first definitions

`SymLevyPair.exponentL` and `SDProfile.exponentL` are `lintegral`s, so they need no
integrability side condition and the elementary facts about them are unconditional; the
real-valued versions are `.toReal` of those. Finiteness is not a field of either structure: it
is `lem:quadratic-growth`, a node, and stating it that way is what keeps the structures free of
a condition whose proof the blueprint owns.

twin: `Hemigroup.levyExponent` / `Hemigroup.levyExponentD` (the same design, opposite transform).

## The profile structure and the bridge

`SDProfile`'s fields are laid out to be field-for-field parallel with Paper I's
`Hemigroup.SelfDecomposableExponent` — `b₀ ↦ a`, then `k`, `b₀_nonneg ↦ a_nonneg`, `k_nonneg`,
`k_antitone`, `k_zero` — so that the bridge map of `lem:bridge-exponents` (blueprint (9.1)–(9.2),
phase B) is a function between two structures with parallel fields and no reshaping. The one
deliberate divergence is the last field: Paper I carries a single finiteness condition
`ne_top`, this structure carries the *two* integrability conditions the blueprint states in
`lem:profile-integrability`, because those are what every family in this article is tested
against. `lem:profile-integrability` is the node that relates the two.

`k_zero` is a normalisation, not a constraint, exactly as in Paper I: `k` is a density against
`dx/x` on `(0,∞)` and every other field leaves `k 0` free.
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
