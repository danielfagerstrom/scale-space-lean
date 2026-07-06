import ScaleSpace.Interfaces

/-!
# Covariance, Lie wedges, and the `G` scale-space — structural `[T]` defs

Abstract scaffolding for the infinitesimal framework (`blueprint` ch. "Generalities" and
"Infinitesimal generators"). These are definitions/`structure`s the theorems quantify over;
the concrete symbol model plugs in via `ScaleSpace.Symbol`. Kept deliberately abstract so
the non-existence argument depends only on the covariance/wedge interface, not on a specific
operator representation.
-/

namespace ScaleSpace

variable {ι : Type*}

/-- A Lie wedge: a closed cone in a Lie algebra, closed under the bracket only in the weak
(semigroup) sense (`blueprint: def:lie-wedge`). Not available in Mathlib; modelled locally.
Fields to be filled in Phase 1A (carrier `Set`, cone closure, weak bracket-closure). -/
structure LieWedge (L : Type*) [Ring L] : Type _ where
  carrier : Set L
  -- cone/closure axioms: TODO Phase 1A

/-- Infinitesimal covariance: `[A_v, B_w] = B_{C v w}` (`blueprint: def:infinitesimal-covariance`).
`A` is the Lie-algebra action of `G`, `B` the semigroup generators, `C` the covariance tensor. -/
structure CovariantTensor (L : Type*) [Ring L] where
  A : ι → L
  B : ι → L
  C : ι → ι → ι
  covariance : ∀ v w, A v * B w - B w * A v = B (C v w)

/-- A `𝔤` scale-space wedge: a minimal Lie wedge of negative-definite conservative covariant
tensor operators (`blueprint: def:g-wedge`). Predicate over a candidate generating family. -/
def IsScaleSpaceWedge {d : ℕ} (gens : ι → Symbol d) : Prop :=
  (∀ w, NegativeDefinite (gens w)) ∧ (∀ w, Conservative (gens w))
  -- ∧ covariance + minimality: TODO Phase 1A

end ScaleSpace
