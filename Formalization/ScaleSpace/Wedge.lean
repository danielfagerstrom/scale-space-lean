import ScaleSpace.Interfaces
import Mathlib.Algebra.Module.Defs

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

The **convex-cone** content is captured concretely here: the carrier contains `0` and is closed
under addition and non-negative real scaling. The remaining two properties of a *Lie* wedge —
topological closedness and weak bracket-closure `⁅v,w⁆ ∈` wedge (one-sided) — need a topology and a
Lie bracket on `L` and are deferred; for the translation-invariant symbols the bracket vanishes
identically (`lem:translation-invariant`), so weak bracket-closure is automatic there. -/
structure LieWedge (L : Type*) [AddCommGroup L] [Module ℝ L] where
  carrier : Set L
  zero_mem : (0 : L) ∈ carrier
  add_mem : ∀ ⦃x⦄, x ∈ carrier → ∀ ⦃y⦄, y ∈ carrier → x + y ∈ carrier
  smul_mem : ∀ ⦃c : ℝ⦄, 0 ≤ c → ∀ ⦃x⦄, x ∈ carrier → c • x ∈ carrier

/-- Infinitesimal covariance: `[A_v, B_w] = B_{C v w}` (`blueprint: def:infinitesimal-covariance`).
`A` is the Lie-algebra action of `G`, `B` the semigroup generators, `C` the covariance tensor. -/
structure CovariantTensor (L : Type*) [Ring L] where
  A : ι → L
  B : ι → L
  C : ι → ι → ι
  covariance : ∀ v w, A v * B w - B w * A v = B (C v w)

/-- The *admissibility* half of a `𝔤` scale-space wedge: the generating family is negative-definite
and conservative (`blueprint: def:g-wedge`). Predicate over a candidate generating family.

The full `def:g-wedge` also asks the family be a *minimal Lie wedge of covariant tensor operators*
(`CovariantTensor`). That covariance condition `⁅A_v, B_w⁆ = B_{C v w}` involves the **position-
dependent** group generators `A_v` (e.g. the scaling symbol `i⁻¹ x ξ`), which do **not** live in
`Symbol d` (position-independent by construction). Folding covariance in therefore requires the full
ΨDO symbol algebra of `def:symbol`; until that is modelled it stays the analytic step the geometry
theorems cite, and `IsScaleSpaceWedge` captures exactly the neg-def + conservative part proved. -/
def IsScaleSpaceWedge {d : ℕ} (gens : ι → Symbol d) : Prop :=
  (∀ w, NegativeDefinite (gens w)) ∧ (∀ w, Conservative (gens w))

end ScaleSpace
