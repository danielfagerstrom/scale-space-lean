/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Mathlib.Algebra.Module.Defs
-- ℝ's own algebraic instances. Module.Defs supplies `Module`, not `Semiring ℝ`; before the
-- split those arrived transitively through the article's Interfaces module
-- (Mathlib.Data.Complex.Basic). This is the minimal import that provides them directly.
import Mathlib.Data.Real.Basic

/-!
# Lie wedges and infinitesimal covariance — the abstract scaffolding

Definitions the scale-space theorems quantify over, kept deliberately free of any concrete
operator representation so that an argument depending only on the covariance/wedge interface
does not drag in a symbol model.

This module is shared across articles. The *admissibility* predicate that says a generating
family is negative-definite and conservative is deliberately **not** here: it is phrased in
terms of a particular symbol type and the analytic interfaces grounded in a particular
article's axiom ledger, so it belongs to that article.
-/

namespace ScaleSpace

variable {ι : Type*}

/-- A Lie wedge: a closed cone in a Lie algebra, closed under the bracket only in the weak
(semigroup) sense (`blueprint: def:lie-wedge`). Not available in Mathlib; modelled locally.

The **convex-cone** content is captured concretely here: the carrier contains `0` and is closed
under addition and non-negative real scaling. The remaining two properties of a *Lie* wedge —
topological closedness and weak bracket-closure `⁅v,w⁆ ∈` wedge (one-sided) — need a topology and a
Lie bracket on `L` and are deferred; for translation-invariant symbols the bracket vanishes
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

end ScaleSpace
