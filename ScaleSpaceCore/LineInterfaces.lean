/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import ScaleSpaceCore.Exponent
import ScaleSpaceCore.Transform

/-!
# The cited interfaces of the line classification, as hypotheses

Home: line:prop:fourier-toolbox

The line classification ([V, Thm. 7.3]: `main_analysis`, `main_uniqueness`, `main_construction`)
rests in Paper V on three cited clauses, admitted there as axioms. This library declares no axiom
(ADR-0026 § 5), so each clause is a `Prop` here, stated in exactly the shape of Paper V's axiom of
the same content, and a trunk theorem that needs one takes it as a **hypothesis**. The article
that draws the conclusion discharges it from its own ledger: Paper V with its axiom of the same
name; Paper VII (`spatial-hemigroup-affine`) from its own ledger entry A3, Sato Thm. 8.1 on `ℝ^d`,
read at `d = 1`.

| hypothesis | source clause | Paper V's axiom (ledger) |
|---|---|---|
| `SymLevyUnique` | Sato Thm. 8.1(ii), uniqueness | `fourier_toolbox_levy_unique` (A3) |
| `SymLevyConverse` | Sato Thm. 8.1(iii), converse | `fourier_toolbox_levy_converse` (A3) |
| `BochnerSymm` | Sato Prop. 2.5, Bochner, symmetric | `fourier_toolbox_bochner_symm` (A1) |

The source is @sato1999levy (Sato, *Lévy Processes and Infinitely Divisible Distributions*,
1999): Thm. 8.1 on pp. 37–38, Prop. 2.5 on pp. 8–9.

## Which theorem takes which

* `main_analysis` and `main_analysis_exists` take `SymLevyUnique` and nothing else. It is spent
  once, in `dilate_le_of_increments`, and reaches them through `exists_profile_of_dilate_le` and
  `sd_exponents_one_implies_three`.
* `main_uniqueness` takes none: it was Lean core in Paper V and is Lean core here.
* `main_construction` takes `LineLawInterfaces`, the bundle of `SymLevyConverse` and
  `BochnerSymm`. Both are spent at the single step that turns a symmetric Lévy exponent into the
  law it is the exponent of (`exists_isSymmetric_of_isSymLevyExponent`), and never apart, which is
  why they travel as one hypothesis; the fields keep them separately dischargeable.

## What the folding convention puts inside the hypotheses

`SymLevyPair` carries a *folded* Lévy measure on `(0,∞)`, not a symmetric measure on `ℝ ∖ {0}`,
so the two Lévy–Khintchine clauses here are Sato's statements composed with the folding
reduction. That reduction is elementary — a symmetric Lévy measure and its image under `x ↦ |x|`
carry the same `∫ (1 - cos ωx)` and the same integrability — but it is inside the statements, as
it is inside Paper V's axioms (that article's fidelity review, R37). An article discharging these
from Sato on the punctured line supplies the reduction.
-/

namespace ScaleSpace

open MeasureTheory

/-- **The uniqueness clause of the symmetric Lévy–Khintchine representation on `ℝ`**: two
symmetric Lévy pairs with the same exponent have the same Gaussian coefficient and the same
(folded) Lévy measure.

Source: @sato1999levy Thm. 8.1(ii), p. 37 — the triplet `(A, ν, γ)` representing an infinitely
divisible law is unique — read on the symmetric laws of `ℝ` (`γ = 0`, `ν` folded onto `(0,∞)`).
This is exactly the statement of Paper V's `SpatialLine.fourier_toolbox_levy_unique` (ledger
A3), which discharges it verbatim; Paper VII's A3 (Sato Thm. 8.1 on `ℝ^d`) contains it at `d = 1`.

Spent by `dilate_le_of_increments`, and through it by `main_analysis`. -/
def SymLevyUnique : Prop :=
  ∀ P Q : SymLevyPair, (∀ ω, P.exponent ω = Q.exponent ω) → P.a = Q.a ∧ P.ν = Q.ν

/-- **The converse clause of the symmetric Lévy–Khintchine representation on `ℝ`**: the exponent
of every symmetric Lévy pair is a continuous negative definite function (`NDₛ`).

Source: @sato1999levy Thm. 8.1(iii), pp. 37–38 — every triplet is the triplet of an infinitely
divisible law — with Cor. 8.3, p. 38, for `e^{-τψ}` at every `τ > 0`, read on the symmetric laws
of `ℝ`. Of `IsSymNegDef`'s five fields only `exp_posDef` needs the citation; the shape is kept
because it is exactly the statement of Paper V's `SpatialLine.fourier_toolbox_levy_converse`
(ledger A3), which discharges it verbatim.

Spent by `exists_isSymmetric_of_isSymLevyExponent`, and through it by `main_construction`. -/
def SymLevyConverse : Prop :=
  ∀ P : SymLevyPair, IsSymNegDef P.exponent

/-- **Bochner's theorem, symmetric form, forward direction**: a real function that is
continuous, positive definite and `1` at the origin is the cosine transform of a symmetric
probability measure.

Source: @sato1999levy Prop. 2.5, pp. 8–9 ((i) and (ii) on p. 8, the symmetric rider using (v),
p. 9). Exactly the statement of Paper V's `SpatialLine.fourier_toolbox_bochner_symm` (ledger A1),
which discharges it verbatim; the reverse direction is elementary and is not a hypothesis.

Spent by `exists_isSymmetric_of_isSymLevyExponent`, and through it by `main_construction`. -/
def BochnerSymm : Prop :=
  ∀ φ : ℝ → ℝ, Continuous φ ∧ IsPositiveDefinite (fun ω => (φ ω : ℂ)) ∧ φ 0 = 1 →
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ IsSymmetric μ ∧ fourierCos μ = φ

/-- **The two interfaces the construction direction spends**, bundled: the converse clause of
the symmetric Lévy–Khintchine representation (`SymLevyConverse`) and Bochner's theorem
(`BochnerSymm`).

They are bundled because `main_construction` spends them together and only together — at the one
step that turns a symmetric Lévy exponent into a law — so the theorem reads with one hypothesis
for one step. Each field is the clause of one named source statement and is discharged
separately: Paper V by `⟨fourier_toolbox_levy_converse, fourier_toolbox_bochner_symm⟩`. A
`Prop`-valued structure, not an axiom. -/
structure LineLawInterfaces : Prop where
  /-- Sato Thm. 8.1(iii), the converse clause (Paper V's ledger A3). -/
  levy_converse : SymLevyConverse
  /-- Sato Prop. 2.5, Bochner's theorem, symmetric form (Paper V's ledger A1). -/
  bochner_symm : BochnerSymm

end ScaleSpace
