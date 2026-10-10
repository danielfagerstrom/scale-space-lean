/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import ScaleSpaceCore.L1Operators
import ScaleSpaceCore.Transform

/-!
# The reflection-symmetric cascade family on `L¹(ℝ)`: the axioms, as structures

Home: line:def:cascade-family

Moved by Q-0301 from Paper V's `SpatialLine/Family.lean` (the structures and predicates) and
`SpatialLine/Covariance.lean` (`IsScaleCovariant.S_zero`, `IsScaleCovariant.S_pos`) at `v0.1`,
statements verbatim up to the namespace. Paper V states its line classification in these, and
Paper VII constructs a `CascadeCore` from the marginals of an isotropic family and states its own
hypotheses in them: the structures themselves are used by two modules, which is case (c) of the
second-demand test (hub `RELEASES.md` § "Dependencies between modules"), the case
`CausalAdmissible` moved under in `v0.2.0`.

## Fidelity notes

* **(A1)** is carried by the type: `X →L[ℝ] X` *is* "bounded linear operator on `X`".
* **(A2)** and **(A3)** are stated pointwise in `f`, which is the same as the operator identities
  `Φ T_a = T_a Φ`, `Φ R = R Φ`. (A3) needs no a.e. hedging: `reflL1` is an operator on `L¹`, so
  the identity is between elements of `L¹`.
* **(A5)** is stated on the positive cone only. It happens to hold on all of `X` for a
  convolution operator, but strengthening the field would *narrow* the structure.
* **(A8)** carries the action `S` as data together with the requirement that each `S lam` be an
  increasing bijection of `[0,∞)`; quantifying `S` existentially is rendered by bundling it.
* **`IsScaleCovariant`** is stated relative to a set `G` of admissible dilation ratios, so that a
  discrete module can instantiate `G = q^ℤ` without restating the core; `CascadeFamily` demands
  `G = Ioi 0`. It takes the *operator family* rather than a `CascadeCore`.

## Positivity is split off

A family satisfying everything but (A4) has to be expressible, so the axioms other than
positivity are `PreCascadeCore`, positivity is the predicate `IsPositive` on an operator family,
and `CascadeCore extends PreCascadeCore` with the positivity and nondegeneracy fields.

## The kernel family is a hypothesis, not a definition

`IsKernelFamily` names a family of kernels representing the operators, and downstream statements
quantify over any `μ` meeting the specification; the representation lemma that produces one
(Paper V's `exists_kernelFamily`) has not moved.
-/

namespace ScaleSpace

open MeasureTheory Set
open scoped ENNReal

/-- **The cascade-family axioms without (A4) and without (ND)**: exactly (A1)–(A3) and
(A5)–(A7). Positivity and nondegeneracy are separate predicates so that each statement can carry
the hypotheses it needs and no more. -/
structure PreCascadeCore where
  /-- The operators, indexed by ordered pairs of scales. **(A1)** is the type. -/
  Φ : ℝ → ℝ → (X →L[ℝ] X)
  /-- **(A2)** Translation covariance. -/
  translation : ∀ s t, 0 ≤ s → s ≤ t → ∀ a f, Φ s t (transL1 a f) = transL1 a (Φ s t f)
  /-- **(A3)** Reflection symmetry — the one axiom that differs from the causal system. -/
  reflection : ∀ s t, 0 ≤ s → s ≤ t → ∀ f, Φ s t (reflL1 f) = reflL1 (Φ s t f)
  /-- **(A5)** Unit mass, on the positive cone.

  The restriction to `IsNonneg f` is the axiom's own. **Do not "strengthen" it to all of `X`**:
  a strengthened field would exclude families the axioms admit. -/
  unit_mass : ∀ s t, 0 ≤ s → s ≤ t → ∀ f, IsNonneg f →
    ∫ x, ((Φ s t f : X) : ℝ → ℝ) x = ∫ x, (f : ℝ → ℝ) x
  /-- **(A6)** The diagonal is the identity. -/
  diag : ∀ t, 0 ≤ t → Φ t t = ContinuousLinearMap.id ℝ X
  /-- **(A6)** The cascade law — a hemigroup, not a semigroup: no dependence on `t - s`. -/
  cascade : ∀ r s t, 0 ≤ r → r ≤ s → s ≤ t → (Φ s t).comp (Φ r s) = Φ r t
  /-- **(A7)** Continuity in the parameters, into `X`. -/
  continuous : ∀ f : X, ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2 f)
    {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2}

/-- **(A4)**, as a predicate on an operator family. -/
def IsPositive (Φ : ℝ → ℝ → (X →L[ℝ] X)) : Prop :=
  ∀ s t, 0 ≤ s → s ≤ t → ∀ f, IsNonneg f → IsNonneg (Φ s t f)

/-- **(ND)**, as a predicate on an operator family. -/
def IsNondegenerate (Φ : ℝ → ℝ → (X →L[ℝ] X)) : Prop :=
  ∀ s t, 0 ≤ s → s < t → Φ s t ≠ ContinuousLinearMap.id ℝ X

/-- **(A1)–(A7) and (ND)**: everything in the definition of a cascade family that does not
mention the covariance group. -/
structure CascadeCore extends PreCascadeCore where
  /-- **(A4)** Positivity. -/
  positive : IsPositive toPreCascadeCore.Φ
  /-- **(ND)** Nondegeneracy. -/
  nondegenerate : IsNondegenerate toPreCascadeCore.Φ

/-- **(A8), relative to a set `G` of admissible dilation ratios.**

`G` is an arbitrary set rather than a subgroup: the axiom is a condition *for each* `lam`, and
which sets `G` can occur is a theorem, not part of the statement. -/
structure IsScaleCovariant (Φ : ℝ → ℝ → (X →L[ℝ] X)) (G : Set ℝ) (S : ℝ → ℝ → ℝ) : Prop where
  /-- Each `S lam` maps `[0,∞)` into itself, ... -/
  S_mapsTo : ∀ lam, 0 < lam → lam ∈ G → MapsTo (S lam) (Ici 0) (Ici 0)
  /-- ... increasingly, ... -/
  S_strictMonoOn : ∀ lam, 0 < lam → lam ∈ G → StrictMonoOn (S lam) (Ici 0)
  /-- ... and onto. -/
  S_surjOn : ∀ lam, 0 < lam → lam ∈ G → SurjOn (S lam) (Ici 0) (Ici 0)
  /-- The intertwining itself. -/
  scale : ∀ (lam : ℝ) (hlam : 0 < lam), lam ∈ G → ∀ s t, 0 ≤ s → s ≤ t →
    (dilL1 hlam).comp (Φ s t) = (Φ (S lam s) (S lam t)).comp (dilL1 hlam)

/-- **A symmetric cascade measurement family** — the core, with (A8) demanded for every
`lam > 0`. -/
structure CascadeFamily extends CascadeCore where
  /-- The scaling action `S_lam` of (A8), carried as data. -/
  S : ℝ → ℝ → ℝ
  /-- **(A8)** Scale covariance, under the full dilation group. -/
  covariant : IsScaleCovariant toCascadeCore.Φ (Ioi 0) S

/-- **`μ` represents `Fam`**: each operator is convolution by the probability measure `μ s t`.

The conclusion `Φ f = μ * f` is read at the level of representatives — the two sides are elements
of `L¹`, so a.e. equality of representatives is equality in `X`, and stating it this way avoids
carrying an `IsFiniteMeasure` instance argument through every signature. -/
structure IsKernelFamily (Φ : ℝ → ℝ → (X →L[ℝ] X)) (μ : ℝ → ℝ → Measure ℝ) : Prop where
  /-- Each kernel is a probability measure. -/
  isProbability : ∀ s t, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t)
  /-- Each operator is convolution by its kernel. -/
  conv : ∀ s t, 0 ≤ s → s ≤ t → ∀ f : X,
    ((Φ s t f : X) : ℝ → ℝ) =ᵐ[volume] mconv (μ s t) (f : ℝ → ℝ)

/-- The kernels are symmetric — the rider (A3) adds to the representation. -/
def IsSymmetricKernelFamily (μ : ℝ → ℝ → Measure ℝ) : Prop :=
  ∀ s t, 0 ≤ s → s ≤ t → IsSymmetric (μ s t)

/-! ## The scaling action -/

/-- **An increasing bijection of `[0,∞)` fixes `0`.** -/
lemma IsScaleCovariant.S_zero {Φ : ℝ → ℝ → (X →L[ℝ] X)} {Gs : Set ℝ} {S : ℝ → ℝ → ℝ}
    (hcov : IsScaleCovariant Φ Gs S) {lam : ℝ} (hlam : 0 < lam) (hmem : lam ∈ Gs) :
    S lam 0 = 0 := by
  obtain ⟨u, hu, hSu⟩ := hcov.S_surjOn lam hlam hmem (Set.self_mem_Ici : (0:ℝ) ∈ Ici 0)
  have hu0 : (0:ℝ) ≤ u := hu
  rcases eq_or_lt_of_le hu0 with h | h
  · rw [← h] at hSu; exact hSu
  · exfalso
    have hlt := hcov.S_strictMonoOn lam hlam hmem (Set.self_mem_Ici : (0:ℝ) ∈ Ici 0) hu h
    have hnn : (0:ℝ) ≤ S lam 0 := hcov.S_mapsTo lam hlam hmem (Set.self_mem_Ici : (0:ℝ) ∈ Ici 0)
    rw [hSu] at hlt
    linarith

/-- **The action moves `(0,∞)` into itself.** -/
lemma IsScaleCovariant.S_pos {Φ : ℝ → ℝ → (X →L[ℝ] X)} {Gs : Set ℝ} {S : ℝ → ℝ → ℝ}
    (hcov : IsScaleCovariant Φ Gs S) {lam : ℝ} (hlam : 0 < lam) (hmem : lam ∈ Gs)
    {t : ℝ} (ht : 0 < t) : 0 < S lam t := by
  have := hcov.S_strictMonoOn lam hlam hmem (Set.self_mem_Ici : (0:ℝ) ∈ Ici 0)
    (le_of_lt ht : t ∈ Ici (0:ℝ)) ht
  rwa [hcov.S_zero hlam hmem] at this

end ScaleSpace
