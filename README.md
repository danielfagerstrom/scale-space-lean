# ScaleSpaceCore

A small Lean 4 library holding the article-independent part of a machine-checked development of
spatio-temporal scale-space theory: Lie wedges and infinitesimal covariance, the receptive-field
commutation lemmas, and the Galilean boost bracket, all proved from
[Mathlib](https://github.com/leanprover-community/mathlib4) alone.

It is the **shared core underneath the formalisation of the hemigroup / causal scale-space kernels
monograph**, and is factored out as its own Lake package because each article in this line
publishes its own DOI from its own repository. What more than one of them needs lives here, so a
result is proved once rather than copied.

## Using it

Add it to a downstream `lakefile.toml`:

```toml
[[require]]
name = "ScaleSpaceCore"
git = "https://github.com/danielfagerstrom/scale-space-lean"
rev = "v0.1.0"
```

Declarations live in `namespace ScaleSpace` — the field's namespace, not one article's. The module
root is `ScaleSpaceCore` so it cannot collide with a consuming article's own `ScaleSpace.*` modules.

## Build

```bash
lake exe cache get   # Mathlib, prebuilt
lake build
```

The toolchain is pinned in `lean-toolchain` to `leanprover/lean4:v4.31.0`, with Mathlib at the
matching tag. Consumers should track the same line: this library and the articles bump together,
deliberately, as one step.

## What is here

| Module | What |
|---|---|
| `Wedge` | `LieWedge` (a convex cone in a Lie algebra) and `CovariantTensor` (`[A_v, B_w] = B_{C v w}`) |
| `ReceptiveField` | `Solves A u` for a bounded generator `A : M →L[ℝ] M`; derivative-commutes-with-generator |
| `BoostBracket` | operator-algebra bracket identities over an arbitrary ℝ-algebra |
| `BoostBracketConcrete` | a Weyl-algebra (`MvPolynomial (Fin 3) ℝ`) faithful realisation grounding the structure constants |

Docstrings occasionally name a blueprint label (`def:lie-wedge`, `thm:receptive-field`,
`thm:galilean-nonexistence`) or a declaration such as `ScaleSpace.drift_forced`. Those point into
the consuming monograph's blueprint and formalisation, not into this package; nothing here depends
on them.

## No axioms, no cited interfaces

**This library carries no axioms and no cited analytic interfaces of its own.** It declares no
`axiom`, contains no `sorry`, and imports nothing outside Mathlib, so `#print axioms` on every result
reduces to the three Lean-core axioms Mathlib itself rests on — `propext`, `Classical.choice`,
`Quot.sound` — and a consumer's trust base gains nothing by depending on it. `AxiomCheck.lean` is
the standing local check of that property; it is not part of the default build target, so run it
directly (`lake env lean AxiomCheck.lean`).

That is the whole discipline of the repository, and it is why some material deliberately stayed
behind in the articles: anything phrased in terms of a particular symbol type, or resting on an
analytic interface from a particular article's axiom ledger, does not belong here.
`IsScaleSpaceWedge` is the worked example — it reads "the generating family is negative-definite
and conservative", which needs `Symbol d`, `NegativeDefinite` and `Conservative`, all
article-specific. Its abstract half (`LieWedge`, `CovariantTensor`) moved here; the predicate
stayed behind. Adding a module that carried an axiom would silently widen every downstream
article's trust base.

## Growing it

Seeded minimally, and extended **on second demand** — a result moves here when a second article
actually needs it, not when it looks general. Candidates being watched: the Cauchy functional
equation forcing `sᵅ`, and a Bernstein-function interface (a second article works with Bernstein
functions of nonincreasing Lévy density, so overlap is likely but unproven).

## License

Copyright (c) 2026 Daniel Fagerström.

Released under the Apache License, Version 2.0 — see [LICENSE](LICENSE). This matches the Mathlib
convention, so the library composes with the rest of the Lean mathematical library ecosystem
without a licence mismatch.
