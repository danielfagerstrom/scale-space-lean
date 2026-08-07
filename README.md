# scale-space-lean

The Lean 4 material shared across the scale-space article repos: `ScaleSpaceCore`.

Each article publishes its own Zenodo DOI from its own repo, so the articles are separate
repositories. This holds what more than one of them needs, so a result is proved once.

```toml
[[require]]
name = "ScaleSpaceCore"
git = "https://github.com/danielfagerstrom/scale-space-lean"
rev = "v0.1.0"
```

## What is here, and what deliberately is not

| Module | What |
|---|---|
| `Wedge` | `LieWedge` (a convex cone in a Lie algebra) and `CovariantTensor` (`[A_v, B_w] = B_{C v w}`) |
| `ReceptiveField` | `Solves A u` for a bounded generator `A : M →L[ℝ] M`; derivative-commutes-with-generator |
| `BoostBracket` | operator-algebra bracket identities over an arbitrary ℝ-algebra |
| `BoostBracketConcrete` | a Weyl-algebra (`MvPolynomial (Fin 3) ℝ`) faithful realisation grounding the structure constants |

Declarations live in `namespace ScaleSpace` — the field's namespace, not one article's. The
module root is `ScaleSpaceCore` so it cannot collide with an article's own `ScaleSpace.*`
modules.

**Not here, on purpose:** anything phrased in terms of a particular symbol type or resting on
an analytic interface from a particular article's axiom ledger. `IsScaleSpaceWedge` is the
worked example — it reads "the generating family is negative-definite and conservative", which
needs `Symbol d`, `NegativeDefinite` and `Conservative`, all article-specific. Its abstract
half (`LieWedge`, `CovariantTensor`) moved here; the predicate stayed behind.

That line is the whole discipline of this repo: **it holds nothing that rests on a cited
interface.** Everything here is proved from Mathlib alone, so a consumer's `#print axioms`
gains nothing from depending on it. Adding a module that carries an axiom would silently widen
every downstream article's trust base.

## Growing it

Seeded minimally, and extended **on second demand** — a result moves here when a second
article actually needs it, not when it looks general. Candidates being watched: the Cauchy
functional equation forcing `sᵅ`, and a Bernstein-function interface (article #2 works with
Bernstein functions of nonincreasing Lévy density, so overlap is likely but unproven).

## Build

```bash
lake exe cache get   # Mathlib, prebuilt
lake build
```

Toolchain is pinned to `leanprover/lean4:v4.31.0` with Mathlib at the matching tag. Consumers
should track the same line: this library and the articles bump together, deliberately, as one
step.
