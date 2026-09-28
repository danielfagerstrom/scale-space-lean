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
| `PowerSumSymmetry` | vanishing odd power sums make `∑ a_j² δ_{a_j}` reflection-invariant; the halving identity `∑ g (a_j) = 2 ∑ g (a_j⁺)` for even, quadratically bounded `g` |
| `CausalCone`, `CausalData` | `CausalAdmissible` (drift `b₀ ≥ 0`, nonincreasing delay profile `k ≥ 0`) with its exponent, the equivalence of the two finiteness forms (`ne_top_iff_windows`, `ofNeTop`), sums, multiples and dilations; the drift, Gamma and stable generators, with `F(σ) = σᵅ` for the last |
| `PolyaFrequencyClass` | the bilateral Laplace transform in Karlin sign and the class `E₂*` (`polyaE2`): multipliability, the `±` paired parameters on the imaginary axis, the real-axis log form, the modulus on the imaginary axis, and the symmetry reduction (evenness near `0` forces `δ = 0` and vanishing odd power sums) |

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

Queued from the spatial article's proving campaign (2026-09-10), in the order the two articles
would spend them: ~~the two-sided Laplace transform as an entire function on a strip with an
identity theorem~~ — **settled by a different route (2026-09-11, `PolyaFrequencyClass`,
`PowerSumSymmetry`).** The debt it was queued for is the matching between Karlin's class `E₂*`
(Total Positivity I, Ch. 7 (2.2) p. 336, Thm. 3.2(a) p. 345) and the spatial article's exponent.
Read at the letter, Karlin's identity already holds on an open strip containing the imaginary
axis (Prop. 1.4, p. 333), so no continuation off that axis is needed: what the matching consumes
is the modulus of `ψ` on the imaginary axis, the `±` pairing, and a symmetry reduction run on the
real axis (odd power sums, then a reflection-invariant atomic measure through Mathlib's
characteristic-function uniqueness). Mathlib's `complexMGF` already carries holomorphy on the
strip and the identity theorem, so no wrapper module was built; one can be added on second demand
(the causal article's one-sided `E₁` interface is the likely consumer). **Locally finite Laplace uniqueness on a half-line**
(proved identically in both articles, differing in one predicate); **the convolution transport
block and the transform bridge** (the spatial article's `ConvolutionOperator`, `TransformBridge`);
**the a.e.-tail / antitone-density toolkit** (`exists_antitone_density`, `tail_eq_of_ae_tail_eq`,
`eqOn_of_ae_eq_of_antitoneOn`); **variation diminution under convolution** and the test-function
uniqueness of finite measures. Each is article-independent and each has two consumers.

**Moved (2026-09-11): the causal admissible cone as a shared type** (`CausalCone`, `CausalData`).
Its extraction is right and Paper V (the spatial article) uses it heavily, keeping the field layout
and names in `SpatialLine.CausalAdmissible`; the second consumer is still to come. Paper I's Lean
is a released artefact behind a DOI and stays frozen at its release — its `SelfDecomposableExponent`
and the trunk's `CausalAdmissible` are provenance, not dependency (Paper I requires `ScaleSpaceCore v0.1.1`
but imports none of its declarations).

## License

Copyright (c) 2026 Daniel Fagerström.

Released under the Apache License, Version 2.0 — see [LICENSE](LICENSE). This matches the Mathlib
convention, so the library composes with the rest of the Lean mathematical library ecosystem
without a licence mismatch.
