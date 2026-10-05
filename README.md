# ScaleSpaceCore

The hemigroup / causal scale-space kernels programme's **shared library** (ADR-0026): it holds what
more than one article needs, moved in on **second demand** — when a second article actually needs
a result, not when it merely looks general — with programme vocabulary allowed (cascades,
admissible cones, eventually the classification). It **carries no axiom**: where shared material
would otherwise rest on a cited analytic interface, it takes what that interface provides as a
**hypothesis** of its statement instead, and the article that draws the conclusion discharges the
hypothesis from its own ledger.

It may `require` `harmonic-semigroups`, the programme's separate Mathlib-quality library grown by a
tutored promotion cycle (not yet created); the dependency runs one way, and nothing here depends on
an article.

Everything currently here is proved from
[Mathlib](https://github.com/leanprover-community/mathlib4) alone: Lie wedges and infinitesimal
covariance, the receptive-field commutation lemmas, the Galilean boost bracket, the causal
admissible cone, and the L¹ / Bochner-convolution / Laplace-uniqueness infrastructure the causal
and spatial articles share. It is its own Lake package because each article in this line publishes
its own DOI from its own repository.

## Using it

Add it to a downstream `lakefile.toml`:

```toml
[[require]]
name = "ScaleSpaceCore"
git = "https://github.com/danielfagerstrom/scale-space-lean"
rev = "v0.2.0"
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
| `L1Operators` | `X = L¹(ℝ)`, translation (`transL1`) and convolution by a measure (`mconv`, `mconvL1`) with what the operator does — translation covariance, positivity, mass, composition — and the pairing lemma `integral_mul_mconv` |
| `BochnerConvolution` | convolution as an `X`-valued Bochner integral (`bconv`, `bconvM`), `Φ (f * g) = f * (Φ g)` (`map_bconv`), `bconv` as the classical pointwise convolution (`coeFn_bconv`), the Bochner form of `mconvL1` (`bconvM_eq_mconvL1`), and pairing against a bounded functional (`pairTrans`, `apply_mconvL1`) |
| `LaplaceUniqueness` | two finite measures on `[0,1]` with the same moments are equal (`ext_of_moments`), via the substitution `x = e^{-t}` (`expNeg`) and Stone–Weierstrass |
| `TailInverse` | the generalised inverse of a nonincreasing tail function (`tailInv`) and its order lemmas, the core of the Choquet-measure construction both articles' cone modules use |

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
actually needs it, not when it looks general. The test (`RELEASES.md`, hub, § "Dependencies between
modules") reads statements only: a declaration whose *statement* mentions only Mathlib types is
material for this library; one whose statement mentions a paper-specific structure stays in that
paper, reached by `require`ing its package at a release tag.

**No axiom moves in.** Where a statement would otherwise need to cite an article's analytic
interface, it takes what that interface provides as a **hypothesis** instead, and the article that
draws the conclusion discharges the hypothesis from its own axiom ledger (ADR-0026, Decision 5) — so
this library stays axiom-free while the shared statement is only the conditional one.

**Dependencies run one way.** This library may `require` `harmonic-semigroups`, the programme's
separate Mathlib-quality library grown only by a tutored promotion cycle (ADR-0026); never the
reverse, and nothing here depends on an article.

**Promotion empties this library, not the other way round.** When a promotion cycle lands a
declaration in `harmonic-semigroups` at its natural generality, the rebase step that follows moves
the shared library and the articles onto the promoted version and deletes the local copy here
(ADR-0026, Decision 3) — a module named below is not necessarily permanent.
`ScaleSpaceCore/LaplaceUniqueness.lean` is **candidate A**'s material (the Laplace transform of
measures on `[0,∞)` and its uniqueness; ADR-0026, Decision 6): it stays here until A's cycle
promotes it.

Candidates being watched: the Cauchy functional equation forcing `sᵅ`, and a Bernstein-function
interface (a second article works with Bernstein functions of nonincreasing Lévy density, so
overlap is likely but unproven).

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
(the causal article's one-sided `E₁` interface is the likely consumer). ~~Locally finite Laplace
uniqueness on a half-line~~ — **moved (2026-09-28, `LaplaceUniqueness`).** ~~The convolution
transport block~~ — **moved (2026-09-28, `L1Operators`, `BochnerConvolution`).** **The transform
bridge** (the spatial article's `TransformBridge`) and **the a.e.-tail / antitone-density
toolkit** (`exists_antitone_density`, `tail_eq_of_ae_tail_eq`, `eqOn_of_ae_eq_of_antitoneOn`) stay
queued; **variation diminution under convolution** and the test-function uniqueness of finite
measures too. Each is article-independent and each has two consumers.

**Moved (2026-09-28): E-0009 slices 1–4** (`L1Operators`, `BochnerConvolution`,
`LaplaceUniqueness`, `TailInverse`) — the L¹ translation/convolution operators, convolution as a
Bochner integral, Laplace-transform uniqueness on `[0,1]`, and the generalised inverse of a
nonincreasing tail function, all byte-identical between Paper I and Paper V up to the causal/spatial
variable rename (`offices/engineer/notes/2026-09-19-lean-duplication-survey.md`). Reflection,
dilation, and anything quantifying over `IsSymmetric` or `IsFolded` stayed behind — spatial-only or
causal-only, per the test above. Paper V's own copies are unchanged here; re-pointing Paper V onto
these modules is a separate item.

**Moved (2026-09-11): the causal admissible cone as a shared type** (`CausalCone`, `CausalData`).
Its extraction is right and Paper V (the spatial article) uses it heavily, keeping the field layout
and names in `SpatialLine.CausalAdmissible`; the second consumer is still to come. Paper I's Lean
is a released artefact behind a DOI and stays frozen at its release — its `SelfDecomposableExponent`
and the trunk's `CausalAdmissible` are provenance, not dependency (Paper I requires `ScaleSpaceCore v0.1.1`
but imports none of its declarations).

## Bumping Mathlib

Nobody has done this yet. Every Lean member of the constellation sits on
`leanprover/lean4:v4.31.0` with `mathlib fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`
(`inputRev v4.31.0`), and this is the runbook for the first time that stops being true (E-0013,
proposed 2026-09-19, accepted 2026-09-30). It is a plan, not an attempt: nothing below has been
run, and the dry run of step one — bumping the trunk alone, without merging — is a separate,
later item, since it pulls a second ~7 GB Mathlib into the shared store.

**The twelve files.** Three per repository, across four repositories:

| Repository | Files |
|---|---|
| `scale-space-lean` (this repository) | `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` |
| `hemigroup-causal-scale-space-kernels` | `Formalization/lakefile.toml`, `Formalization/lean-toolchain`, `Formalization/lake-manifest.json` |
| `spatial-hemigroup-scale-space` | `Formalization/lakefile.toml`, `Formalization/lean-toolchain`, `Formalization/lake-manifest.json` |
| `scale-space-foundations` | `Formalization/lakefile.toml`, `Formalization/lean-toolchain`, `Formalization/lake-manifest.json` |

**The order.** Trunk first: bump `lean-toolchain` and the `mathlib` `rev` in `lakefile.toml` here,
build, then tag the new trunk release. Only then each article, in one commit per article that
bumps both its own `mathlib` rev and its `ScaleSpaceCore` rev together — an article pinned to the
old trunk tag with the new Mathlib (or vice versa) is exactly the half-bumped state the order
exists to avoid. `lake-manifest.json` is regenerated by the build in each case, not hand-edited;
it is the lockfile (seven of the ten packages it lists — `plausible`, `LeanSearchClient`,
`importGraph`, `proofwidgets`, `aesop`, `Qq`, `batteries` — carry `inputRev` `main`/`master` and
are held only by the SHA this file records, inherited from Mathlib's own lakefile; a `lake update`
outside a planned bump is what moves them and breaks reproducibility).

**Each consumer's current trunk tag, and what a bump does to it.**

- **`hemigroup-causal-scale-space-kernels` (Paper I) — `v0.1.1`, frozen.** Q-0182 (E-0011) answered
  (a): *"Paper I's Lean stays frozen at its release, the require is provenance, not dependency."*
  Its Lean is a released artefact behind a DOI; a trunk Mathlib bump does not touch it, and its
  `ScaleSpaceCore` requirement stays at `v0.1.1` whether or not the trunk ever reaches that tag
  again. It is named here for completeness, not as a step the bump performs.
- **`spatial-hemigroup-scale-space` (Paper V) — `v0.2.0`.** A bump moves its `mathlib` rev and
  re-points its `ScaleSpaceCore` requirement to whatever the trunk's post-bump tag is, in one
  commit, through the store sequence below. (Its `ScaleSpaceCore` pin is independently scheduled
  to move to `v0.3.0` first, for the unrelated E-0009 extraction — Q-0188, blocked on that tag —
  so a Mathlib bump run after that lands re-points from `v0.3.0`, not `v0.2.0`.)
- **`scale-space-foundations` (SSF) — `v0.1.0`.** Parked since 2026-08; the same move applies when
  it is next built, with one difference: `Formalization/.lake/packages` is currently evicted while
  the repository is parked, so the sequence below starts from `lake-store.py restore`, not
  `unlink` — there is no junction yet to unlink.

**The store.** `lake-store.py`'s module docstring: Mathlib's prebuilt oleans are *"about 7 GB per
project, identical across every project that pins the same revisions"*, shared by Windows
directory junctions into `dev/.lake-store/<pkg>-<rev>` rather than duplicated per project. It
keys entries by package **and** revision, so bumping Mathlib does not replace the old store entry
— it adds a **second** one, and the two coexist (roughly 14 GB) until every project has moved off
the old revision. Per project, the sequence is `unlink`, bump the pin, build, `link` — never
`lake update` in a linked project, which the hub's `CLAUDE.md` states as a standing rule:

> Never `lake update` or `lake clean` in a linked project; `unlink` (or `wt-remove`) before
> deleting a checkout or removing a worktree, since a recursive delete follows the junctions and
> empties the store.

The same rule, from `lake-store.py`'s own docstring:

> Rules the store relies on (also in the hub's CLAUDE.md):
>   * never `lake update` in a linked project — a pin bump is a new store entry, then `link` again;
>   * never `lake clean` in a linked project — it cleans through the junctions;
>   * `unlink` before removing a checkout or worktree; `git worktree remove --force` follows junctions.

Only after the last of the four Lean roots has relinked onto the new Mathlib revision does
`lake-store.py gc` run, to delete the now-unreferenced old entry. Running it earlier would evict a
project — Paper I, frozen, or SSF, parked and possibly not rebuilt for a while — still linked to
the old revision.

**A fifth thing this surfaces, not a step it performs.** `scale-space-foundations`'s three
GitHub Actions workflows (`docs.yml`, `lean.yml`, `manifest.yml`) still call
`danielfagerstrom/article-kit/.github/workflows/<name>.yml@main`, unlike Paper I and Paper V,
which pin the same workflows at `@v0.1.0` (E-0003, delivered). A Mathlib bump run while SSF still
tracks `article-kit` at `main` risks its Lean CI changing underneath the bump, from an unrelated
`article-kit` change landing on `main` the same week — the risk E-0013 named, not yet closed by
anything in this runbook.

## License

Copyright (c) 2026 Daniel Fagerström.

Released under the Apache License, Version 2.0 — see [LICENSE](LICENSE). This matches the Mathlib
convention, so the library composes with the rest of the Lean mathematical library ecosystem
without a licence mismatch.
