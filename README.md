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
admissible cone and the line's admissible cone with the bridge between them, the `Cin` rays,
the L¹ / Bochner-convolution / Laplace-uniqueness infrastructure the causal and spatial articles
share, and the line's reflection-symmetric cascade-family vocabulary with its kernel constructor,
which the spatial articles share. It is its own Lake package because each article in this line publishes
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
| `L1Operators` | `X = L¹(ℝ)`, translation (`transL1`), reflection (`reflL1`), mass-preserving dilation (`dilate`, `dilL1`) and convolution by a measure (`mconv`, `mconvL1`) with what the operator does — translation covariance, positivity, mass, composition — and the pairing lemma `integral_mul_mconv` |
| `BochnerConvolution` | convolution as an `X`-valued Bochner integral (`bconv`, `bconvM`), `Φ (f * g) = f * (Φ g)` (`map_bconv`), `bconv` as the classical pointwise convolution (`coeFn_bconv`), the Bochner form of `mconvL1` (`bconvM_eq_mconvL1`), and pairing against a bounded functional (`pairTrans`, `apply_mconvL1`) |
| `LaplaceUniqueness` | two finite measures on `[0,1]` with the same moments are equal (`ext_of_moments`), via the substitution `x = e^{-t}` (`expNeg`) and Stone–Weierstrass |
| `TailInverse` | the generalised inverse of a nonincreasing tail function (`tailInv`) and its order lemmas, the core of the Choquet-measure construction both articles' cone modules use |
| `Transform` | symmetric measures on the line (`IsSymmetric`), the cosine transform (`fourierCos`) and the exponent `-log ∘ fourierCos` (`exponent`); the bridge to Mathlib's `charFun` (`fourierCos_eq_charFun_re`, `charFun_eq_fourierCos_of_symmetric`) |
| `L1OperatorsSpace` | the operators of `L1Operators` on `L¹(E)`, `E` a finite-dimensional real normed space with an additive Haar measure as `volume` (`EuclideanSpace ℝ (Fin d)` and `ℝ` are instances), under the suffix `E`: translation (`transL1E`), reflection (`reflL1E`), the linear dilation `D_A f = \|det A\|⁻¹ f(A⁻¹ ·)` for `A : E ≃L[ℝ] E` (`dilL1E`, an isometry with `D_A D_B = D_{AB}`, inverse `D_{A⁻¹}`, `D_A T_a = T_{Aa} D_A`; the isotropic case `homothety`, rotations at `\|det Q\| = 1`), convolution by a finite measure (`mconvE`, `mconvL1E`) with translation covariance, positivity, mass, contraction, composition and `δ₀`; transport `D_A (μ * f) = (A_* μ) * D_A f` (`dilL1E_comp_mconvL1E`); the relational bridges (`eq_transL1E_iff`, `eq_dilL1E_iff`, `eq_mconvL1E_iff`, `intertwines_iff_dilL1E`, `translation_iff_transL1E`); and the `d = 1` recoveries `transL1E_real`, `reflL1E_real`, `dilL1E_homothety_real`, `mconvL1E_real` |
| `L1OperatorsEuclidean` | the matrix dilation on `L¹(ℝ^d)` in Paper VII's terms: `matEquiv A` for an invertible matrix (acting by `Matrix.toEuclideanCLM`, inverse `toEuclideanCLM A⁻¹`, determinant `A.det`), `coeFn_dilL1E_matEquiv`, `intertwines_iff_dilL1E_matEquiv`, `D_A D_B = D_{AB}`, rotations by orthogonal `Q`, and `λ • 1` as the homothety |
| `BochnerConvolutionSpace` | `BochnerConvolution` on `L¹(E)`: `continuous_transL1E`, `bconvE` with the interchange identity `Φ (f * g) = f * Φ g` (`map_bconvE`) and `coeFn_bconvE`, the Bochner form `μ * f = ∫ T_y f dμ` (`bconvME_eq_mconvL1E`), pairing against a bounded functional (`pairTransE`, `apply_mconvL1E`, `apply_bconvE`), and the kernel of the identity is `δ₀` (`eq_dirac_of_mconvL1E_eq_id`) |
| `L1ContinuitySpace`, `FourierPairingSpace` | on `L¹(E)`: the modulus of continuity `transDiffE`, the estimate (★) `‖μ * f - f‖₁ ≤ ∫ ‖T_y f - f‖₁ dμ` (`norm_mconvL1E_sub_le`) and its Lévy clause; over an inner product space, the character pairing `charCLME` with `(μ * f)^ = μ̂ f̂` (`charCLME_mconvL1E`, Mathlib's `charFun` sign `e^{i⟨x,ω⟩}`) |
| `Transport` | convolution against reflection and dilation — a symmetric kernel commutes with `reflL1` (`mconvL1_reflL1`), dilation intertwines with the dilated kernel (`dilL1_comp_mconvL1`) — and the kernel of the identity is `δ₀` (`eq_dirac_of_mconvL1_eq_id`) |
| `Family` | the reflection-symmetric cascade family on `L¹(ℝ)`: `PreCascadeCore` ((A1)–(A3), (A5)–(A7)), `CascadeCore` (+ (A4) `IsPositive`, (ND) `IsNondegenerate`), `IsScaleCovariant` ((A8) relative to a set of ratios), `CascadeFamily`, and the kernel-family hypotheses `IsKernelFamily`, `IsSymmetricKernelFamily` |
| `L1Continuity` | the modulus of continuity of translation (`transDiff`), the estimate `‖μ * f - f‖₁ ≤ ∫ ‖T_y f - f‖₁ dμ` (`norm_mconvL1_sub_le`), and Lévy's continuity theorem in the form (A7) consumes |
| `Construction` | `CascadeData`, the kernel-level constructor: symmetric probability kernels with the cascade law and a transform continuous in the scales give a `PreCascadeCore` (`preCore`, with (A7) as `continuousOn_mconvL1`), positivity, a kernel family, and — under one hypothesis each — `cascadeCore` and `isScaleCovariant` |
| `SDProfile`, `SDProfileCone` | the line's admissible cone: `SDProfile` (Gaussian coefficient `a ≥ 0`, nonincreasing folded profile `k ≥ 0`) with `exponentL`, `exponent`, `profileMeasure`, `levyMeasure` and `IsAdmissibleExponent`; the folding predicate `IsFolded` and the symmetric Lévy pair `SymLevyPair` with its quadratic growth bound; `profile_integrability` and `profile_integrability_pair`; sums and multiples (`admissible_cone`), evenness, `exponent_zero` and `continuous_exponent` |
| `BrownianDensity` | the Brownian laws `brownianLaw`, `brownianDensity` and the elementary bounds and Gaussian jump integral the bridge reads; the cosine transform's value at a centred Gaussian (`fourierCos_gaussianReal`; `fourierCos` itself is `Transform`'s) |
| `BridgeExponents` | `bridge_exponents`: every `CausalAdmissible` maps to an `SDProfile` with coefficient `b₀/2`, folded profile `2x∫g_u(x)k(u)du/u` and exponent `F(ω²/2)` (`CausalAdmissible.bridgeDatum`) |
| `Cin`, `CinRays` | `Cin(z) = ∫₀^z (1 - cos v)dv/v` with `cin_elementary` (even, nondecreasing on `[0,∞)`, `≤ z²/4`) and the expansions `cin_expansion_zero`, `cin_expansion_top`; the unit-step profile `cinProfile τ` and the ray `cin_ray` (exponent `Cin(τ·)`) |
| `SelfDecomposable` | self-decomposability `μ = (c •)_* μ ∗ ρ_c` (`IsSelfDecomposable`) and operator self-decomposability `μ = (e^{-tB})_* μ ∗ ρ_t` (`IsBSelfDecomposable`, the scalar case at `B = 1`) on a real vector space; the transform form on a finite-dimensional inner product space (`isSelfDecomposable_iff_charFun`), the line's `b > 1` form (`isSelfDecomposable_real_iff`), images under linear maps, and a transform without zeros (`IsSelfDecomposable.charFun_ne_zero`). A candidate for promotion to `harmonic-semigroups` |
| `GaussianKernel` | the multivariate Gaussian kernel `u ↦ N(0, uI_d)` is measurable (`measurable_multivariateGaussian_zero_smul_one`), through `CFC.sqrt (u • 1) = √u • 1` for every real `u` (`sqrt_smul_one_eq`) and `N(0, uI_d)` as the image of the standard Gaussian under `x ↦ √u • x` (`multivariateGaussian_zero_smul_one`) |
| `DilationInvariance` | a function continuous at the origin, where it vanishes, and fixed by one dilation vanishes identically (`dilation_invariance`) |
| `LineInterfaces` | the three cited clauses the line classification rests on, as `Prop`s to be taken as hypotheses: `SymLevyUnique` (Sato Thm. 8.1(ii)), `SymLevyConverse` (Sato Thm. 8.1(iii)), `BochnerSymm` (Sato Prop. 2.5), the last two bundled as `LineLawInterfaces` |
| `MainAnalysis`, `MainConstruction` | **the line classification** ([V, Thm. 7.3]), stated conditionally: `main_analysis`, `main_analysis_exists` (a family satisfying (A1)–(A8) and (ND) is a convolution cascade in a normalised gauge with an `SDProfile` exponent; hypothesis `SymLevyUnique`), `main_uniqueness` (no hypothesis), `main_construction` (the converse; hypothesis `LineLawInterfaces`) |
| `Exponent`, `SDExponents`, `DilationDecrease`, `AntitoneDensity`, `AnalysisDirection` | `IsPositiveDefinite`, `IsSymNegDef`, `IsSymLevyExponent`; `lem:selfdecomposable-exponents` in both directions — the dilation increments of a profile exponent are Lévy exponents (`sd_increment_isSymLevyExponent`), and conversely (`sd_exponents_one_implies_three`, through `D_c ν ≤ ν` and the antitone density of a translation-decreasing measure) |
| `TransformBridge`, `TransformUniqueness`, `Representation`, `Nonvanishing`, `Pairing`, `Cascade`, `Additivity`, `Transmittance`, `Covariance`, `DilationAtom`, `Rigidity`, `Gauge`, `GaugeLevy` | what the necessity direction reads: the convolution representation of a family (`representation_existsUnique`, with the character pairing appended to `BochnerConvolution`), nonvanishing of the transform, the kernel family (`exists_kernelFamily`, `kernel_symmetric`), additivity of the exponent, covariance and action rigidity, and the canonical gauge (`canonical_gauge`) |
| `Truncation`, `NullArray`, `Tightness`, `LevyExtraction`, `Increments` | every increment exponent of a cascade is a symmetric Lévy exponent (`increments_levy`), by a null array, tightness and Lévy-measure extraction |
| `GammaMeasure` | four facts about Mathlib's `gammaMeasure`: integration against it is integration against its density on `(0,∞)` (`lintegral_gammaMeasure`); its Laplace transform against `u^q e^{-su}` (`lintegral_gammaMeasure_rpow_mul_exp`); and that it lives on the positive axis (`gammaMeasure_Iio_zero`, `ae_pos_gammaMeasure`) |

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

Where a result needs a cited interface, the interface is a **hypothesis** of the statement
instead (ADR-0026 § 5), stated as a `Prop` the consuming article discharges from its own ledger.
`LineInterfaces` is the worked example: `main_analysis` takes `hA3 : SymLevyUnique`, which Paper V
discharges with its axiom `fourier_toolbox_levy_unique` and Paper VII from its own A3 at `d = 1`.
`#print axioms` on the conditional theorem is still Lean core.

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
bridge** (the spatial article's `TransformBridge`; its `charFun` identities moved 2026-10-05 into
`Transform`, and `fourierCos_gaussianReal` with `BrownianDensity`; the symmetric-measure half and
the rest stay queued) and **the a.e.-tail / antitone-density
toolkit** (`exists_antitone_density`, `tail_eq_of_ae_tail_eq`, `eqOn_of_ae_eq_of_antitoneOn`) stay
queued; **variation diminution under convolution** and the test-function uniqueness of finite
measures too. Each is article-independent and each has two consumers.

**Moved (2026-10-05): `dilation_invariance`** (`DilationInvariance`) — a function continuous at the
origin, where it vanishes, and fixed by one dilation vanishes identically, from Paper V's
`SpatialLine/Dilation.lean` (the public cone export, tag `v0.1`). Second demand: Paper V's
classification's uniqueness clause, and Paper VII's `thm:isotropic-classification`,
`prop:isotropic-corner`, `prop:similarity-ray-families`(3) and `prop:diagonal-ray-families`(5)
(`spatial-hemigroup-affine/records/formalization/SECOND-DEMAND.md` § 3 row V8; § 6, SSL-4). The
statement mentions only Mathlib types; `dilation_atom`, the file's other lemma (about the dilation
of measures along a sequence), stayed behind — its proof is not needed here and it is not itself
second demand. Paper V's own copy is unchanged; re-pointing Paper V and Paper VII onto this module
is a separate item.

**Moved (2026-09-28): E-0009 slices 1–4** (`L1Operators`, `BochnerConvolution`,
`LaplaceUniqueness`, `TailInverse`) — the L¹ translation/convolution operators, convolution as a
Bochner integral, Laplace-transform uniqueness on `[0,1]`, and the generalised inverse of a
nonincreasing tail function, all byte-identical between Paper I and Paper V up to the causal/spatial
variable rename (`offices/engineer/notes/2026-09-19-lean-duplication-survey.md`). Reflection,
dilation, and anything quantifying over `IsSymmetric` or `IsFolded` stayed behind — spatial-only or
causal-only, per the test above. Paper V's own copies are unchanged here; re-pointing Paper V onto
these modules is a separate item.

**Moved (2026-10-05): the line's cascade-family vocabulary and its kernel constructor**
(`Transform`, `Transport`, `Family`, `L1Continuity`, `Construction`, and reflection and dilation in
`L1Operators`), from Paper V at `v0.1`, statements verbatim up to the namespace. This overrides the
2026-09-28 judgement that reflection and dilation are spatial-specific: a second spatial module
(Paper VII, `spatial-hemigroup-affine`) constructs a `CascadeCore` from the marginals of an
isotropic family and states its hypotheses in the vocabulary, so the structures themselves are
second demand and move with the declarations stated in them — the case `CausalAdmissible` moved
under. The representation lemma that produces a kernel family (`exists_kernelFamily`) has not
moved; the admissible cone on the line moved the same day (below).

**Moved (2026-10-05): the line's admissible cone as a shared type** (`SDProfile`, `SDProfileCone`,
`BrownianDensity`, `BridgeExponents`, `Cin`, `CinRays`), the line analogue of the causal cone's
move below. The spatial-affine article states its class `𝒜_d` in `SDProfile` (its second demand,
hub `spatial-hemigroup-affine/records/formalization/SECOND-DEMAND.md`, SSL-2), so the structure
moved from Paper V's cone export (`cone-v0.1`) with the declarations stated in it:
`bridge_exponents`, now a theorem between two trunk structures, and the `Cin` rays. It brought
the Lean-core dependencies its proofs read — `IsFolded`, `SymLevyPair` and its growth bound, the
Lean-core half of `lem:profile-integrability`, the Brownian density, and the part of the transform
bridge that computes `fourierCos` at a Gaussian (`fourierCos` itself came with the cascade
vocabulary, above: the two moves carried identical copies, and this one now imports it). `IsSelfDecomposable` (SSL-3),
`bridge_exponents_mixture` and the Gaussian mixtures (SSL-8), and the Choquet superposition of
`lem:cin-rays`(2) stayed behind. Paper V's own copies are unchanged here.

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
