# Changelog

All notable changes to this repository are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/); versions correspond to Lean release tags.

## [Unreleased]

### Changed

- `README.md` and a new `CLAUDE.md` describe this repository as the programme's **shared library**
  under ADR-0026 (hub, supersedes ADR-0021): admission by second demand, programme vocabulary
  allowed, no axioms (a cited interface becomes a hypothesis, discharged by the consuming article),
  and a one-way dependency onto the new (not yet created) Mathlib-quality library,
  `harmonic-semigroups`. No Lean change; the stale `rev = "v0.1.0"` in the README's `lakefile.toml`
  example is corrected to `v0.2.0`.

### Added

- `ScaleSpaceCore.SDProfile`, `ScaleSpaceCore.SDProfileCone`: **the line's admissible cone as a
  shared type** — the line analogue of `CausalAdmissible`'s move in `v0.2.0`. `SDProfile`
  (Gaussian coefficient `a`, folded profile `k`, `k_antitone`, `k_zero`, two finiteness fields)
  with `exponentL`, `exponent`, `profileMeasure`, `levyMeasure`, `IsAdmissibleExponent`;
  `admissible_cone` (sums and nonnegative multiples), `exponent_neg`, `exponent_zero`,
  `continuous_exponent`; and what these rest on: `IsFolded`, `SymLevyPair` with
  `quadratic_growth`, `profile_integrability` and `profile_integrability_pair`.
- `ScaleSpaceCore.BrownianDensity`: `brownianLaw`, `brownianDensity` and the facts the bridge
  reads; `fourierCos` with `fourierCos_eq_charFun_re` and `fourierCos_gaussianReal`.
- `ScaleSpaceCore.BridgeExponents`: `bridge_exponents (F : CausalAdmissible) : ∃ Q : SDProfile,
  Q.a = F.b₀ / 2 ∧ … ∧ ∀ ω, Q.exponent ω = F.exponent (ω ^ 2 / 2)`, the map from the causal cone
  into the line's, now a theorem between two trunk structures.
- `ScaleSpaceCore.Cin`, `ScaleSpaceCore.CinRays`: `cin`, `cinProfile`, `cin_elementary`,
  `cin_expansion_zero`, `cin_expansion_top`, and the ray `cin_ray`.

These six modules are SSL-2 of the spatial-affine article's second-demand report (hub
`spatial-hemigroup-affine/records/formalization/SECOND-DEMAND.md`, rows V3, B2, B4): that article
states its class `𝒜_d` in `SDProfile`, which is case (c), so the structure moved with the
declarations stated in it. They are moved from Paper V's cone export (`cone-v0.1`, commit
`f28c066e`, namespace `SpatialLine`) with statements unchanged up to the namespace, and brought
only Lean-core dependencies; `AxiomCheck.lean` prints only `propext`, `Classical.choice`,
`Quot.sound` for every one of them. `IsSelfDecomposable` (SSL-3), `profile_integrability_mem`
(spends Paper V's ledger A3), `bridge_exponents_mixture` and the Brownian mixture facts (SSL-8),
and `cin_superposition` with `HasProfileTail` stayed behind. No article repository is edited;
re-pointing Paper V and Paper VII onto these modules is later work. No tag is cut here.

- `ScaleSpaceCore.L1Operators`: `X = L¹(ℝ)`, translation (`transL1`), convolution by a measure
  (`mconv`, `mconvL1`) and what the operator does — translation covariance, positivity, mass,
  composition — plus the bounded-test-function pairing lemma `integral_mul_mconv`.
- `ScaleSpaceCore.BochnerConvolution`: convolution as an `X`-valued Bochner integral (`bconv`,
  `bconvM`), `Φ (f * g) = f * (Φ g)` (`map_bconv`), `bconv` identified with the classical
  pointwise convolution (`coeFn_bconv`), the Bochner form of `mconvL1` (`bconvM_eq_mconvL1`), and
  pairing against a bounded functional (`pairTrans`, `apply_mconvL1`).
- `ScaleSpaceCore.LaplaceUniqueness`: two finite measures on `[0,1]` with the same moments are
  equal (`ext_of_moments`), via the substitution `x = e^{-t}` (`expNeg`) and Stone–Weierstrass.
- `ScaleSpaceCore.TailInverse`: the generalised inverse of a nonincreasing tail function
  (`tailInv`) and its order lemmas.

These four modules are slices 1–4 of proposal E-0009 (hub `proposals/E-0009.md`): 73
declarations were byte-identical between the causal and spatial articles up to the `t,r → x,y`
variable rename
(hub `offices/engineer/notes/2026-09-19-lean-duplication-survey.md`), and slices 1–4 cover the
bulk of that duplication. Every moved declaration is Mathlib-only; `AxiomCheck.lean` prints only
the three Lean-core axioms (`propext`, `Classical.choice`, `Quot.sound`) for each. Reflection,
dilation, and anything quantifying over an article's own predicate (`IsSymmetric`, `IsFolded`)
stayed behind, named in the pull request. Slice 5 (the approximate identity) is deferred: it
states a new lemma rather than moving one, per the proposal.

No article repository is edited by this change; re-pointing Paper V onto these modules is a
separate item (Q-0188). No tag is cut here — the release is the author's, after merge.

## [0.2.0]

- `PowerSumSymmetry`: vanishing odd power sums and the halving identity.
- `PolyaFrequencyClass`: Karlin's bilateral Laplace transform and the class `E₂*`.
- `CausalCone`, `CausalData`: the causal admissible cone as a shared type
  (`CausalAdmissible`), and its three generators (drift, Gamma, stable).

## [0.1.1]

- Release-readiness only (Apache 2.0 license, public README); no module changes.

## [0.1.0]

- Initial modules: `Wedge`, `ReceptiveField`, `BoostBracket`, `BoostBracketConcrete`.
