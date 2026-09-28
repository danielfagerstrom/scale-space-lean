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
