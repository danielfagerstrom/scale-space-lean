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
- `README.md` gains a "Bumping Mathlib" section (E-0013): the twelve files across the four Lean
  repositories, the trunk-first order, each consumer's current trunk tag and what a bump does to
  it, Paper I's frozen position (Q-0182), and the `lake-store.py` sequence. Documentation only; no
  Mathlib bump is performed.

### Added

- `ScaleSpaceCore.SDProfile`, `ScaleSpaceCore.SDProfileCone`: **the line's admissible cone as a
  shared type** — the line analogue of `CausalAdmissible`'s move in `v0.2.0`. `SDProfile`
  (Gaussian coefficient `a`, folded profile `k`, `k_antitone`, `k_zero`, two finiteness fields)
  with `exponentL`, `exponent`, `profileMeasure`, `levyMeasure`, `IsAdmissibleExponent`;
  `admissible_cone` (sums and nonnegative multiples), `exponent_neg`, `exponent_zero`,
  `continuous_exponent`; and what these rest on: `IsFolded`, `SymLevyPair` with
  `quadratic_growth`, `profile_integrability` and `profile_integrability_pair`.
- `ScaleSpaceCore.BrownianDensity`: `brownianLaw`, `brownianDensity` and the facts the bridge
  reads, and `fourierCos_gaussianReal`. (`fourierCos`, `fourierCos_apply`,
  `integrable_charFun_integrand` and `fourierCos_eq_charFun_re` came with this move too, but the
  cascade-vocabulary move (Q-0301), merged first, had carried identical copies into `Transform`;
  at the merge `BrownianDensity` dropped its copies and imports `Transform`.)
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

- `ScaleSpaceCore.L1Operators` gains reflection (`reflₗ`, `reflL1`, `coeFn_reflL1`, with
  `measurePreserving_neg'`, `reflect_congr_ae`, `integrable_reflect`) and mass-preserving dilation
  (`dilate`, `dilₗ`, `dilL1`, `coeFn_dilL1`, with `quasiMeasurePreserving_const_mul`,
  `dilate_congr_ae`, `integrable_dilate`, `lintegral_comp_const_mul`).
- `ScaleSpaceCore.Transform`: `IsSymmetric`, `fourierCos`, `exponent` (`-log ∘ fourierCos`), and
  the bridge to Mathlib's `charFun` (`fourierCos_dirac_zero`, `integrable_charFun_integrand`,
  `fourierCos_eq_charFun_re`, `charFun_eq_fourierCos_of_symmetric`).
- `ScaleSpaceCore.Transport`: `mconv_reflect`, `mconvL1_reflL1`, `dilate_mconv`,
  `dilL1_comp_mconvL1`, `eq_dirac_of_mconvL1_eq_id`, `norm_sub_eq_lintegral`.
- `ScaleSpaceCore.Family`: `PreCascadeCore`, `IsPositive`, `IsNondegenerate`, `CascadeCore`,
  `IsScaleCovariant` (with `IsScaleCovariant.S_zero`, `IsScaleCovariant.S_pos`), `CascadeFamily`,
  `IsKernelFamily`, `IsSymmetricKernelFamily`.
- `ScaleSpaceCore.L1Continuity`: the modulus of continuity of translation (`transDiff`, its
  bounded-continuous form `transDiffBCF`), the estimate `norm_mconvL1_sub_le` and its consequences,
  and `levy_continuity`, which its proof calls.
- `ScaleSpaceCore.Construction`: `CascadeData` with `preCore`, `isPositive`, `isKernelFamily`,
  `isNondegenerate`, `cascadeCore`, `isScaleCovariant`, and the (A7) proof
  `continuousOn_mconvL1`.

These are the line's cascade-family vocabulary and its kernel constructor (Q-0301; Paper VII's
second-demand report, `spatial-hemigroup-affine/records/formalization/SECOND-DEMAND.md`, item
SSL-1), moved from Paper V's `SpatialLine` modules `Basic`, `ConvolutionOperator`, `Transform`,
`TransformBridge`, `Transport`, `Family`, `Covariance`, `L1Continuity`, `TransformUniqueness` and
`Construction` at the cone export's `v0.1` (`f28c066e`). Every statement and proof is identical to
Paper V's up to the namespace; where `main` already had a declaration (`X`, `transL1`, `mconv`,
`mconvL1` and the rest of `L1Operators`, `continuous_transL1`) it is reused, not duplicated.

**This overrides Q-0187's judgement.** Q-0187 left reflection, dilation and anything quantifying
over an article's own predicate behind as spatial-specific. A second spatial module now needs
them: Paper VII's `lem:isotropic-marginal-family` constructs a `CascadeCore` from the marginals of
an isotropic family, and `thm:isotropic-classification` and `prop:isotropic-corner` state their
hypotheses in this vocabulary. The structures themselves are used by two modules, so case (c) of
the second-demand test applies (hub `RELEASES.md` § "Dependencies between modules"): the
structure moves with the declarations stated in it, as `CausalAdmissible` did in `v0.2.0`.

Every moved declaration is Mathlib-only and Lean core: `AxiomCheck.lean` prints only `propext`,
`Classical.choice`, `Quot.sound` for each, including `CascadeData.cascadeCore`,
`CascadeData.isScaleCovariant` and `eq_dirac_of_mconvL1_eq_id`. No interface of Paper V's was
needed, so no statement gained a hypothesis.

Stayed behind in Paper V: `exists_kernelFamily` (it needs the representation lemma, about 1,900
lines; it follows on its own demand); `SDProfile` and everything stated in it (SSL-2); the line
classification (SSL-6); `representation_converse`, the rest of `Covariance`
(`covariance_fourier`, `covariance_similarity` and their lemmas, whose proofs call Paper V's
`kernel_transform_pos` and `eq_of_mconv_gaussTest_ae`), `IsFolded`, `laplaceL`, `fourier_uniqueness`, and the
rest of `TransformBridge` — none has a second demand yet. Paper V and Paper VII are not edited;
they keep using the `require`d `SpatialHemigroup` declarations until a later re-pointing item. No
tag is cut here.

## [0.2.0]

- `PowerSumSymmetry`: vanishing odd power sums and the halving identity.
- `PolyaFrequencyClass`: Karlin's bilateral Laplace transform and the class `E₂*`.
- `CausalCone`, `CausalData`: the causal admissible cone as a shared type
  (`CausalAdmissible`), and its three generators (drift, Gamma, stable).

## [0.1.1]

- Release-readiness only (Apache 2.0 license, public README); no module changes.

## [0.1.0]

- Initial modules: `Wedge`, `ReceptiveField`, `BoostBracket`, `BoostBracketConcrete`.
