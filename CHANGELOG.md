# Changelog

All notable changes to this repository are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/); versions correspond to Lean release tags.

## [Unreleased]

### Added

- `ScaleSpaceCore.GammaMeasure` (Q-0362): four facts about Mathlib's `gammaMeasure` —
  `lintegral_gammaMeasure` (integration against it is integration against its density on
  `(0,∞)`), `lintegral_gammaMeasure_rpow_mul_exp` (its Laplace transform against `u^q e^{-su}`,
  the one computation both second-demand consumers' proofs need), `gammaMeasure_Iio_zero` and
  `ae_pos_gammaMeasure` (it lives on the positive axis). Moved from Paper V's cone export
  (`cone-v0.1`, `f28c066e`, `SpatialLine.MaternMixture`), statements unchanged up to the
  namespace. Second demand: Paper V's `matern_gamma_mixture` and Paper VII's
  `lintegral_exp_gammaMeasure`/`ae_nonneg_gammaMeasure`
  (`Formalization/AffineHemigroup/MaternOrbit.lean`), the case `q = 0`, `r = 1`
  (`records/formalization/SECOND-DEMAND-candidates.md` § A3). Every declaration is Mathlib-only;
  `AxiomCheck.lean` prints only `propext`, `Classical.choice`, `Quot.sound`. Neither article is
  edited; Paper VII's switch to a one-line corollary is a later item. No tag is cut here.
- **The Laplace transform on the half-line and its uniqueness** (Q-0360; candidate A1 of
  `spatial-hemigroup-affine`'s `records/formalization/SECOND-DEMAND-candidates.md`). Moved from
  Paper V's package at the cone export's `v0.1`, statements verbatim up to the namespace:
  `laplaceL` and `laplaceL_apply` from `SpatialLine.Transform` into
  `ScaleSpaceCore.Transform`; `integral_exp_neg_eq_toReal_laplaceL`, `expNeg_mem_Icc`,
  `map_expNeg_compl_Icc`, `isFiniteMeasure_map_expNeg`, `integral_pow_map_expNeg`,
  `laplaceL_injective_of_isFiniteMeasure`, `laplaceL_withDensity_expNeg`,
  `laplaceL_injective_of_ne_top` and `laplace_uniqueness_locally_finite` from
  `SpatialLine.LaplaceUniqueness` into `ScaleSpaceCore.LaplaceUniqueness`, beside `expNeg` and
  `ext_of_moments` (which E-0009 moved). Second demand: Paper V (`Thorin`, `StableThorin`,
  `ScaleMonotone`, `ThorinBridge`) and Paper VII (`lem:bernstein-triplet-unique`). E-0009 left them
  behind because `IsFolded` was spatial-only; it has been in `SDProfile` since Q-0302.
  `LaplaceUniqueness` now imports `Transform` and `SDProfile`. Paper I's twin `Hemigroup.laplaceL`
  stays (Paper I is frozen, Q-0182); Paper V and Paper VII are not edited. All eleven print only
  Lean core (`AxiomCheck.lean`).

## [0.3.0] — 2026-10-07

The shared library under ADR-0026, with the second-demand moves of Paper V and Paper VII:
- the line's classification, stated conditionally (SSL-6);
- the line's toolbox (SSL-1 to SSL-4, Q-0187);
- the `L¹` operators in dimension `d` (SSL-5, Q-0332).

Tagged by the author's decision of 2026-10-07, so that Paper VII can require SSL-5. Every
declaration prints only `propext`, `Classical.choice` and `Quot.sound` (`AxiomCheck.lean`).

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

- **The `L¹` operators in dimension `d`** (Q-0332; SSL-5 of `spatial-hemigroup-affine`'s
  `records/formalization/SECOND-DEMAND.md`, row V10). This is a **generalization written in the
  trunk, not an extraction**: Q-0187 moved the line's `L1Operators`/`BochnerConvolution` in on two
  articles' demand, and the `d`-dimensional layer existed nowhere; the author decided on
  2026-10-05 (Q-0281) that the trunk writes the general form first and Paper VII proves its
  operator nodes (`lem:operators-to-kernels`, `lem:glplus-operator-families`,
  `prop:glplus-families`) against a trunk tag. The setting is a finite-dimensional real normed
  space `E` with `[MeasureSpace E] [BorelSpace E] [IsAddHaarMeasure (volume : Measure E)]`, so
  `EuclideanSpace ℝ (Fin d)` and `ℝ` are instances; the general names carry an `E` suffix.
  - `ScaleSpaceCore.L1OperatorsSpace`: `transL1E`, `reflL1E`, the linear dilation
    `dilL1E A` (`D_A f = |det A|⁻¹ f(A⁻¹ ·)`, `A : E ≃L[ℝ] E`) with `norm_dilL1E`, `dilL1E_comp`
    (`D_A D_B = D_{AB}`), `dilL1E_symm_comp`/`dilL1E_comp_symm`, `dilL1EEquiv`,
    `dilL1E_comp_transL1E` (`D_A T_a = T_{Aa} D_A`), the isotropic case (`homothety`,
    `coeFn_dilL1E_homothety`, `λ^{-d} f(·/λ)`) and rotations (`coeFn_dilL1E_of_abs_det_eq_one`);
    `mconvE`/`mconvL1E` with `mconvL1E_transL1E`, `isNonnegE_mconvL1E`, `integral_mconvL1E`,
    `norm_mconvL1E_le`, `mconvL1E_comp`, `mconvL1E_dirac_zero`; transport
    `dilL1E_comp_mconvL1E` (`D_A (μ * f) = (A_* μ) * D_A f`) and its "if" corollary
    `dilL1E_conj_mconvL1E`; the relational bridges `eq_transL1E_iff`, `eq_dilL1E_iff`,
    `eq_mconvL1E_iff`, `intertwines_iff_dilL1E`, `translation_iff_transL1E`; and the `d = 1`
    recoveries `transL1E_real`, `reflL1E_real`, `dilL1E_homothety_real` (with
    `dilateE_homothety_real`: `dilate`'s `lam⁻¹ f(lam⁻¹ x)` is `|det A|⁻¹ f(A⁻¹ x)` at `A = lam`),
    `mconvL1E_real`, `mconvE_real`, `isNonnegE_real`.
  - `ScaleSpaceCore.L1OperatorsEuclidean`: the matrix form Paper VII reads — `matEquiv A` acting
    by `Matrix.toEuclideanCLM`, `det_matEquiv`, `coeFn_dilL1E_matEquiv`, `eq_dilL1E_matEquiv_iff`,
    `intertwines_iff_dilL1E_matEquiv`, `dilL1E_matEquiv_comp`, `coeFn_dilL1E_matEquiv_orthogonal`,
    `matEquiv_smul_one`.
  - `ScaleSpaceCore.BochnerConvolutionSpace`: `continuous_transL1E`, `bconvE`, `map_bconvE`
    (`Φ (f * g) = f * Φ g`), `coeFn_bconvE`, `bconvME_eq_mconvL1E` (`μ * f = ∫ T_y f dμ`),
    `apply_mconvL1E_general`, `pairTransE`, `apply_mconvL1E`, `apply_bconvE`,
    `eq_dirac_of_mconvL1E_eq_id`, and `bconvE_real`, `bconvME_real`.
  - `ScaleSpaceCore.L1ContinuitySpace` (stretch): `transDiffE`, `transDiffBCFE`, (★)
    `norm_mconvL1E_sub_le`, `transDiffE_mconvL1E_le`, `norm_mconvL1E_comp_sub_le`, the Lévy clause
    `tendsto_norm_mconvL1E_sub_of_tendsto_charFun` over an inner product space, `transDiffE_real`.
  - `ScaleSpaceCore.FourierPairingSpace` (stretch): `charCLME`, `charCLME_transL1E`,
    `charCLME_mconvL1E` (`(μ * f)^ = μ̂ f̂`, Mathlib's `charFun` convention).

  Every ℝ declaration keeps its name and statement; the line's cascade vocabulary (`Family`,
  `Construction`, `L1Continuity`, `Transform`) stays on the line. Not here: a zero-free test
  function in dimension `d` and the injectivity of `μ ↦ μ * ·`, and the representation theorem
  (Paper VII's `lem:operators-to-kernels`(1)). `AxiomCheck.lean` gains a line for each new public
  declaration and prints only `propext`, `Classical.choice`, `Quot.sound` for all of them. No tag
  is cut here.
- `ScaleSpaceCore.GaussianKernel` (Q-0306): `measurable_multivariateGaussian_zero_smul_one`,
  `Measurable fun u : ℝ => multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (u • 1)`, Paper
  VII's `measurable_gaussVar` in Mathlib's types (the line is the case `d = 1`); with
  `sqrt_smul_one_eq` (`CFC.sqrt (u • 1) = √u • 1`, every real `u`) and
  `multivariateGaussian_zero_smul_one` (`N(0, uI_d)` is the image of `stdGaussian` under
  `x ↦ √u • x`). No hypotheses; Lean-core axioms only.
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

- `ScaleSpaceCore.SelfDecomposable` (Q-0303; SSL-3 of `spatial-hemigroup-affine`'s
  `records/formalization/SECOND-DEMAND.md`): self-decomposability (`IsSelfDecomposable`, the
  measure form `μ = (c •)_* μ ∗ ρ_c`, `c ∈ (0,1)`, residual existential) and operator
  self-decomposability (`IsBSelfDecomposable`, `μ = (e^{-tB})_* μ ∗ ρ_t`, `t > 0`) on a real normed
  space; the scalar notion as the case `B = 1` (`isBSelfDecomposable_one_iff`) and the `t ≥ 0` form
  (`isBSelfDecomposable_iff_nonneg`); images under continuous linear maps
  (`IsSelfDecomposable.map`); on a finite-dimensional real inner product space the transform form
  (`isSelfDecomposable_iff_charFun`, Paper VII's form), the line's `b > 1` form
  (`isSelfDecomposable_real_iff`, Paper V's `SpatialLine.IsSelfDecomposable` verbatim), the
  doubling inequality, and a transform without zeros (`IsSelfDecomposable.charFun_ne_zero`, the
  argument of Paper VII's `prop:gw-ray-families`(1)). The second demand is Paper V on `ℝ` and
  Paper VII on `ℝ^d`; neither article is edited here, and their re-pointing is a later item. A
  candidate for the promotion cycle into `harmonic-semigroups` (ADR-0026, Decision 3); the
  generality chosen is recorded in the module docstring as provisional.

- `ScaleSpaceCore.DilationInvariance`: `dilation_invariance` — a function continuous at the
  origin, where it vanishes, and fixed by one dilation vanishes identically. Moved from Paper V's
  `SpatialLine/Dilation.lean` (`lem:dilation-invariance`, [V, Lem. 6.3]), second demand now: Paper
  V's classification uniqueness clause, and Paper VII's `thm:isotropic-classification`,
  `prop:isotropic-corner`, `prop:similarity-ray-families`(3) and `prop:diagonal-ray-families`(5)
  (`spatial-hemigroup-affine/records/formalization/SECOND-DEMAND.md` § 3 row V8; § 6, SSL-4). The
  statement is Lean-core only; `AxiomCheck.lean` prints only `propext`, `Classical.choice`,
  `Quot.sound`. `dilation_atom`, the other lemma in the source file, is not moved here: it is not
  second demand and the moved proof does not use it. (It moved later with the line
  classification, into `DilationAtom`.) No article repository is edited by this
  change.
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

- **The line classification, stated conditionally** (Q-0305; SSL-6 of
  `spatial-hemigroup-affine/records/formalization/SECOND-DEMAND.md`, row V6; ADR-0026 § 5).
  Paper V's [V, Thm. 7.3] in the trunk, with each cited interface a **hypothesis**:
  - `ScaleSpaceCore.LineInterfaces`: `SymLevyUnique` (the uniqueness clause of the symmetric
    Lévy–Khintchine representation on `ℝ`, Sato Thm. 8.1(ii)), `SymLevyConverse` (its converse,
    Sato Thm. 8.1(iii)) and `BochnerSymm` (Bochner's theorem, symmetric form, Sato Prop. 2.5),
    each a `Prop` with exactly the statement of Paper V's axiom of the same content
    (`fourier_toolbox_levy_unique`, `fourier_toolbox_levy_converse`,
    `fourier_toolbox_bochner_symm`); the last two bundled as the `Prop`-valued structure
    `LineLawInterfaces`, because the construction spends them together at one step.
  - `ScaleSpaceCore.MainAnalysis`: `main_analysis` and `main_analysis_exists` take
    `hA3 : SymLevyUnique` and nothing else (it is spent once, in `dilate_le_of_increments`,
    through `sd_exponents_one_implies_three`); `main_uniqueness` takes no hypothesis;
    `main_analysis_of_profileForm` as in Paper V.
  - `ScaleSpaceCore.MainConstruction`: `main_construction` takes `hI : LineLawInterfaces`.
  - What they reach, moved alongside: `Exponent` (`IsPositiveDefinite`, `IsSymNegDef`,
    `IsSymLevyExponent`), `TransformBridge`, `TransformUniqueness`, the character pairing appended
    to `BochnerConvolution` (`charCLM`, `gaussL1`, `mconvL1_injective`, `setIntegral_bconv`),
    `Representation`, `Nonvanishing`, `Pairing`, `Cascade` (`exists_kernelFamily`,
    `kernel_symmetric`), `Additivity`, `Transmittance`, `Covariance`, `DilationAtom`
    (`dilation_atom`, now reached), `Rigidity`, `Gauge`, `GaugeLevy` (`canonical_gauge`),
    `Truncation`, `NullArray`, `Tightness`, `LevyExtraction`, `Increments` (`increments_levy`),
    `SDExponents` (Paper V's `SelfDecomposable` increments and `incrementProfile`),
    `DilationDecrease`, `AntitoneDensity`, `AnalysisDirection`.

  Moved from Paper V's cone export (`cone-v0.1`, `f28c066e`): exactly the declarations in the
  closure of the four theorems, computed from Paper V's environment; statements and proofs
  unchanged up to the namespace except where an axiom call became the hypothesis, and in
  `MainConstruction`, where the continuity of `F` is `SDProfile.continuous_exponent` (Lean core)
  instead of `profile_integrability_mem` (which spends A3's converse and stays behind). The
  conclusions are Paper V's. `AxiomCheck.lean` gains a line for every moved declaration (282);
  all print only `propext`, `Classical.choice`, `Quot.sound`. Stayed behind: the bundle
  `main_characterization`, `profile_integrability_mem`, `increments_levy_infinitely_divisible`,
  `sd_exponents_three_implies_one`, and the non-closure declarations of each source module. Paper
  V and Paper VII are not edited: Paper V discharges `hA3` with `fourier_toolbox_levy_unique` and
  `hI` with `⟨fourier_toolbox_levy_converse, fourier_toolbox_bochner_symm⟩`; Paper VII discharges
  `hA3` from its own ledger A3 at `d = 1` when it switches. No tag is cut here.

## [0.2.0]

- `PowerSumSymmetry`: vanishing odd power sums and the halving identity.
- `PolyaFrequencyClass`: Karlin's bilateral Laplace transform and the class `E₂*`.
- `CausalCone`, `CausalData`: the causal admissible cone as a shared type
  (`CausalAdmissible`), and its three generators (drift, Gamma, stable).

## [0.1.1]

- Release-readiness only (Apache 2.0 license, public README); no module changes.

## [0.1.0]

- Initial modules: `Wedge`, `ReceptiveField`, `BoostBracket`, `BoostBracketConcrete`.
