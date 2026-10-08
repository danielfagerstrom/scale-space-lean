/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import ScaleSpaceCore

/-! The discipline this library claims: everything is proved from Mathlib alone, so a
consumer's trust base gains nothing by depending on it. Anything beyond Lean core
(propext, Classical.choice, Quot.sound) means an analytic interface has leaked in. -/

#print axioms ScaleSpace.LieWedge
#print axioms ScaleSpace.CovariantTensor
#print axioms ScaleSpace.ReceptiveField.Solves
#print axioms ScaleSpace.ReceptiveField.iteratedDeriv_solves
#print axioms ScaleSpace.BoostBracket.boost_bracket
#print axioms ScaleSpace.BoostBracket.Concrete.boost_bracket_concrete
#print axioms ScaleSpace.squareWeightedAtoms
#print axioms ScaleSpace.isFiniteMeasure_squareWeightedAtoms
#print axioms ScaleSpace.integral_squareWeightedAtoms
#print axioms ScaleSpace.tsum_sq_mul_sin_eq_zero
#print axioms ScaleSpace.squareWeightedAtoms_neg
#print axioms ScaleSpace.squareWeightedAtoms_map_neg
#print axioms ScaleSpace.summable_comp_of_abs_le_sq
#print axioms ScaleSpace.summable_comp_max_of_abs_le_sq
#print axioms ScaleSpace.tsum_eq_two_mul_tsum_posPart

-- CausalCone: half-line helpers
#print axioms ScaleSpace.lintegral_Ioi_split
#print axioms ScaleSpace.map_mul_restrict_Ioi
#print axioms ScaleSpace.setLIntegral_Ioi_comp_mul
#print axioms ScaleSpace.lintegral_ofReal_ne_top_of_integrableOn
-- CausalCone: the structure and its exponent
#print axioms ScaleSpace.CausalAdmissible
#print axioms ScaleSpace.CausalAdmissible.exponentL
#print axioms ScaleSpace.CausalAdmissible.exponent
#print axioms ScaleSpace.CausalAdmissible.aemeasurable_k
#print axioms ScaleSpace.CausalAdmissible.aemeasurable_k_mono
#print axioms ScaleSpace.CausalAdmissible.integrableOn_k_Ioo
#print axioms ScaleSpace.CausalAdmissible.integrableOn_k_div_Ioi
#print axioms ScaleSpace.CausalAdmissible.mul_exp_neg_le
#print axioms ScaleSpace.CausalAdmissible.one_sub_exp_bounds
#print axioms ScaleSpace.CausalAdmissible.Ioi_zero_eq_union
#print axioms ScaleSpace.CausalAdmissible.integrableOn_k_div_Ici
#print axioms ScaleSpace.CausalAdmissible.aemeasurable_k_Ioo
#print axioms ScaleSpace.CausalAdmissible.aemeasurable_k_Ici
#print axioms ScaleSpace.CausalAdmissible.measurable_expIntegrand
#print axioms ScaleSpace.CausalAdmissible.integrableOn_exponentIntegrand
#print axioms ScaleSpace.CausalAdmissible.integrableOn_derivIntegrand
#print axioms ScaleSpace.CausalAdmissible.exponentIntegrand_nonneg
#print axioms ScaleSpace.CausalAdmissible.lintegral_exponentIntegrand_ne_top
#print axioms ScaleSpace.CausalAdmissible.exponentL_ne_top
#print axioms ScaleSpace.CausalAdmissible.exponent_eq
#print axioms ScaleSpace.CausalAdmissible.exponent_zero
#print axioms ScaleSpace.CausalAdmissible.hasDerivAt_exponent
#print axioms ScaleSpace.CausalAdmissible.exponent_eq_zero_of_trivial
#print axioms ScaleSpace.CausalAdmissible.deriv_integral_pos
-- CausalCone: the two field forms
#print axioms ScaleSpace.CausalAdmissible.lintegral_min_split
#print axioms ScaleSpace.CausalAdmissible.lintegral_min_ne_top
#print axioms ScaleSpace.CausalAdmissible.min_one_mul_le
#print axioms ScaleSpace.CausalAdmissible.min_one_le_two_mul_one_sub_exp
#print axioms ScaleSpace.CausalAdmissible.lintegral_exponentIntegrand_ne_top_of_windows
#print axioms ScaleSpace.CausalAdmissible.windows_of_lintegral_exponentIntegrand_ne_top
#print axioms ScaleSpace.CausalAdmissible.ne_top_iff_windows
#print axioms ScaleSpace.CausalAdmissible.ofNeTop
#print axioms ScaleSpace.CausalAdmissible.ofNeTop_b₀
#print axioms ScaleSpace.CausalAdmissible.ofNeTop_k
#print axioms ScaleSpace.CausalAdmissible.ofNeTop_exponentL
-- CausalCone: the combinators
#print axioms ScaleSpace.CausalAdmissible.add
#print axioms ScaleSpace.CausalAdmissible.smul
#print axioms ScaleSpace.CausalAdmissible.lintegral_min_dilate_ne_top
#print axioms ScaleSpace.CausalAdmissible.dilate
#print axioms ScaleSpace.CausalAdmissible.add_b₀
#print axioms ScaleSpace.CausalAdmissible.add_k
#print axioms ScaleSpace.CausalAdmissible.smul_b₀
#print axioms ScaleSpace.CausalAdmissible.smul_k
#print axioms ScaleSpace.CausalAdmissible.dilate_b₀
#print axioms ScaleSpace.CausalAdmissible.dilate_k
#print axioms ScaleSpace.CausalAdmissible.exponentL_add
#print axioms ScaleSpace.CausalAdmissible.exponentL_smul
#print axioms ScaleSpace.CausalAdmissible.exponentL_dilate
#print axioms ScaleSpace.CausalAdmissible.exponent_add
#print axioms ScaleSpace.CausalAdmissible.exponent_smul
#print axioms ScaleSpace.CausalAdmissible.exponent_dilate
-- CausalData: the three generators
#print axioms ScaleSpace.CausalAdmissible.driftDatum
#print axioms ScaleSpace.CausalAdmissible.driftDatum_exponent
#print axioms ScaleSpace.CausalAdmissible.gammaCausalProfile
#print axioms ScaleSpace.CausalAdmissible.gammaCausalProfile_nonneg
#print axioms ScaleSpace.CausalAdmissible.gammaCausalProfile_le
#print axioms ScaleSpace.CausalAdmissible.integrableOn_gammaCausalProfile
#print axioms ScaleSpace.CausalAdmissible.integrableOn_gammaCausalProfile_div
#print axioms ScaleSpace.CausalAdmissible.gammaCausalDatum
#print axioms ScaleSpace.CausalAdmissible.gammaCausalDatum_b₀
#print axioms ScaleSpace.CausalAdmissible.gammaCausalDatum_k
#print axioms ScaleSpace.CausalAdmissible.stableCausalProfile
#print axioms ScaleSpace.CausalAdmissible.stableCausalConst_pos
#print axioms ScaleSpace.CausalAdmissible.stableCausalProfile_nonneg
#print axioms ScaleSpace.CausalAdmissible.stableCausalProfile_antitoneOn
#print axioms ScaleSpace.CausalAdmissible.integrableOn_stableCausalProfile
#print axioms ScaleSpace.CausalAdmissible.integrableOn_stableCausalProfile_div
#print axioms ScaleSpace.CausalAdmissible.stableCausalDatum
#print axioms ScaleSpace.CausalAdmissible.stableCausalDatum_b₀
#print axioms ScaleSpace.CausalAdmissible.stableCausalDatum_dilate_k
#print axioms ScaleSpace.CausalAdmissible.stableCausalDatum_exponent_mul
#print axioms ScaleSpace.CausalAdmissible.stableCausalDatum_integral_one
#print axioms ScaleSpace.CausalAdmissible.stableCausalDatum_exponent
#print axioms ScaleSpace.bilateralLaplace_eq_complexMGF
#print axioms ScaleSpace.bilateralLaplace_ofReal_mul_I
#print axioms ScaleSpace.bilateralLaplace_ofReal
#print axioms ScaleSpace.bilateralLaplace_neg_of_map_neg
#print axioms ScaleSpace.multipliable_polyaE2_factor
#print axioms ScaleSpace.ofReal_tprod_of_multipliable
#print axioms ScaleSpace.summable_pairSeq_sq
#print axioms ScaleSpace.tsum_pairSeq_sq
#print axioms ScaleSpace.polyaE2_pairSeq_mul_I
#print axioms ScaleSpace.polyaE2_ofReal
#print axioms ScaleSpace.norm_polyaE2_mul_I
#print axioms ScaleSpace.eq_zero_of_hasSum_mul_pow_eq_zero
#print axioms ScaleSpace.oddPowerSums_eq_zero
#print axioms ScaleSpace.polyaE2_even_imp_oddPowerSums

-- L1Operators: `X`, translation, and convolution by a measure
#print axioms ScaleSpace.X
#print axioms ScaleSpace.IsNonneg
#print axioms ScaleSpace.measurePreserving_sub_const
#print axioms ScaleSpace.translate_congr_ae
#print axioms ScaleSpace.integrable_translate
#print axioms ScaleSpace.transₗ
#print axioms ScaleSpace.transL1
#print axioms ScaleSpace.coeFn_transL1
#print axioms ScaleSpace.mconv
#print axioms ScaleSpace.mconv_apply
#print axioms ScaleSpace.lintegral_lintegral_sub_eq
#print axioms ScaleSpace.lintegral_enorm_mconv_le
#print axioms ScaleSpace.integrable_uncurry_sub
#print axioms ScaleSpace.integrable_mconv
#print axioms ScaleSpace.ae_ae_sub_of_ae
#print axioms ScaleSpace.mconv_congr_ae
#print axioms ScaleSpace.mconv_add_ae
#print axioms ScaleSpace.mconv_smul
#print axioms ScaleSpace.mconvₗ
#print axioms ScaleSpace.mconvL1
#print axioms ScaleSpace.coeFn_mconvL1
-- L1Operators: what `mconvL1` does
#print axioms ScaleSpace.mconv_comp_sub
#print axioms ScaleSpace.mconv_nonneg
#print axioms ScaleSpace.integral_mconv
#print axioms ScaleSpace.mconv_conv
#print axioms ScaleSpace.mconv_dirac_zero
#print axioms ScaleSpace.mconvL1_congr
#print axioms ScaleSpace.norm_mconvL1_le
#print axioms ScaleSpace.mconvL1_transL1
#print axioms ScaleSpace.isNonneg_mconvL1
#print axioms ScaleSpace.integral_mconvL1
#print axioms ScaleSpace.mconvL1_comp
#print axioms ScaleSpace.mconvL1_dirac_zero
#print axioms ScaleSpace.integral_mul_mconv

-- BochnerConvolution: translation acts continuously on `L¹`
#print axioms ScaleSpace.subCM
#print axioms ScaleSpace.subCM_apply
#print axioms ScaleSpace.measurePreserving_subCM
#print axioms ScaleSpace.transL1_eq
#print axioms ScaleSpace.continuous_transL1
#print axioms ScaleSpace.norm_transL1_le
-- BochnerConvolution: convolution as a Bochner integral, and `bconv = ` the classical convolution
#print axioms ScaleSpace.bconv
#print axioms ScaleSpace.integrable_smul_transL1
#print axioms ScaleSpace.map_bconv
#print axioms ScaleSpace.setIntegralCLM
#print axioms ScaleSpace.setIntegralCLM_apply
#print axioms ScaleSpace.integrable_uncurry_pconv
#print axioms ScaleSpace.integrable_pconv
#print axioms ScaleSpace.coeFn_bconv
#print axioms ScaleSpace.measurePreserving_const_sub
#print axioms ScaleSpace.bconv_comm
-- BochnerConvolution: `μ * f` as a Bochner integral, and pairing with a bounded functional
#print axioms ScaleSpace.integrable_transL1
#print axioms ScaleSpace.bconvM
#print axioms ScaleSpace.bconvM_eq_mconvL1
#print axioms ScaleSpace.apply_mconvL1_general
#print axioms ScaleSpace.pairTrans
#print axioms ScaleSpace.pairTrans_apply
#print axioms ScaleSpace.apply_mconvL1
#print axioms ScaleSpace.apply_bconv

-- LaplaceUniqueness: the substitution `x = e^{-t}`, and Weierstrass on `[0,1]`
#print axioms ScaleSpace.expNeg
#print axioms ScaleSpace.continuous_expNeg
#print axioms ScaleSpace.injective_expNeg
#print axioms ScaleSpace.measurableEmbedding_expNeg
#print axioms ScaleSpace.integrable_of_carried
#print axioms ScaleSpace.abs_integral_sub_le_of_carried
#print axioms ScaleSpace.integral_polynomial_eq_of_moments
#print axioms ScaleSpace.ext_of_moments
-- LaplaceUniqueness: injectivity of the Laplace transform on folded measures (Q-0360)
#print axioms ScaleSpace.integral_exp_neg_eq_toReal_laplaceL
#print axioms ScaleSpace.expNeg_mem_Icc
#print axioms ScaleSpace.map_expNeg_compl_Icc
#print axioms ScaleSpace.isFiniteMeasure_map_expNeg
#print axioms ScaleSpace.integral_pow_map_expNeg
#print axioms ScaleSpace.laplaceL_injective_of_isFiniteMeasure
#print axioms ScaleSpace.laplaceL_withDensity_expNeg
#print axioms ScaleSpace.laplaceL_injective_of_ne_top
#print axioms ScaleSpace.laplace_uniqueness_locally_finite

-- TailInverse: the generalised inverse of a nonincreasing tail function
#print axioms ScaleSpace.tailInv
#print axioms ScaleSpace.tailInv_nonneg
#print axioms ScaleSpace.bddAbove_tailSet
#print axioms ScaleSpace.lt_of_lt_tailInv
#print axioms ScaleSpace.lt_tailInv_of_lt
#print axioms ScaleSpace.antitoneOn_tailInv

-- L1Operators: reflection and dilation (Q-0301)
#print axioms ScaleSpace.measurePreserving_neg'
#print axioms ScaleSpace.reflect_congr_ae
#print axioms ScaleSpace.integrable_reflect
#print axioms ScaleSpace.reflₗ
#print axioms ScaleSpace.reflL1
#print axioms ScaleSpace.coeFn_reflL1
#print axioms ScaleSpace.quasiMeasurePreserving_const_mul
#print axioms ScaleSpace.dilate
#print axioms ScaleSpace.dilate_congr_ae
#print axioms ScaleSpace.integrable_dilate
#print axioms ScaleSpace.lintegral_comp_const_mul
#print axioms ScaleSpace.dilₗ
#print axioms ScaleSpace.dilL1
#print axioms ScaleSpace.coeFn_dilL1

-- Transform: symmetry, the cosine transform, the exponent, the bridge to `charFun`
#print axioms ScaleSpace.IsSymmetric
#print axioms ScaleSpace.fourierCos
#print axioms ScaleSpace.fourierCos_apply
#print axioms ScaleSpace.exponent
#print axioms ScaleSpace.exponent_apply
#print axioms ScaleSpace.fourierCos_dirac_zero
#print axioms ScaleSpace.integrable_charFun_integrand
#print axioms ScaleSpace.fourierCos_eq_charFun_re
#print axioms ScaleSpace.charFun_eq_fourierCos_of_symmetric
-- Transform: the Laplace transform on the half-line (Q-0360)
#print axioms ScaleSpace.laplaceL
#print axioms ScaleSpace.laplaceL_apply
-- Transform: the point mass at the origin is symmetric, the truncation of `1 - cos` (Q-0364)
#print axioms ScaleSpace.isSymmetric_dirac_zero
#print axioms ScaleSpace.one_sub_cos_le

-- Transport: convolution against reflection and dilation, the kernel of the identity
#print axioms ScaleSpace.mconv_reflect
#print axioms ScaleSpace.mconvL1_reflL1
#print axioms ScaleSpace.dilate_mconv
#print axioms ScaleSpace.dilL1_comp_mconvL1
#print axioms ScaleSpace.eq_dirac_of_mconvL1_eq_id
#print axioms ScaleSpace.norm_sub_eq_lintegral

-- Family: the cascade-family vocabulary
#print axioms ScaleSpace.PreCascadeCore
#print axioms ScaleSpace.IsPositive
#print axioms ScaleSpace.IsNondegenerate
#print axioms ScaleSpace.CascadeCore
#print axioms ScaleSpace.IsScaleCovariant
#print axioms ScaleSpace.CascadeFamily
#print axioms ScaleSpace.IsKernelFamily
#print axioms ScaleSpace.IsSymmetricKernelFamily
#print axioms ScaleSpace.IsScaleCovariant.S_zero
#print axioms ScaleSpace.IsScaleCovariant.S_pos

-- L1Continuity: the modulus of continuity of translation, and Lévy's continuity theorem
#print axioms ScaleSpace.levy_continuity
#print axioms ScaleSpace.transDiff
#print axioms ScaleSpace.continuous_transDiff
#print axioms ScaleSpace.transDiff_nonneg
#print axioms ScaleSpace.transDiff_zero
#print axioms ScaleSpace.transDiff_le
#print axioms ScaleSpace.integrable_transDiff
#print axioms ScaleSpace.lintegral_enorm_sub_eq
#print axioms ScaleSpace.lintegral_enorm_mconv_sub_le
#print axioms ScaleSpace.norm_mconvL1_sub_le
#print axioms ScaleSpace.transDiff_mconvL1_le
#print axioms ScaleSpace.norm_mconvL1_comp_sub_le
#print axioms ScaleSpace.transDiffBCF
#print axioms ScaleSpace.transDiffBCF_apply
#print axioms ScaleSpace.tendsto_integral_transDiff_of_tendsto_charFun
#print axioms ScaleSpace.tendsto_norm_mconvL1_sub_of_tendsto_charFun

-- Construction: the kernel constructor
#print axioms ScaleSpace.CascadeData
#print axioms ScaleSpace.CascadeData.instIsProbabilityMeasure
#print axioms ScaleSpace.CascadeData.charFun_kernel
#print axioms ScaleSpace.CascadeData.tendsto_integral_transDiff
#print axioms ScaleSpace.CascadeData.norm_sub_left
#print axioms ScaleSpace.CascadeData.norm_sub_right
#print axioms ScaleSpace.CascadeData.continuousOn_mconvL1
#print axioms ScaleSpace.CascadeData.preCore
#print axioms ScaleSpace.CascadeData.preCore_Φ
#print axioms ScaleSpace.CascadeData.isPositive
#print axioms ScaleSpace.CascadeData.isKernelFamily
#print axioms ScaleSpace.CascadeData.isNondegenerate
#print axioms ScaleSpace.CascadeData.cascadeCore
#print axioms ScaleSpace.CascadeData.cascadeCore_Φ
#print axioms ScaleSpace.CascadeData.isScaleCovariant

-- SDProfile: the line's admissible cone, the symmetric Lévy pair, and `lem:profile-integrability`
#print axioms ScaleSpace.IsFolded
#print axioms ScaleSpace.SymLevyPair
#print axioms ScaleSpace.SymLevyPair.exponentL
#print axioms ScaleSpace.SymLevyPair.exponent
#print axioms ScaleSpace.profileMeasure
#print axioms ScaleSpace.SDProfile
#print axioms ScaleSpace.SDProfile.exponentL
#print axioms ScaleSpace.SDProfile.exponent
#print axioms ScaleSpace.SDProfile.levyMeasure
#print axioms ScaleSpace.IsAdmissibleExponent
#print axioms ScaleSpace.SymLevyPair.lintegral_sq_div_two_ne_top
#print axioms ScaleSpace.SymLevyPair.measure_Ioi_one_ne_top
#print axioms ScaleSpace.SymLevyPair.quadratic_growth
#print axioms ScaleSpace.SymLevyPair.exponentL_ne_top
#print axioms ScaleSpace.profile_integrability
#print axioms ScaleSpace.isFolded_profileMeasure
#print axioms ScaleSpace.exponentL_eq_of_profileMeasure
#print axioms ScaleSpace.profile_integrability_pair
#print axioms ScaleSpace.SDProfile.exponent_zero
-- SDProfileCone: `lem:admissible-cone` and continuity
#print axioms ScaleSpace.SDProfile.aemeasurable_k
#print axioms ScaleSpace.SDProfile.aemeasurable_k_mono
#print axioms ScaleSpace.SDProfile.add
#print axioms ScaleSpace.SDProfile.smul
#print axioms ScaleSpace.SDProfile.add_a
#print axioms ScaleSpace.SDProfile.add_k
#print axioms ScaleSpace.SDProfile.smul_a
#print axioms ScaleSpace.SDProfile.smul_k
#print axioms ScaleSpace.SDProfile.exponentL_ne_top
#print axioms ScaleSpace.SDProfile.exponentL_neg
#print axioms ScaleSpace.SDProfile.exponent_neg
#print axioms ScaleSpace.SDProfile.exponentL_add
#print axioms ScaleSpace.SDProfile.exponentL_smul
#print axioms ScaleSpace.SDProfile.exponent_add
#print axioms ScaleSpace.SDProfile.exponent_smul
#print axioms ScaleSpace.admissible_cone
#print axioms ScaleSpace.SymLevyPair.one_sub_cos_mul_le
#print axioms ScaleSpace.SymLevyPair.measurable_one_sub_cos
#print axioms ScaleSpace.SymLevyPair.continuous_jump
#print axioms ScaleSpace.SymLevyPair.continuous_exponentL
#print axioms ScaleSpace.SymLevyPair.continuous_exponent
#print axioms ScaleSpace.SDProfile.continuous_exponent

-- BrownianDensity: the cosine transform at a Gaussian, and the Brownian density
#print axioms ScaleSpace.fourierCos_gaussianReal
#print axioms ScaleSpace.brownianLaw
#print axioms ScaleSpace.brownianDensity
#print axioms ScaleSpace.brownianDensity_eq
#print axioms ScaleSpace.brownianDensity_nonneg
#print axioms ScaleSpace.measurable_brownianDensity
#print axioms ScaleSpace.measurable_brownianDensity_time
#print axioms ScaleSpace.measurable_brownianDensity_uncurry
#print axioms ScaleSpace.brownianDensity_neg
#print axioms ScaleSpace.brownianLaw_eq_withDensity
#print axioms ScaleSpace.sq_le_four_mul_exp
#print axioms ScaleSpace.brownianDensity_div_le
#print axioms ScaleSpace.brownianDensity_le_one
#print axioms ScaleSpace.lintegral_brownianLaw_one_sub_cos
#print axioms ScaleSpace.lintegral_brownianDensity
#print axioms ScaleSpace.lintegral_even_eq_two_mul
#print axioms ScaleSpace.lintegral_Ioi_brownianDensity_one_sub_cos
-- BrownianDensity: mixtures against the Brownian laws (Q-0363, SSL-8)
#print axioms ScaleSpace.measurable_brownianLaw
#print axioms ScaleSpace.isProbabilityMeasure_bind_brownianLaw
#print axioms ScaleSpace.fourierCos_bind_brownianLaw

-- BridgeExponents: `lem:bridge-exponents`, from `CausalAdmissible` into `SDProfile`
#print axioms ScaleSpace.mixWeight
#print axioms ScaleSpace.mixWeight_nonneg
#print axioms ScaleSpace.CausalAdmissible.mixDensityL
#print axioms ScaleSpace.CausalAdmissible.mixDensityL_ne_top
#print axioms ScaleSpace.CausalAdmissible.ofReal_mul_mixDensityL
#print axioms ScaleSpace.CausalAdmissible.mixDensityL_antitone
#print axioms ScaleSpace.CausalAdmissible.bridgeProfile
#print axioms ScaleSpace.CausalAdmissible.integral_eq_mixDensityL
#print axioms ScaleSpace.CausalAdmissible.bridgeProfile_eq
#print axioms ScaleSpace.CausalAdmissible.bridgeProfile_nonneg
#print axioms ScaleSpace.CausalAdmissible.bridgeProfile_zero
#print axioms ScaleSpace.CausalAdmissible.bridgeProfile_antitoneOn
#print axioms ScaleSpace.CausalAdmissible.ofReal_bridgeProfile_div
#print axioms ScaleSpace.integral_sq_gaussianReal
#print axioms ScaleSpace.integrable_sq_brownianLaw
#print axioms ScaleSpace.lintegral_sq_brownianDensity
#print axioms ScaleSpace.lintegral_brownianDensity_eq_one
#print axioms ScaleSpace.lintegral_min_brownianDensity_le
#print axioms ScaleSpace.CausalAdmissible.lintegral_Ioi_mul_mixDensityL
#print axioms ScaleSpace.CausalAdmissible.aemeasurable_bridgeProfile
#print axioms ScaleSpace.CausalAdmissible.lintegral_min_profileMeasure_ne_top
#print axioms ScaleSpace.CausalAdmissible.profileJump_bridgeProfile
#print axioms ScaleSpace.CausalAdmissible.bridgeDatum
#print axioms ScaleSpace.CausalAdmissible.bridgeDatum_a
#print axioms ScaleSpace.CausalAdmissible.bridgeDatum_k
#print axioms ScaleSpace.CausalAdmissible.bridgeDatum_exponentL
#print axioms ScaleSpace.CausalAdmissible.bridgeDatum_exponent
#print axioms ScaleSpace.bridge_exponents

-- Cin: `Cin` and the function clauses of `lem:cin-rays`(1)
#print axioms ScaleSpace.cinIntegrand
#print axioms ScaleSpace.cin
#print axioms ScaleSpace.cin_apply
#print axioms ScaleSpace.cinProfile
#print axioms ScaleSpace.cinIntegrand_nonneg
#print axioms ScaleSpace.cinIntegrand_neg
#print axioms ScaleSpace.cinIntegrand_le_half
#print axioms ScaleSpace.measurable_cinIntegrand
#print axioms ScaleSpace.intervalIntegrable_cinIntegrand
#print axioms ScaleSpace.abs_cinIntegrand_le
#print axioms ScaleSpace.continuous_cinIntegrand
#print axioms ScaleSpace.hasDerivAt_cin
#print axioms ScaleSpace.continuous_cin
#print axioms ScaleSpace.cin_zero
#print axioms ScaleSpace.cin_neg
#print axioms ScaleSpace.cin_nonneg
#print axioms ScaleSpace.cin_le_sq_of_nonneg
#print axioms ScaleSpace.cin_le_sq
#print axioms ScaleSpace.monotoneOn_cin
#print axioms ScaleSpace.cin_elementary
#print axioms ScaleSpace.cin_sub_sq_bound
#print axioms ScaleSpace.cin_expansion_zero_bound
#print axioms ScaleSpace.cin_expansion_zero
#print axioms ScaleSpace.rpow_neg_two
#print axioms ScaleSpace.integrableOn_sin_div_sq
#print axioms ScaleSpace.norm_integral_Ioi_sin_div_sq
#print axioms ScaleSpace.hasDerivAt_sin_div
#print axioms ScaleSpace.integral_cos_div
#print axioms ScaleSpace.cin_eq_log_sub
#print axioms ScaleSpace.cinConst
#print axioms ScaleSpace.cin_sub_log_eq
#print axioms ScaleSpace.cin_expansion_top_bound
#print axioms ScaleSpace.cin_expansion_top
#print axioms ScaleSpace.cin_nonneg'
#print axioms ScaleSpace.dilate_cinIntegrand
#print axioms ScaleSpace.intervalIntegral_dilate_cinIntegrand
#print axioms ScaleSpace.dilate_cinIntegrand_nonneg
#print axioms ScaleSpace.dilate_cinIntegrand_le
#print axioms ScaleSpace.intervalIntegrable_dilate_cinIntegrand
-- CinRays: the ray
#print axioms ScaleSpace.cinProfile_nonneg
#print axioms ScaleSpace.cinProfile_le_one
#print axioms ScaleSpace.cinProfile_eq_zero
#print axioms ScaleSpace.cinProfile_eq_one
#print axioms ScaleSpace.antitoneOn_cinProfile
#print axioms ScaleSpace.measurable_cinProfile
#print axioms ScaleSpace.cinSDProfile
#print axioms ScaleSpace.cinSDProfile_exponentL
#print axioms ScaleSpace.cin_ray

-- SelfDecomposable: self-decomposability on a real vector space, the line as an instance
#print axioms ScaleSpace.IsSelfDecomposable
#print axioms ScaleSpace.IsBSelfDecomposable
#print axioms ScaleSpace.coe_exp_neg_smul_one
#print axioms ScaleSpace.isBSelfDecomposable_one_iff
#print axioms ScaleSpace.isBSelfDecomposable_iff_nonneg
#print axioms ScaleSpace.IsSelfDecomposable.map
#print axioms ScaleSpace.isSelfDecomposable_iff_charFun
#print axioms ScaleSpace.isSelfDecomposable_real_iff
#print axioms ScaleSpace.re_charFun_eq_integral_cos
#print axioms ScaleSpace.one_sub_re_charFun_two_smul_le
#print axioms ScaleSpace.one_sub_norm_sq_charFun_two_smul_le
#print axioms ScaleSpace.IsSelfDecomposable.charFun_ne_zero

-- GaussianKernel: the kernel `u ↦ N(0, uI_d)` is measurable
#print axioms ScaleSpace.sqrt_smul_one_eq
#print axioms ScaleSpace.multivariateGaussian_zero_smul_one
#print axioms ScaleSpace.measurable_multivariateGaussian_zero_smul_one

-- DilationInvariance: a function fixed by one dilation is constant
#print axioms ScaleSpace.dilation_invariance

-- Q-0305: the line classification and what it reaches, moved from Paper V
-- (`cone-v0.1`). `main_analysis`, `main_analysis_exists` take `SymLevyUnique`,
-- `main_construction` takes `LineLawInterfaces`, as hypotheses; each line below must
-- print only `propext`, `Classical.choice`, `Quot.sound`.
-- TransformBridge: The bridge between the cosine transform and Mathlib's characteristic function
#print axioms ScaleSpace.integrable_cos_mul
#print axioms ScaleSpace.integrable_sin_mul
#print axioms ScaleSpace.fourierCos_zero
#print axioms ScaleSpace.fourierCos_le_one
#print axioms ScaleSpace.continuous_fourierCos
#print axioms ScaleSpace.charFun_map_const_mul
-- TransformUniqueness: Uniqueness and continuity for the Fourier transform of a measure on the line
#print axioms ScaleSpace.fourier_uniqueness
-- Exponent: The function classes: positive definiteness, `NDₛ` and `LEₛ`
#print axioms ScaleSpace.IsPositiveDefinite
#print axioms ScaleSpace.IsSymNegDef
#print axioms ScaleSpace.IsSymLevyExponent
-- BochnerConvolution: Convolution as a vector-valued integral, and pairing against a bounded functional
#print axioms ScaleSpace.bconv_congr_ae
#print axioms ScaleSpace.setIntegral_bconv
#print axioms ScaleSpace.integrable_setIntegral_bconv
#print axioms ScaleSpace.integrable_char_mul
#print axioms ScaleSpace.charCLM
#print axioms ScaleSpace.charCLM_apply
#print axioms ScaleSpace.charCLM_transL1
#print axioms ScaleSpace.charCLM_mconvL1
#print axioms ScaleSpace.gaussL1
#print axioms ScaleSpace.coeFn_gaussL1
#print axioms ScaleSpace.charCLM_gaussL1
#print axioms ScaleSpace.charCLM_gaussL1_ne_zero
#print axioms ScaleSpace.mconvL1_injective
-- Representation: `lem:convolution-representation`: the operators are convolutions
#print axioms ScaleSpace.approxId
#print axioms ScaleSpace.approxId_eq_zero
#print axioms ScaleSpace.approxId_nonneg
#print axioms ScaleSpace.integrable_approxId
#print axioms ScaleSpace.integral_approxId
#print axioms ScaleSpace.approxIdL1
#print axioms ScaleSpace.coeFn_approxIdL1
#print axioms ScaleSpace.isNonneg_approxIdL1
#print axioms ScaleSpace.integral_approxIdL1
#print axioms ScaleSpace.transL1_zero
#print axioms ScaleSpace.tendsto_bconv_approxId
#print axioms ScaleSpace.tendsto_bconv_approxIdL1
#print axioms ScaleSpace.approx
#print axioms ScaleSpace.approxMeasure
#print axioms ScaleSpace.isNonneg_approx
#print axioms ScaleSpace.integral_approx
#print axioms ScaleSpace.bconv_approx
#print axioms ScaleSpace.tendsto_bconv_approx
#print axioms ScaleSpace.isProbabilityMeasure_approxMeasure
#print axioms ScaleSpace.tailSet
#print axioms ScaleSpace.measurableSet_tailSet
#print axioms ScaleSpace.tailSet_antitone
#print axioms ScaleSpace.setIntegral_comp_sub_right
#print axioms ScaleSpace.tail_le_tail_bconv
#print axioms ScaleSpace.exists_measure_tailSet_le
#print axioms ScaleSpace.exists_setIntegral_abs_tailSet_le
#print axioms ScaleSpace.epsSeq
#print axioms ScaleSpace.epsSeq_pos
#print axioms ScaleSpace.tendsto_epsSeq
#print axioms ScaleSpace.exists_uniform_tail
#print axioms ScaleSpace.approxMeasure_tailSet
#print axioms ScaleSpace.isTightMeasureSet_approxMeasure
#print axioms ScaleSpace.exists_weak_limit
#print axioms ScaleSpace.integral_approxMeasure
#print axioms ScaleSpace.apply_eq_integral_pairTrans
#print axioms ScaleSpace.exists_isProbabilityMeasure_eq_mconvL1
#print axioms ScaleSpace.eq_mconvL1_of_ae
#print axioms ScaleSpace.existsUnique_repr_of_operator
#print axioms ScaleSpace.reflL1_reflL1
#print axioms ScaleSpace.mconvL1_map_neg
#print axioms ScaleSpace.isSymmetric_of_reflL1
#print axioms ScaleSpace.representation_existsUnique
-- Nonvanishing: `lem:nonvanishing`: the transforms of the kernels never vanish
#print axioms ScaleSpace.Phi_eq_mconvL1
#print axioms ScaleSpace.isSymmetric_kernel
#print axioms ScaleSpace.kernel_conv
#print axioms ScaleSpace.kernel_diag
#print axioms ScaleSpace.fourierCos_kernel_mul
#print axioms ScaleSpace.continuousOn_fourierCos_kernel
#print axioms ScaleSpace.nonvanishing
-- Pairing: Pairing a test function against `mconv`, and the measure it determines
#print axioms ScaleSpace.fourierSin
#print axioms ScaleSpace.fourierSin_apply
#print axioms ScaleSpace.charFun_eq
#print axioms ScaleSpace.integral_odd_eq_zero
#print axioms ScaleSpace.integrable_cos_mul_self
#print axioms ScaleSpace.integrable_sin_mul_self
#print axioms ScaleSpace.integral_sin_mul_eq_zero
#print axioms ScaleSpace.integral_cos_mul_translate
#print axioms ScaleSpace.integral_sin_mul_translate
#print axioms ScaleSpace.integral_cos_mul_mconv
#print axioms ScaleSpace.integral_sin_mul_mconv
#print axioms ScaleSpace.gaussTest
#print axioms ScaleSpace.measurable_gaussTest
#print axioms ScaleSpace.integrable_gaussTest
#print axioms ScaleSpace.gaussTest_even
#print axioms ScaleSpace.integral_cos_mul_gaussTest
#print axioms ScaleSpace.integral_cos_mul_gaussTest_pos
#print axioms ScaleSpace.eq_of_mconv_gaussTest_ae
#print axioms ScaleSpace.coeFn_gaussL1_gaussTest
-- Cascade: The kernels of a cascade family, and the positivity of their transforms
#print axioms ScaleSpace.exists_kernelFamily
#print axioms ScaleSpace.kernel_symmetric
#print axioms ScaleSpace.kernel_ne_dirac
#print axioms ScaleSpace.fourierCos_kernel_diag
#print axioms ScaleSpace.fourierCos_kernel_mul_comm
#print axioms ScaleSpace.continuousOn_fourierCos_kernel_zero
#print axioms ScaleSpace.kernel_transform_pos
-- Additivity: `lem:additivity`: the cascade, at the level of measures and of exponents
#print axioms ScaleSpace.abs_fourierCos_le_one
#print axioms ScaleSpace.exponent_add
#print axioms ScaleSpace.exponent_self
#print axioms ScaleSpace.exponent_nonneg
#print axioms ScaleSpace.exponent_eq_sub
#print axioms ScaleSpace.continuousOn_exponent
#print axioms ScaleSpace.continuous_exponent
#print axioms ScaleSpace.exponent_atZero
-- Transmittance: `cor:smoothed-transmittance`: one strictly monotone number per scale
#print axioms ScaleSpace.gaussTest_apply
#print axioms ScaleSpace.gaussTest_pos
#print axioms ScaleSpace.continuous_gaussTest
#print axioms ScaleSpace.integral_fourierCos_mul_gaussTest
#print axioms ScaleSpace.strictAntiOn_transmittance
-- Covariance: `lem:covariance-fourier`: (A8) as an identity of measures and of exponents
#print axioms ScaleSpace.mconv_map_mul
#print axioms ScaleSpace.dilate_dilate
#print axioms ScaleSpace.dilate_one
#print axioms ScaleSpace.dilate_inv_dilate
#print axioms ScaleSpace.dilate_dilate_inv
#print axioms ScaleSpace.fourierCos_map_mul
#print axioms ScaleSpace.map_mul_kernel_of_covariant
#print axioms ScaleSpace.isScaleCovariant_of_map_mul
#print axioms ScaleSpace.map_mul_kernel_of_exponent
#print axioms ScaleSpace.covariance_fourier
#print axioms ScaleSpace.covariance_similarity
-- DilationAtom: `lem:dilation-invariance` and `lem:dilation-atom`: the two elementary dilation facts
#print axioms ScaleSpace.dilation_atom
-- Rigidity: `lem:action-rigidity`: the relabellings are unique, compose, are continuous, and move
#print axioms ScaleSpace.fourierCos_similarity
#print axioms ScaleSpace.action_rigidity_injective
#print axioms ScaleSpace.action_rigidity_group
#print axioms ScaleSpace.action_rigidity_no_fixed_point
#print axioms ScaleSpace.transmittance_similarity
#print axioms ScaleSpace.continuous_transmittance_orbit
#print axioms ScaleSpace.action_rigidity_continuous
-- Gauge: `prop:canonical-gauge`, the orbit coordinate
#print axioms ScaleSpace.lt_S_of_one_lt
#print axioms ScaleSpace.S_strictMonoOn_ratio
#print axioms ScaleSpace.canonical_gauge_orbit
#print axioms ScaleSpace.canonical_gauge_of_levy
-- Truncation: The two elementary inequalities of `thm:increments-levy`
#print axioms ScaleSpace.one_sub_exp_neg_le
#print axioms ScaleSpace.sub_one_sub_exp_neg_le
#print axioms ScaleSpace.sub_sin_eq_intervalIntegral
#print axioms ScaleSpace.one_sub_sinc_ge_of_le_pi
#print axioms ScaleSpace.one_sub_sinc_ge
-- NullArray: `thm:increments-levy`, part one: the null-array estimate
#print axioms ScaleSpace.part
#print axioms ScaleSpace.part_zero
#print axioms ScaleSpace.part_self
#print axioms ScaleSpace.part_le_succ
#print axioms ScaleSpace.part_mem_Icc
#print axioms ScaleSpace.part_nonneg
#print axioms ScaleSpace.part_succ_sub
#print axioms ScaleSpace.isProbabilityMeasure_part
#print axioms ScaleSpace.sum_exponent_part
#print axioms ScaleSpace.partitionMeasure
#print axioms ScaleSpace.isFiniteMeasure_partitionMeasure
#print axioms ScaleSpace.integral_partitionMeasure_eq_sum
#print axioms ScaleSpace.integral_partitionMeasure
#print axioms ScaleSpace.abs_sub_integral_partitionMeasure_le
#print axioms ScaleSpace.exists_partition_increment_le
#print axioms ScaleSpace.tendsto_integral_partitionMeasure
-- Tightness: `thm:increments-levy`, part two: the truncation inequality
#print axioms ScaleSpace.integrable_sinc_mul
#print axioms ScaleSpace.intervalIntegral_fourierCos_eq
#print axioms ScaleSpace.integral_one_sub_sinc_le
#print axioms ScaleSpace.meanExponent
#print axioms ScaleSpace.continuous_exponent_pair
#print axioms ScaleSpace.meanExponent_nonneg
#print axioms ScaleSpace.integral_one_sub_sinc_partitionMeasure_le
#print axioms ScaleSpace.exponent_pair_atZero
#print axioms ScaleSpace.exists_meanExponent_le
#print axioms ScaleSpace.tendsto_meanExponent
-- LevyExtraction: `thm:increments-levy`, part three: the test function and the limiting pair
#print axioms ScaleSpace.levyTest
#print axioms ScaleSpace.continuous_levyTest
#print axioms ScaleSpace.levyTest_zero
#print axioms ScaleSpace.levyTest_mul_min
#print axioms ScaleSpace.levyTest_nonneg
#print axioms ScaleSpace.levyTest_le
#print axioms ScaleSpace.levyTestBdd
#print axioms ScaleSpace.levyTestBdd_apply
#print axioms ScaleSpace.eq_of_mapClusterPt
#print axioms ScaleSpace.foldedPartition
#print axioms ScaleSpace.weightedPartition
#print axioms ScaleSpace.isFiniteMeasure_foldedPartition
#print axioms ScaleSpace.isFiniteMeasure_weightedPartition
#print axioms ScaleSpace.weightedPartition_le_foldedPartition
#print axioms ScaleSpace.integral_levyTest_weightedPartition
#print axioms ScaleSpace.measureReal_weightedPartition_univ_le
#print axioms ScaleSpace.measureReal_weightedPartition_compl_le
#print axioms ScaleSpace.finiteMeasure_apply_coe
#print axioms ScaleSpace.exists_limit_measure
-- Increments: `thm:increments-levy`: every increment exponent is a symmetric Lévy exponent
#print axioms ScaleSpace.limitLevyMeasure
#print axioms ScaleSpace.measurable_weightInv
#print axioms ScaleSpace.isFolded_limitLevyMeasure
#print axioms ScaleSpace.lintegral_limitLevyMeasure
#print axioms ScaleSpace.weightInv_mul_ofReal
#print axioms ScaleSpace.isSymLevyExponent_of_limit_measure
#print axioms ScaleSpace.increments_levy
-- GaugeLevy: `prop:canonical-gauge`, closed
#print axioms ScaleSpace.canonical_gauge
-- LineInterfaces: The cited interfaces of the line classification, as hypotheses
#print axioms ScaleSpace.SymLevyUnique
#print axioms ScaleSpace.SymLevyConverse
#print axioms ScaleSpace.BochnerSymm
#print axioms ScaleSpace.LineLawInterfaces
-- SDExponents: `lem:selfdecomposable-exponents`, (3) ⟹ (1): the dilation increments
#print axioms ScaleSpace.incrementProfile
#print axioms ScaleSpace.profileJumpL
#print axioms ScaleSpace.SDProfile.exponentL_eq_add_jump
#print axioms ScaleSpace.aemeasurable_profileJump_integrand
#print axioms ScaleSpace.antitoneOn_comp_div
#print axioms ScaleSpace.profileJumpL_comp_div
#print axioms ScaleSpace.lintegral_profileMeasure
#print axioms ScaleSpace.lintegral_one_sub_cos_profileMeasure
#print axioms ScaleSpace.min_one_sq_mul_le
#print axioms ScaleSpace.lintegral_min_profileMeasure_comp_div_ne_top
#print axioms ScaleSpace.incrementProfile_nonneg
#print axioms ScaleSpace.incrementProfile_le
#print axioms ScaleSpace.aemeasurable_incrementProfile
#print axioms ScaleSpace.profileJumpL_add_increment
#print axioms ScaleSpace.sd_increment_pair
#print axioms ScaleSpace.sd_dilate_pair
#print axioms ScaleSpace.sd_increment_isSymLevyExponent
-- DilationDecrease: The dilation identity read backwards
#print axioms ScaleSpace.symLevyPair_dilate
#print axioms ScaleSpace.symLevyPair_add
#print axioms ScaleSpace.dilate_le_of_increments
-- AntitoneDensity: A translation-decreasing measure has a nonincreasing density
#print axioms ScaleSpace.measure_Ioc_shift_le
#print axioms ScaleSpace.measure_Ioc_double_le
#print axioms ScaleSpace.tonelli_window
#print axioms ScaleSpace.two_pow_mul_ofReal_half_pow
#print axioms ScaleSpace.sandwich_upper
#print axioms ScaleSpace.sandwich_lower
#print axioms ScaleSpace.sigmaFinite_of_measure_Ioi_ne_top
#print axioms ScaleSpace.dyadicTerm
#print axioms ScaleSpace.dyadicDensity
#print axioms ScaleSpace.antitone_dyadicTerm
#print axioms ScaleSpace.measurable_dyadicTerm
#print axioms ScaleSpace.monotone_dyadicTerm
#print axioms ScaleSpace.antitone_dyadicDensity
#print axioms ScaleSpace.setLIntegral_dyadicTerm
#print axioms ScaleSpace.dyadicTerm_integral_lower
#print axioms ScaleSpace.dyadicTerm_integral_upper
#print axioms ScaleSpace.tendsto_half_pow
#print axioms ScaleSpace.antitone_half_pow
#print axioms ScaleSpace.setLIntegral_dyadicDensity
#print axioms ScaleSpace.eq_withDensity_dyadicDensity
-- AnalysisDirection: The analysis direction of `lem:selfdecomposable-exponents`
#print axioms ScaleSpace.SymLevyPair.measure_Ioi_ne_top
#print axioms ScaleSpace.measure_eq_of_inter_Ioi
#print axioms ScaleSpace.map_log_Ioi
#print axioms ScaleSpace.map_log_shift
#print axioms ScaleSpace.map_exp_withDensity
#print axioms ScaleSpace.dyadicDensity_ne_top
#print axioms ScaleSpace.exists_profile_of_dilate_le
#print axioms ScaleSpace.sd_exponents_one_implies_three
-- MainConstruction: `thm:main-characterization`, the construction direction
#print axioms ScaleSpace.exists_isSymmetric_of_isSymLevyExponent
#print axioms ScaleSpace.ConstructionData
#print axioms ScaleSpace.ConstructionData.chi_pos
#print axioms ScaleSpace.ConstructionData.chi_nonneg
#print axioms ScaleSpace.ConstructionData.chi_mapsTo
#print axioms ScaleSpace.ConstructionData.chi_le
#print axioms ScaleSpace.ConstructionData.chi_continuousOn
#print axioms ScaleSpace.ConstructionData.expo
#print axioms ScaleSpace.ConstructionData.expo_isSymLevyExponent
#print axioms ScaleSpace.ConstructionData.expo_self
#print axioms ScaleSpace.ConstructionData.expo_add
#print axioms ScaleSpace.ConstructionData.kernel
#print axioms ScaleSpace.ConstructionData.kernel_prob
#print axioms ScaleSpace.ConstructionData.instIsProbabilityMeasureKernel
#print axioms ScaleSpace.ConstructionData.kernel_sym
#print axioms ScaleSpace.ConstructionData.fourierCos_kernel
#print axioms ScaleSpace.ConstructionData.charFun_kernel
#print axioms ScaleSpace.ConstructionData.kernel_self
#print axioms ScaleSpace.ConstructionData.kernel_conv
#print axioms ScaleSpace.ConstructionData.cos_continuousOn
#print axioms ScaleSpace.ConstructionData.kernel_ne_dirac
#print axioms ScaleSpace.ConstructionData.chiInv
#print axioms ScaleSpace.ConstructionData.chiInv_spec
#print axioms ScaleSpace.ConstructionData.chiInv_chi
#print axioms ScaleSpace.ConstructionData.gaugeAction
#print axioms ScaleSpace.ConstructionData.gaugeAction_nonneg
#print axioms ScaleSpace.ConstructionData.chi_gaugeAction
#print axioms ScaleSpace.ConstructionData.gaugeAction_strictMonoOn
#print axioms ScaleSpace.ConstructionData.gaugeAction_surjOn
#print axioms ScaleSpace.ConstructionData.kernel_map_const_mul
#print axioms ScaleSpace.ConstructionData.cascadeData
#print axioms ScaleSpace.main_construction
-- MainAnalysis: `thm:main-characterization`, the analysis and uniqueness directions
#print axioms ScaleSpace.main_uniqueness
#print axioms ScaleSpace.fourierCos_eq_exp_neg_exponent
#print axioms ScaleSpace.isSymLevyExponent_dilate_diff
#print axioms ScaleSpace.main_analysis_of_profileForm
#print axioms ScaleSpace.main_analysis
#print axioms ScaleSpace.main_analysis_exists
-- L1OperatorsSpace (Q-0332, SSL-5)
#print axioms ScaleSpace.IsNonnegE
#print axioms ScaleSpace.measurePreserving_sub_constE
#print axioms ScaleSpace.translate_congr_aeE
#print axioms ScaleSpace.integrable_translateE
#print axioms ScaleSpace.transₗE
#print axioms ScaleSpace.transL1E
#print axioms ScaleSpace.coeFn_transL1E
#print axioms ScaleSpace.norm_transL1E_le
#print axioms ScaleSpace.eq_transL1E_iff
#print axioms ScaleSpace.transL1E_zero
#print axioms ScaleSpace.transL1E_comp
#print axioms ScaleSpace.isNonnegE_transL1E
#print axioms ScaleSpace.det_ne_zeroE
#print axioms ScaleSpace.dilateE
#print axioms ScaleSpace.dilateE_apply
#print axioms ScaleSpace.homothety
#print axioms ScaleSpace.homothety_apply
#print axioms ScaleSpace.homothety_symm_apply
#print axioms ScaleSpace.det_homothety
#print axioms ScaleSpace.abs_det_neg
#print axioms ScaleSpace.det_refl
#print axioms ScaleSpace.map_symm_volumeE
#print axioms ScaleSpace.quasiMeasurePreserving_symmE
#print axioms ScaleSpace.lintegral_comp_symmE
#print axioms ScaleSpace.dilateE_congr_ae
#print axioms ScaleSpace.integrable_dilateE
#print axioms ScaleSpace.dilₗE
#print axioms ScaleSpace.lintegral_enorm_dilateE
#print axioms ScaleSpace.dilL1E
#print axioms ScaleSpace.coeFn_dilL1E
#print axioms ScaleSpace.eq_dilL1E_iff
#print axioms ScaleSpace.norm_dilL1E
#print axioms ScaleSpace.dilL1E_refl
#print axioms ScaleSpace.dilL1E_comp
#print axioms ScaleSpace.dilL1E_symm_comp
#print axioms ScaleSpace.dilL1E_comp_symm
#print axioms ScaleSpace.dilL1EEquiv
#print axioms ScaleSpace.dilL1EEquiv_apply
#print axioms ScaleSpace.dilL1EEquiv_symm_apply
#print axioms ScaleSpace.dilL1E_comp_transL1E
#print axioms ScaleSpace.isNonnegE_dilL1E
#print axioms ScaleSpace.integral_dilL1E
#print axioms ScaleSpace.coeFn_dilL1E_of_abs_det_eq_one
#print axioms ScaleSpace.coeFn_dilL1E_homothety
#print axioms ScaleSpace.measurePreserving_negE
#print axioms ScaleSpace.reflect_congr_aeE
#print axioms ScaleSpace.integrable_reflectE
#print axioms ScaleSpace.reflₗE
#print axioms ScaleSpace.reflL1E
#print axioms ScaleSpace.coeFn_reflL1E
#print axioms ScaleSpace.reflL1E_eq_dilL1E
#print axioms ScaleSpace.mconvE
#print axioms ScaleSpace.mconvE_apply
#print axioms ScaleSpace.lintegral_lintegral_sub_eqE
#print axioms ScaleSpace.lintegral_enorm_mconv_leE
#print axioms ScaleSpace.integrable_uncurry_subE
#print axioms ScaleSpace.integrable_mconvE
#print axioms ScaleSpace.ae_ae_sub_of_aeE
#print axioms ScaleSpace.mconvE_congr_ae
#print axioms ScaleSpace.mconvE_add_ae
#print axioms ScaleSpace.mconvE_smul
#print axioms ScaleSpace.mconvₗE
#print axioms ScaleSpace.mconvL1E
#print axioms ScaleSpace.coeFn_mconvL1E
#print axioms ScaleSpace.eq_mconvL1E_iff
#print axioms ScaleSpace.mconvE_comp_sub
#print axioms ScaleSpace.integral_mconvE
#print axioms ScaleSpace.mconvE_conv
#print axioms ScaleSpace.mconvE_dirac_zero
#print axioms ScaleSpace.mconvL1E_congr
#print axioms ScaleSpace.norm_mconvL1E_le
#print axioms ScaleSpace.mconvL1E_transL1E
#print axioms ScaleSpace.isNonnegE_mconvL1E
#print axioms ScaleSpace.integral_mconvL1E
#print axioms ScaleSpace.mconvL1E_comp
#print axioms ScaleSpace.mconvL1E_dirac_zero
#print axioms ScaleSpace.dilateE_mconvE
#print axioms ScaleSpace.dilL1E_comp_mconvL1E
#print axioms ScaleSpace.dilL1E_conj_mconvL1E
#print axioms ScaleSpace.intertwines_iff_dilL1E
#print axioms ScaleSpace.translation_iff_transL1E
#print axioms ScaleSpace.transL1E_real
#print axioms ScaleSpace.reflL1E_real
#print axioms ScaleSpace.mconvL1E_real
#print axioms ScaleSpace.mconvE_real
#print axioms ScaleSpace.dilateE_homothety_real
#print axioms ScaleSpace.dilL1E_homothety_real
#print axioms ScaleSpace.isNonnegE_real
-- BochnerConvolutionSpace (Q-0332, SSL-5)
#print axioms ScaleSpace.subCME
#print axioms ScaleSpace.subCME_apply
#print axioms ScaleSpace.measurePreserving_subCME
#print axioms ScaleSpace.transL1E_eq
#print axioms ScaleSpace.continuous_transL1E
#print axioms ScaleSpace.bconvE
#print axioms ScaleSpace.integrable_smul_transL1E
#print axioms ScaleSpace.map_bconvE
#print axioms ScaleSpace.setIntegralCLME
#print axioms ScaleSpace.setIntegralCLME_apply
#print axioms ScaleSpace.integrable_uncurry_pconvE
#print axioms ScaleSpace.integrable_pconvE
#print axioms ScaleSpace.coeFn_bconvE
#print axioms ScaleSpace.integrable_transL1E
#print axioms ScaleSpace.bconvME
#print axioms ScaleSpace.bconvME_eq_mconvL1E
#print axioms ScaleSpace.apply_mconvL1E_general
#print axioms ScaleSpace.pairTransE
#print axioms ScaleSpace.pairTransE_apply
#print axioms ScaleSpace.apply_mconvL1E
#print axioms ScaleSpace.apply_bconvE
#print axioms ScaleSpace.eq_dirac_of_mconvL1E_eq_id
#print axioms ScaleSpace.bconvE_real
#print axioms ScaleSpace.bconvME_real
-- L1OperatorsEuclidean (Q-0332, SSL-5)
#print axioms ScaleSpace.matEquiv
#print axioms ScaleSpace.matEquiv_apply
#print axioms ScaleSpace.matEquiv_symm_apply
#print axioms ScaleSpace.det_matEquiv
#print axioms ScaleSpace.matEquiv_mul
#print axioms ScaleSpace.coeFn_dilL1E_matEquiv
#print axioms ScaleSpace.eq_dilL1E_matEquiv_iff
#print axioms ScaleSpace.intertwines_iff_dilL1E_matEquiv
#print axioms ScaleSpace.dilL1E_matEquiv_comp
#print axioms ScaleSpace.abs_det_of_transpose_mul_self
#print axioms ScaleSpace.isUnit_det_of_transpose_mul_self
#print axioms ScaleSpace.coeFn_dilL1E_matEquiv_orthogonal
#print axioms ScaleSpace.matEquiv_smul_one
-- L1ContinuitySpace (Q-0332, SSL-5)
#print axioms ScaleSpace.transDiffE
#print axioms ScaleSpace.continuous_transDiffE
#print axioms ScaleSpace.transDiffE_nonneg
#print axioms ScaleSpace.transDiffE_zero
#print axioms ScaleSpace.transDiffE_le
#print axioms ScaleSpace.integrable_transDiffE
#print axioms ScaleSpace.norm_mconvL1E_sub_le
#print axioms ScaleSpace.transDiffE_mconvL1E_le
#print axioms ScaleSpace.norm_mconvL1E_comp_sub_le
#print axioms ScaleSpace.transDiffBCFE
#print axioms ScaleSpace.transDiffBCFE_apply
#print axioms ScaleSpace.transDiffE_real
#print axioms ScaleSpace.tendsto_integral_transDiffE_of_tendsto_charFun
#print axioms ScaleSpace.tendsto_norm_mconvL1E_sub_of_tendsto_charFun
-- FourierPairingSpace (Q-0332, SSL-5)
#print axioms ScaleSpace.integrable_char_mulE
#print axioms ScaleSpace.charCLME
#print axioms ScaleSpace.charCLME_apply
#print axioms ScaleSpace.charCLME_transL1E
#print axioms ScaleSpace.charCLME_mconvL1E
-- GammaMeasure (Q-0362)
#print axioms ScaleSpace.lintegral_gammaMeasure
#print axioms ScaleSpace.lintegral_gammaMeasure_rpow_mul_exp
#print axioms ScaleSpace.gammaMeasure_Iio_zero
#print axioms ScaleSpace.ae_pos_gammaMeasure

-- ConvPow (Q-0361): the `n`-fold convolution power of a measure
#print axioms ScaleSpace.convPow
#print axioms ScaleSpace.isFiniteMeasure_convPow
#print axioms ScaleSpace.isProbabilityMeasure_convPow_real
#print axioms ScaleSpace.isFiniteMeasure_convPow_Rd

-- PosSemidefSum (Q-0364): a real positive semidefinite matrix as a double sum and a positive definite kernel
#print axioms ScaleSpace.star_dotProduct_mulVec_eq_sum
#print axioms ScaleSpace.posSemidef_iff_sum
#print axioms ScaleSpace.sum_sum_mul
#print axioms ScaleSpace.sum_mul_conj_nonneg_of_posSemidef

-- LaplaceLaw (Q-0364): the Laplace law on the line
#print axioms ScaleSpace.laplaceDensity
#print axioms ScaleSpace.laplaceLaw
#print axioms ScaleSpace.laplaceDensity_nonneg
#print axioms ScaleSpace.continuous_laplaceDensity
#print axioms ScaleSpace.measurable_laplaceDensity
#print axioms ScaleSpace.integrableOn_laplaceDensity_Ioi
#print axioms ScaleSpace.integrableOn_laplaceDensity_Iic
#print axioms ScaleSpace.integrable_laplaceDensity
#print axioms ScaleSpace.expoDensity
#print axioms ScaleSpace.expoDensity_def
#print axioms ScaleSpace.expoDensity_nonneg
#print axioms ScaleSpace.integrable_expoDensity
#print axioms ScaleSpace.integral_expoDensity
#print axioms ScaleSpace.integrable_expoDensity_neg
#print axioms ScaleSpace.laplaceDensity_eq_half_add
#print axioms ScaleSpace.laplaceDensity_ae_eq
#print axioms ScaleSpace.integral_laplaceDensity
#print axioms ScaleSpace.isProbabilityMeasure_laplaceLaw

-- ExpIntegral (Q-0364): the integral of `e^{-cu}` over the half-line
#print axioms ScaleSpace.integrableOn_exp_neg_Ioi_zero
#print axioms ScaleSpace.lintegral_Ioi_exp_neg_mul

-- InverseGamma (Q-0363, SSL-8): the inverse-gamma integral and the inverse-gamma law
#print axioms ScaleSpace.inverse_gamma_integral
#print axioms ScaleSpace.expMap_image
#print axioms ScaleSpace.expMap_monotone
#print axioms ScaleSpace.expMap_hasDeriv
#print axioms ScaleSpace.lintegral_Ioi_comp_exp
#print axioms ScaleSpace.exp_rpow
#print axioms ScaleSpace.lintegral_Ioi_inverseGammaKernel
#print axioms ScaleSpace.inverseGammaDensity
#print axioms ScaleSpace.inverseGammaLaw
#print axioms ScaleSpace.measurable_inverseGammaDensity
#print axioms ScaleSpace.inverseGammaDensity_nonneg
#print axioms ScaleSpace.inverseGammaDensity_eq_indicator
#print axioms ScaleSpace.inverseGammaLaw_Iio_zero
#print axioms ScaleSpace.isProbabilityMeasure_inverseGammaLaw

-- StudentTransform (Q-0363, SSL-8): the Student-t law as a Gaussian variance mixture
#print axioms ScaleSpace.besselK
#print axioms ScaleSpace.studentDensity
#print axioms ScaleSpace.studentLaw
#print axioms ScaleSpace.lintegral_exp_mul_of_even
#print axioms ScaleSpace.inverseGamma_brownian_integrand
#print axioms ScaleSpace.integral_inverseGamma_brownian
#print axioms ScaleSpace.studentDensity_pos
#print axioms ScaleSpace.lintegral_inverseGamma_brownian
#print axioms ScaleSpace.bridge_families_bessel
#print axioms ScaleSpace.lintegral_Ioi_rpow_exp_besselKernel
#print axioms ScaleSpace.lintegral_cosh_exp_eq_besselK
#print axioms ScaleSpace.besselK_neg
#print axioms ScaleSpace.besselK_nonneg
#print axioms ScaleSpace.lintegral_exp_neg_inverseGammaLaw
#print axioms ScaleSpace.student_transform
