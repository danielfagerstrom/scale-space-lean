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

-- DilationInvariance: a function fixed by one dilation is constant
#print axioms ScaleSpace.dilation_invariance
