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
