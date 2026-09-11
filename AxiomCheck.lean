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
