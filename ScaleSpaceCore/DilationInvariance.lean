/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A function fixed by one dilation is constant

Home: line:lem:dilation-invariance

`lem:dilation-invariance` ([V, Lem. 6.3]), moved from Paper V's `SpatialLine/Dilation.lean`
(the public cone export `spatial-hemigroup-scale-space-cone`, tag `v0.1`) and second demand now:
Paper V uses it in the uniqueness clause of its classification, and Paper VII
(`spatial-hemigroup-affine`) in `thm:isotropic-classification`, `prop:isotropic-corner`,
`prop:similarity-ray-families`(3) and `prop:diagonal-ray-families`(5)
(`spatial-hemigroup-affine/records/formalization/SECOND-DEMAND.md` § 3 row V8; § 6, SSL-4). The
statement mentions only Mathlib types, so nothing here needs to become a hypothesis.
-/

namespace ScaleSpace

open Filter
open scoped Topology

/-- **`lem:dilation-invariance`.** A function fixed by one dilation and continuous at the
origin, where it vanishes, vanishes identically.

Continuity is asked **at `0` only**, which is all the iteration needs and all three uses supply. -/
theorem dilation_invariance (h : ℝ → ℝ) (hcont : ContinuousAt h 0) (hzero : h 0 = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≠ 1) (hinv : ∀ ω : ℝ, h ω = h (κ * ω)) :
    ∀ ω : ℝ, h ω = 0 := by
  -- The contracting case; the expanding case is reduced to it by inverting `κ`.
  have key : ∀ c : ℝ, 0 < c → c < 1 → (∀ ω : ℝ, h ω = h (c * ω)) → ∀ ω, h ω = 0 := by
    intro c hc hc1 hcinv ω
    have hiter : ∀ n : ℕ, h (c ^ n * ω) = h ω := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          have := hcinv (c ^ n * ω)
          rw [← ih, this]
          ring_nf
    have hlim : Tendsto (fun n : ℕ => c ^ n * ω) atTop (𝓝 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc1
      simpa using this.mul_const ω
    have h1 : Tendsto (fun n : ℕ => h (c ^ n * ω)) atTop (𝓝 (h 0)) := hcont.tendsto.comp hlim
    have h2 : Tendsto (fun n : ℕ => h (c ^ n * ω)) atTop (𝓝 (h ω)) := by
      simp only [hiter]
      exact tendsto_const_nhds
    have huniq := tendsto_nhds_unique h1 h2
    rw [← huniq, hzero]
  rcases lt_or_gt_of_ne hκ1 with hlt | hgt
  · exact key κ hκ hlt hinv
  · refine key κ⁻¹ (by positivity) (by rw [inv_lt_one_iff₀]; right; exact hgt) ?_
    intro ω
    have hstep := hinv (κ⁻¹ * ω)
    rw [← mul_assoc, mul_inv_cancel₀ hκ.ne', one_mul] at hstep
    exact hstep.symm

end ScaleSpace
