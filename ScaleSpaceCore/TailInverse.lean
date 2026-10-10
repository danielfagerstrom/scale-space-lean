/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.Normed.Group.Basic

/-!
# The generalised inverse of a nonincreasing tail function

Home: none (standard analysis in Mathlib's types: pure order theory and real analysis, not
article-specific in any sense, per the module's own prose; ref: @resnick1987extreme, §0.2, p. 3)

Slice 4 of E-0009 (hub `proposals/E-0009.md`), moved from Paper I's `Subordinator.lean` and
Paper V's `SpatialLine/CinRays.lean`, where it was proved identically in both articles
(`offices/engineer/notes/2026-09-19-lean-duplication-survey.md` §§ 3, 6). Pure order theory and
real analysis, no measure theory: a generalised inverse of an antitone function on a half-line is
not article-specific in any sense, and both articles use it to build a Choquet measure whose
tails realise a given nonincreasing profile.

## References

* @resnick1987extreme, §0.2, p. 3: the (left-continuous) generalised inverse of a monotone
  function, `H^←(y) = inf{s : H(s) ≥ y}` with `inf ∅ = +∞` — `tailInv h y = sup{u > 0 : y < h u}`
  is the same construction for an antitone `h`, with the sign and the half-line domain flipped.
-/

namespace ScaleSpace

open Set Filter Topology

/-- The generalised inverse of a nonincreasing `h`: `tailInv h y = sup {u > 0 : h u > y}`. -/
noncomputable def tailInv (h : ℝ → ℝ) (y : ℝ) : ℝ := sSup {u : ℝ | 0 < u ∧ y < h u}

variable {h : ℝ → ℝ}

theorem tailInv_nonneg (y : ℝ) : 0 ≤ tailInv h y := by
  rcases eq_empty_or_nonempty {u : ℝ | 0 < u ∧ y < h u} with he | ⟨u, hu⟩
  · rw [tailInv, he, Real.sSup_empty]
  · by_cases hbd : BddAbove {u : ℝ | 0 < u ∧ y < h u}
    · exact le_trans hu.1.le (le_csSup hbd hu)
    · rw [tailInv, Real.sSup_of_not_bddAbove hbd]

theorem bddAbove_tailSet (htend : Tendsto h atTop (𝓝 0)) {y : ℝ} (hy : 0 < y) :
    BddAbove {u : ℝ | 0 < u ∧ y < h u} := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp (htend.eventually_lt_const hy)
  refine ⟨M, fun u hu => ?_⟩
  by_contra hc
  exact absurd (hM u (le_of_lt (not_le.mp hc))) (not_lt.mpr hu.2.le)

theorem lt_of_lt_tailInv (hmono : AntitoneOn h (Ioi 0))
    {y r : ℝ} (hr : 0 < r) (hlt : r < tailInv h y) : y < h r := by
  have hne : {u : ℝ | 0 < u ∧ y < h u}.Nonempty := by
    rcases eq_empty_or_nonempty {u : ℝ | 0 < u ∧ y < h u} with he | hne
    · rw [tailInv, he, Real.sSup_empty] at hlt; linarith
    · exact hne
  obtain ⟨u, hu, hru⟩ := exists_lt_of_lt_csSup hne hlt
  exact lt_of_lt_of_le hu.2 (hmono (mem_Ioi.mpr hr) (mem_Ioi.mpr hu.1) hru.le)

theorem lt_tailInv_of_lt (htend : Tendsto h atTop (𝓝 0)) {y u r : ℝ} (hy : 0 < y) (hu : 0 < u)
    (hru : r < u) (hlt : y < h u) : r < tailInv h y :=
  lt_of_lt_of_le hru (le_csSup (bddAbove_tailSet htend hy) ⟨hu, hlt⟩)

theorem antitoneOn_tailInv (htend : Tendsto h atTop (𝓝 0)) :
    AntitoneOn (tailInv h) (Ioi 0) := by
  intro y₁ h₁ y₂ h₂ h12
  rcases eq_empty_or_nonempty {u : ℝ | 0 < u ∧ y₂ < h u} with he | hne
  · rw [tailInv, he, Real.sSup_empty]; exact tailInv_nonneg _
  · exact csSup_le_csSup (bddAbove_tailSet htend (mem_Ioi.mp h₁)) hne
      (fun u hu => ⟨hu.1, lt_of_le_of_lt h12 hu.2⟩)

end ScaleSpace
