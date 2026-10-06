/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import ScaleSpaceCore.LevyExtraction
import ScaleSpaceCore.Exponent

/-!
# `thm:increments-levy`: every increment exponent is a symmetric Lévy exponent

Blueprint: `blueprint/src/parts/05-cascade.tex`, `thm:increments-levy`.

`LevyExtraction` produced a finite measure `ϱ` on `[0,∞)` with

  `∫ k_ω dϱ = g_{s,t}(ω)` for every `ω`,  `k_ω(x) = (1 - cos ωx)/(1 ∧ x²)`, `k_ω(0) = ω²/2`.

What is left is the last paragraph of the blueprint's proof: read `ϱ` in two pieces, the atom at
the origin and the rest. The atom is the Gaussian coefficient — that is what filling the
removable singularity of `k_ω` bought — and the rest, divided back by the weight, is the Lévy
measure:

  `a := ϱ(\{0\})/2`,  `ν := (1 ∧ x²)^{-1}\,ϱ|_{(0,∞)}`,

for which `∫ (1 ∧ x²)\,dν = ϱ((0,∞)) < ∞` and `a ω² + ∫ (1 - \cos ωx)\,dν(x) = ∫ k_ω\,dϱ`. There
is no atom at infinity to exclude, because tightness has already forbidden it, and
correspondingly no killing term — the point at which the spatial argument differs from the
causal one, where the killing term is admitted by the compactification and excluded afterwards.

## Infinite divisibility

The last sentence of the node is stated at the transform, because Mathlib has no convolution
power of measures. It is the only place in Chapter 5 where the trust boundary is spent: the
`n`-th root of `\hat\mu_{s,t}` is the transform of a probability measure because the pair
`(a/n, ν/n)` is again a symmetric Lévy pair, and that is `prop:fourier-toolbox`(3)'s converse
together with (1) — ledger **A1** and **A3**.

twin: `Hemigroup.CascadeCore.exponent_hasLevyRep` (`Hemigroup/LevyTriple.lean`).

## Provenance

Moved by Q-0305 from Paper V's `SpatialLine/Increments.lean` (the public cone export,
`cone-v0.1`, commit `f28c066e`) for the line classification (`MainAnalysis`,
`MainConstruction`): only the declarations those theorems reach, with statements and
proofs unchanged up to the namespace. Blueprint labels are Paper V's.
-/

namespace ScaleSpace

open MeasureTheory Set Filter
open scoped ENNReal Topology NNReal

/-! ## The split of the limit measure at the origin -/

/-- The Lévy measure read off the limit measure: the weight `1 ∧ x²` divided back out, on
`(0,∞)`. -/
noncomputable def limitLevyMeasure (ϱ : Measure ℝ) : Measure ℝ :=
  (ϱ.restrict (Ioi 0)).withDensity fun x => ENNReal.ofReal (min 1 (x ^ 2))⁻¹

lemma measurable_weightInv : Measurable fun x : ℝ => ENNReal.ofReal (min 1 (x ^ 2))⁻¹ := by
  fun_prop

/-- The Lévy measure is folded: it is carried by `(0,∞)`. -/
lemma isFolded_limitLevyMeasure (ϱ : Measure ℝ) : IsFolded (limitLevyMeasure ϱ) := by
  rw [IsFolded, limitLevyMeasure, withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  have hempty : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iic, Set.mem_empty_iff_false, iff_false,
      not_and, not_lt]
    exact fun h => h
  rw [hempty, Measure.restrict_empty, lintegral_zero_measure]

/-- An integral against the Lévy measure is an integral against `ϱ` on `(0,∞)`, with the weight
divided out. -/
lemma lintegral_limitLevyMeasure (ϱ : Measure ℝ) {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ x, h x ∂(limitLevyMeasure ϱ)
      = ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (x ^ 2))⁻¹ * h x ∂ϱ := by
  rw [limitLevyMeasure, lintegral_withDensity_eq_lintegral_mul _ measurable_weightInv hh]
  rfl

/-- On `(0,∞)` the weight and its inverse cancel. -/
lemma weightInv_mul_ofReal {x : ℝ} (hx : 0 < x) (c : ℝ) :
    ENNReal.ofReal (min 1 (x ^ 2))⁻¹ * ENNReal.ofReal (min 1 (x ^ 2) * c)
      = ENNReal.ofReal c := by
  have hpos : 0 < min 1 (x ^ 2) := lt_min zero_lt_one (by positivity)
  rw [← ENNReal.ofReal_mul (by positivity), ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]

/-- **The split.** Every finite measure on `[0,∞)` whose pairing with the test function is a
given function `ψ` exhibits `ψ` as a symmetric Lévy exponent, with `a = ϱ(\{0\})/2` and
`ν = (1 ∧ x²)^{-1}ϱ|_{(0,∞)}`. -/
theorem isSymLevyExponent_of_limit_measure (ϱ : Measure ℝ) [IsFiniteMeasure ϱ]
    (hIio : ϱ (Iio 0) = 0) (ψ : ℝ → ℝ) (hψ : ∀ ω, ∫ x, levyTest ω x ∂ϱ = ψ ω) :
    IsSymLevyExponent ψ := by
  have hmeas : ∀ ω : ℝ, Measurable fun x : ℝ => ENNReal.ofReal (levyTest ω x) := fun ω =>
    ENNReal.measurable_ofReal.comp (continuous_levyTest ω).measurable
  -- the total pairing, as a lower integral
  have hsplit : ∀ ω : ℝ, ∫⁻ x, ENNReal.ofReal (levyTest ω x) ∂ϱ
      = ENNReal.ofReal (levyTest ω 0) * ϱ {(0 : ℝ)}
        + ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (levyTest ω x) ∂ϱ := by
    intro ω
    have hcompl : ∫⁻ x in (Ici (0 : ℝ))ᶜ, ENNReal.ofReal (levyTest ω x) ∂ϱ = 0 := by
      refine setLIntegral_measure_zero _ _ ?_
      rwa [compl_Ici]
    have htot : ∫⁻ x, ENNReal.ofReal (levyTest ω x) ∂ϱ
        = ∫⁻ x in Ici (0 : ℝ), ENNReal.ofReal (levyTest ω x) ∂ϱ := by
      rw [← lintegral_add_compl _ measurableSet_Ici, hcompl, add_zero]
    have hIci : Ici (0 : ℝ) = Ioi (0 : ℝ) ∪ {(0 : ℝ)} := (Ioi_union_left).symm
    rw [htot, hIci, lintegral_union (measurableSet_singleton (0 : ℝ))
      (by simp [Set.disjoint_singleton_right]), lintegral_singleton, add_comm]
  -- the pair
  have hnu : ∀ ω : ℝ, ∫⁻ x, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂(limitLevyMeasure ϱ)
      = ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (levyTest ω x) ∂ϱ := by
    intro ω
    have hmeas2 : Measurable fun x : ℝ => ENNReal.ofReal (1 - Real.cos (ω * x)) := by fun_prop
    rw [lintegral_limitLevyMeasure ϱ hmeas2]
    refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [← levyTest_mul_min ω x, mul_comm (levyTest ω x)]
    exact weightInv_mul_ofReal hx (levyTest ω x)
  have hfin : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(limitLevyMeasure ϱ) ≠ ⊤ := by
    rw [lintegral_limitLevyMeasure ϱ (by fun_prop)]
    have hone : ∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal (min 1 (x ^ 2))⁻¹ * ENNReal.ofReal (min 1 (x ^ 2)) ∂ϱ
        = ∫⁻ _ in Ioi (0 : ℝ), 1 ∂ϱ := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have := weightInv_mul_ofReal hx 1
      rwa [mul_one, ENNReal.ofReal_one] at this
    rw [hone, lintegral_one, Measure.restrict_apply_univ]
    exact (measure_lt_top ϱ _).ne
  refine ⟨⟨(ϱ {(0 : ℝ)}).toReal / 2, limitLevyMeasure ϱ, by positivity,
    isFolded_limitLevyMeasure ϱ, hfin⟩, fun ω => ?_⟩
  -- the exponent of the pair is `ψ`
  have hatom : ENNReal.ofReal ((ϱ {(0 : ℝ)}).toReal / 2 * ω ^ 2)
      = ENNReal.ofReal (levyTest ω 0) * ϱ {(0 : ℝ)} := by
    rw [levyTest_zero, show (ϱ {(0 : ℝ)}).toReal / 2 * ω ^ 2
        = (ϱ {(0 : ℝ)}).toReal * (ω ^ 2 / 2) by ring,
      ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (measure_ne_top ϱ _), mul_comm]
  have hexpL : (SymLevyPair.exponentL
      ⟨(ϱ {(0 : ℝ)}).toReal / 2, limitLevyMeasure ϱ, by positivity,
        isFolded_limitLevyMeasure ϱ, hfin⟩ ω)
      = ∫⁻ x, ENNReal.ofReal (levyTest ω x) ∂ϱ := by
    rw [SymLevyPair.exponentL, hatom, hnu ω, hsplit ω]
  rw [SymLevyPair.exponent, hexpL, ← hψ ω]
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => levyTest_nonneg ω x)
    (continuous_levyTest ω).aestronglyMeasurable

/-! ## The theorem -/

variable {Fam : PreCascadeCore} {μ : ℝ → ℝ → Measure ℝ} {s t : ℝ}

/-- **`thm:increments-levy`.** Every increment exponent is a symmetric Lévy exponent.

Reading: `g_{s,t} ∈ LEₛ` is `IsSymLevyExponent (exponent (μ s t))`, which is exactly "there are
`a(s,t) ≥ 0` and a folded `ν_{s,t}` with `∫(1 ∧ x²) ν < ∞` and `eq:increment-levy`". The
uniqueness of the pair is *not* asserted here: it is `prop:fourier-toolbox`(3), which the node's
own annotation identifies as what the toolbox supplies rather than what this theorem proves.

Class (b) — twin `Hemigroup.CascadeCore.exponent_hasLevyRep`, same null-array plan. Two
changes: the weight `1 - e^{-x}` becomes `1 ∧ x²`, and the compactification is replaced by the
truncation inequality of `Tightness`, because the test function
`(1 - cos ωx)/(1 ∧ x²)` oscillates at infinity and does not extend to a compactification. -/
theorem increments_levy (Fam : PreCascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hker : IsKernelFamily Fam.Φ μ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    IsSymLevyExponent (exponent (μ s t)) := by
  obtain ⟨ϱ, hfin, hIio, hpair⟩ := exists_limit_measure hker hs hst
  haveI := hfin
  exact isSymLevyExponent_of_limit_measure ϱ hIio _ hpair

end ScaleSpace
