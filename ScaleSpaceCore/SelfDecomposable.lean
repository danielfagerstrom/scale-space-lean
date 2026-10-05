/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Self-decomposable laws on a real vector space

A measure `μ` is **self-decomposable** if for every `c ∈ (0,1)` there is a probability measure
`ρ_c` (a *residual*) with `μ = (c •)_* μ ∗ ρ_c` (Sato, *Lévy Processes and Infinitely Divisible
Distributions*, § 15); it is **`B`-self-decomposable**, for a linear endomorphism `B`, if for every
`t > 0` there is a probability measure `ρ_t` with `μ = (e^{-tB})_* μ ∗ ρ_t` (Jurek–Mason's
`exp(-tQ)`-decomposability). The scalar notion is the case `B = 1`.

Second demand (SSL-3 of `spatial-hemigroup-affine`'s `records/formalization/SECOND-DEMAND.md`):
Paper V defines the notion on the line ([V, Def. 2.12], `SpatialLine.IsSelfDecomposable`), Paper VII
on `ℝ^d` and for operators. This module is the generalization, with the line as an instance
(`isSelfDecomposable_real_iff`, whose right-hand side is Paper V's definition verbatim), so that the
articles' copies can be deleted when they re-point. Proved from Mathlib alone.

## Main results

* `isSelfDecomposable_iff_charFun`: the transform form `μ̂(ξ) = μ̂(cξ) ρ̂_c(ξ)`, for a finite
  measure on a finite-dimensional real inner product space (Paper VII's form).
* `isSelfDecomposable_real_iff`: on `ℝ`, Sato's `b > 1` form `μ̂(ω) = μ̂(ω/b) ρ̂_b(ω)` (Paper V's).
* `isBSelfDecomposable_one_iff`: the scalar notion is operator self-decomposability at `B = 1`;
  `isBSelfDecomposable_iff_nonneg`: allowing `t = 0` changes nothing.
* `IsSelfDecomposable.map`: images under continuous linear maps, into another space.
* `IsSelfDecomposable.charFun_ne_zero`: the transform of a self-decomposable probability measure
  has no zeros, by the elementary argument of Paper VII's `prop:gw-ray-families`(1) (the first zero
  along a ray, and the doubling inequality `one_sub_norm_sq_charFun_two_smul_le`), without passing
  through infinite divisibility.

## Design

* **Generality.** The definitions read only the real vector space structure, `Measure.map` and
  `Measure.conv`, and are stated on a real normed space (the norm is what `NormedSpace.exp` on
  `E →L[ℝ] E` needs). The transform results are stated on a finite-dimensional real inner product
  space: `charFun` needs the inner product, and `Measure.ext_of_charFun` needs completeness and
  second countability, which finite dimension supplies. Both consumers' spaces, `ℝ` and
  `EuclideanSpace ℝ (Fin d)`, are instances. A topological group was not chosen: the dilations
  `c • ·` need real scalars.
* **Measure form, transform form as a lemma.** The definition is the convolution identity, the
  law-level reading of `X =d cX + R_c` with `R_c` independent of `X`; Sato's Definition 15.1 and
  both consumers state it on the transform side, and `isSelfDecomposable_iff_charFun` is the
  bridge, valid for finite measures. The measure form needs no inner product, and makes
  images a consequence of `Measure.map_conv_continuousLinearMap`.
* **The residual is an existential, not data.** It is unique only where the transform has no zeros,
  which is a theorem here (`charFun_ne_zero`), not something a definition should presuppose; both
  consumers quantify it existentially.
* **`μ` being a probability measure is not part of the definition**, as in both consumers, which
  carry `IsProbabilityMeasure μ` beside it; the results assume what they use.
* **`t > 0` in `IsBSelfDecomposable`**, as in Paper VII; the `t ≥ 0` form of ledger A5 is
  equivalent for s-finite `μ` (`isBSelfDecomposable_iff_nonneg`), the residual at `t = 0` being
  `δ₀`.

## Promotion

Self-decomposability is textbook (Sato § 15) and is stated here in Mathlib's vocabulary only
(`charFun`, `Measure.conv`, `Measure.map`, `NormedSpace.exp`). It is a candidate for the promotion
cycle into the Mathlib-quality library `harmonic-semigroups` (hub ADR-0026, Decision 3), together
with the Lévy–Khintchine form; the choice of generality above is provisional and belongs to that
cycle. The trunk holds the module meanwhile.
-/

namespace ScaleSpace

open MeasureTheory Filter Set
open scoped Topology RealInnerProductSpace

/-! ## The definitions -/

section Definitions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

/-- **Self-decomposability** (Sato § 15): for every `c ∈ (0,1)` there is a probability measure
`ρ_c` with `μ = (c •)_* μ ∗ ρ_c`. -/
def IsSelfDecomposable (μ : Measure E) : Prop :=
  ∀ c : ℝ, 0 < c → c < 1 → ∃ ρ : Measure E, IsProbabilityMeasure ρ ∧ μ = μ.map (c • ·) ∗ ρ

/-- **Operator self-decomposability**: for every `t > 0` there is a probability measure `ρ_t` with
`μ = (e^{-tB})_* μ ∗ ρ_t`. -/
def IsBSelfDecomposable (B : E →L[ℝ] E) (μ : Measure E) : Prop :=
  ∀ t : ℝ, 0 < t → ∃ ρ : Measure E, IsProbabilityMeasure ρ ∧
    μ = μ.map ⇑(NormedSpace.exp (-t • B) : E →L[ℝ] E) ∗ ρ

end Definitions

/-! ## The scalar case and `t = 0` -/

section Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `e^{-t·1} = e^{-t} •` on `E`. -/
theorem coe_exp_neg_smul_one (t : ℝ) :
    ⇑(NormedSpace.exp (-t • (1 : E →L[ℝ] E))) = (Real.exp (-t) • ·) := by
  rw [← Algebra.algebraMap_eq_smul_one, ← NormedSpace.algebraMap_exp_comm, ← Real.exp_eq_exp_ℝ,
    Algebra.algebraMap_eq_smul_one]
  funext x
  simp

variable [MeasurableSpace E]

/-- **The scalar notion is the case `B = 1`**: `c = e^{-t}`. -/
theorem isBSelfDecomposable_one_iff (μ : Measure E) :
    IsBSelfDecomposable (1 : E →L[ℝ] E) μ ↔ IsSelfDecomposable μ := by
  simp only [IsBSelfDecomposable, coe_exp_neg_smul_one]
  constructor
  · intro h c hc0 hc1
    have ht : 0 < -Real.log c := neg_pos.2 (Real.log_neg hc0 hc1)
    simpa [neg_neg, Real.exp_log hc0] using h _ ht
  · intro h t ht
    exact h _ (Real.exp_pos _) (by simpa using Real.exp_lt_exp.2 (by linarith : -t < 0))

variable [BorelSpace E] [SecondCountableTopology E]

/-- **Allowing `t = 0` changes nothing**: the residual at `t = 0` is `δ₀`. -/
theorem isBSelfDecomposable_iff_nonneg (B : E →L[ℝ] E) (μ : Measure E) [SFinite μ] :
    IsBSelfDecomposable B μ ↔ ∀ t : ℝ, 0 ≤ t → ∃ ρ : Measure E, IsProbabilityMeasure ρ ∧
      μ = μ.map ⇑(NormedSpace.exp (-t • B) : E →L[ℝ] E) ∗ ρ := by
  refine ⟨fun h t ht => ?_, fun h t ht => h t ht.le⟩
  rcases ht.eq_or_lt with rfl | ht
  · refine ⟨Measure.dirac 0, inferInstance, ?_⟩
    rw [neg_zero, zero_smul, NormedSpace.exp_zero, show ⇑(1 : E →L[ℝ] E) = id from rfl,
      Measure.map_id, Measure.conv_dirac_zero]
  · exact h t ht

end Operator

/-! ## Images under linear maps -/

section Images

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- **The image of a self-decomposable measure under a linear map is self-decomposable**, with
residual `L_* ρ_c`. -/
theorem IsSelfDecomposable.map {μ : Measure E} [SFinite μ] (h : IsSelfDecomposable μ)
    (L : E →L[ℝ] F) : IsSelfDecomposable (μ.map L) := by
  intro c hc0 hc1
  obtain ⟨ρ, hρ, hfac⟩ := h c hc0 hc1
  refine ⟨ρ.map L, Measure.isProbabilityMeasure_map L.continuous.aemeasurable, ?_⟩
  have hcomm : (L ∘ (c • ·)) = ((c • ·) ∘ L) := funext fun x => L.map_smul c x
  calc μ.map L = (μ.map (c • ·) ∗ ρ).map L := by rw [← hfac]
    _ = (μ.map (c • ·)).map L ∗ ρ.map L := Measure.map_conv_continuousLinearMap L
    _ = (μ.map L).map (c • ·) ∗ ρ.map L := by
      rw [Measure.map_map L.continuous.measurable (continuous_const_smul c).measurable,
        Measure.map_map (continuous_const_smul c).measurable L.continuous.measurable, hcomm]

end Images

/-! ## The transform form -/

section Transform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The transform form** `μ̂(ξ) = μ̂(cξ) ρ̂_c(ξ)`, for a finite measure (Paper VII's form). -/
theorem isSelfDecomposable_iff_charFun (μ : Measure E) [IsFiniteMeasure μ] :
    IsSelfDecomposable μ ↔ ∀ c : ℝ, 0 < c → c < 1 → ∃ ρ : Measure E, IsProbabilityMeasure ρ ∧
      ∀ ξ : E, charFun μ ξ = charFun μ (c • ξ) * charFun ρ ξ := by
  refine forall_congr' fun c => forall_congr' fun _ => forall_congr' fun _ =>
    exists_congr fun ρ => and_congr_right fun hρ => ?_
  constructor
  · intro h ξ
    conv_lhs => rw [h]
    rw [charFun_conv, charFun_map_smul]
  · intro h
    exact Measure.ext_of_charFun (funext fun ξ => by rw [charFun_conv, charFun_map_smul, h ξ])

/-- **The line as an instance**: on `ℝ`, self-decomposability is Sato's `b > 1` form
`μ̂(ω) = μ̂(ω/b) ρ̂_b(ω)`. The right-hand side is Paper V's `SpatialLine.IsSelfDecomposable`
([V, Def. 2.12]) verbatim, with `c = b⁻¹`. -/
theorem isSelfDecomposable_real_iff (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IsSelfDecomposable μ ↔ ∀ b : ℝ, 1 < b → ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
      ∀ ω : ℝ, charFun μ ω = charFun μ (ω / b) * charFun ρ ω := by
  rw [isSelfDecomposable_iff_charFun]
  constructor
  · intro h b hb
    obtain ⟨ρ, hρ, hfac⟩ := h b⁻¹ (inv_pos.2 (by linarith)) (inv_lt_one_of_one_lt₀ hb)
    exact ⟨ρ, hρ, fun ω => by rw [hfac ω, smul_eq_mul, div_eq_inv_mul]⟩
  · intro h c hc0 hc1
    obtain ⟨ρ, hρ, hfac⟩ := h c⁻¹ ((one_lt_inv₀ hc0).2 hc1)
    exact ⟨ρ, hρ, fun ω => by rw [hfac ω, smul_eq_mul, div_inv_eq_mul, mul_comm c ω]⟩

/-! ## The doubling inequality -/

omit [FiniteDimensional ℝ E] in
/-- The real part of a transform is the integral of the cosine. -/
theorem re_charFun_eq_integral_cos (ρ : Measure E) [IsProbabilityMeasure ρ] (η : E) :
    (charFun ρ η).re = ∫ x, Real.cos ⟪x, η⟫ ∂ρ := by
  have hintc : Integrable (fun x : E => Complex.exp (⟪x, η⟫ * Complex.I)) ρ :=
    Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (Eventually.of_forall fun x => by rw [Complex.norm_exp_ofReal_mul_I])
  rw [charFun_apply, ← RCLike.re_to_complex, ← integral_re hintc]
  simp [Complex.exp_ofReal_mul_I_re]

omit [FiniteDimensional ℝ E] in
/-- **The doubling inequality for a real part**: `1 - Re κ̂(2ξ) ≤ 4(1 - Re κ̂(ξ))`, from
`1 - cos 2τ ≤ 4(1 - cos τ)` under the integral. -/
theorem one_sub_re_charFun_two_smul_le (κ : Measure E) [IsProbabilityMeasure κ] (ξ : E) :
    1 - (charFun κ ((2 : ℝ) • ξ)).re ≤ 4 * (1 - (charFun κ ξ).re) := by
  have hint : ∀ η : E, Integrable (fun x : E => Real.cos ⟪x, η⟫) κ := fun η =>
    Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  rw [re_charFun_eq_integral_cos, re_charFun_eq_integral_cos]
  have h1 : (1 : ℝ) = ∫ _x, (1 : ℝ) ∂κ := by simp
  rw [h1, ← integral_sub (integrable_const 1) (hint _), ← integral_sub (integrable_const 1)
    (hint _), ← integral_const_mul]
  apply integral_mono ((integrable_const 1).sub (hint _))
    (((integrable_const 1).sub (hint _)).const_mul 4)
  intro x
  simp only [Pi.sub_apply, real_inner_smul_right, Real.cos_two_mul]
  nlinarith [Real.cos_le_one ⟪x, ξ⟫, Real.neg_one_le_cos ⟪x, ξ⟫]

/-- **The doubling inequality**: `1 - |ρ̂(2ξ)|² ≤ 4(1 - |ρ̂(ξ)|²)` for a probability measure `ρ`,
since `|ρ̂|²` is the transform of the symmetrisation `ρ ∗ (-1)_* ρ`. -/
theorem one_sub_norm_sq_charFun_two_smul_le (ρ : Measure E) [IsProbabilityMeasure ρ] (ξ : E) :
    1 - ‖charFun ρ ((2 : ℝ) • ξ)‖ ^ 2 ≤ 4 * (1 - ‖charFun ρ ξ‖ ^ 2) := by
  haveI : IsProbabilityMeasure (ρ.map ((-1 : ℝ) • ·)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hκ : ∀ η : E, (charFun (ρ ∗ ρ.map ((-1 : ℝ) • ·)) η).re = ‖charFun ρ η‖ ^ 2 := by
    intro η
    rw [charFun_conv, charFun_map_smul, neg_one_smul, charFun_neg, Complex.mul_conj,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have := one_sub_re_charFun_two_smul_le (ρ ∗ ρ.map ((-1 : ℝ) • ·)) ξ
  rwa [hκ, hκ] at this

/-! ## The transform has no zeros -/

/-- **The transform of a self-decomposable probability measure has no zeros** (Paper VII,
`prop:gw-ray-families`(1)). Let `z₀` be the first zero along a ray. At `z₀` the factorisation
forces `ρ̂_c(z₀) = 0`, so the doubling inequality at `z₀/2` gives `|μ̂(z₀/2)|² ≤ ¾ |μ̂(cz₀/2)|²`
for every `c ∈ (0,1)`, which fails in the limit `c ↑ 1` since `μ̂(z₀/2) ≠ 0`. -/
theorem IsSelfDecomposable.charFun_ne_zero {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : IsSelfDecomposable μ) (z : E) : charFun μ z ≠ 0 := by
  rw [isSelfDecomposable_iff_charFun] at hμ
  intro hz
  /- The first zero along the ray of `z`. -/
  set Z : Set ℝ := {t : ℝ | 0 ≤ t ∧ charFun μ (t • z) = 0} with hZ
  have hZne : Z.Nonempty := ⟨1, zero_le_one, by rwa [one_smul]⟩
  have hZbdd : BddBelow Z := ⟨0, fun t ht => ht.1⟩
  have hcray : Continuous fun t : ℝ => charFun μ (t • z) :=
    continuous_charFun.comp (continuous_id.smul continuous_const)
  have hZclosed : IsClosed Z := isClosed_Ici.inter (isClosed_singleton.preimage hcray)
  set t₀ := sInf Z with ht₀def
  have ht₀ : t₀ ∈ Z := hZclosed.csInf_mem hZne hZbdd
  have ht₀pos : 0 < t₀ := by
    rcases eq_or_lt_of_le ht₀.1 with h | h
    · exfalso
      have h2 := ht₀.2
      rw [← h, zero_smul, charFun_zero] at h2
      simp at h2
    · exact h
  have hbelow : ∀ s : ℝ, 0 ≤ s → s < t₀ → charFun μ (s • z) ≠ 0 := fun s hs hst h0 =>
    (not_lt.2 (csInf_le hZbdd ⟨hs, h0⟩)) hst
  set z₀ := t₀ • z with hz₀
  set w := (1 / 2 : ℝ) • z₀ with hw
  have hw0 : charFun μ w ≠ 0 := by
    rw [hw, hz₀, smul_smul]
    exact hbelow _ (by positivity) (by linarith)
  /- For every `c ∈ (0,1)`: `|μ̂(w)|² ≤ ¾ |μ̂(cw)|²`. -/
  have key : ∀ c : ℝ, 0 < c → c < 1 → ‖charFun μ w‖ ^ 2 ≤ 3 / 4 * ‖charFun μ (c • w)‖ ^ 2 := by
    intro c hc0 hc1
    obtain ⟨ρ, hρ, hfac⟩ := hμ c hc0 hc1
    have hρz : charFun ρ z₀ = 0 := by
      have h := hfac z₀
      rw [ht₀.2] at h
      have hne : charFun μ (c • z₀) ≠ 0 := by
        rw [hz₀, smul_smul]
        exact hbelow _ (by positivity) (by nlinarith)
      exact (mul_eq_zero.1 h.symm).resolve_left hne
    have hdbl := one_sub_norm_sq_charFun_two_smul_le ρ w
    rw [hw, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul, ← hw, hρz,
      norm_zero] at hdbl
    have hρw : ‖charFun ρ w‖ ^ 2 ≤ 3 / 4 := by nlinarith
    have h := congrArg (fun x => ‖x‖ ^ 2) (hfac w)
    simp only [norm_mul, mul_pow] at h
    rw [h]
    have := sq_nonneg ‖charFun μ (c • w)‖
    nlinarith
  /- The limit `c ↑ 1`. -/
  have hlim : Tendsto (fun c : ℝ => 3 / 4 * ‖charFun μ (c • w)‖ ^ 2) (𝓝[<] 1)
      (𝓝 (3 / 4 * ‖charFun μ w‖ ^ 2)) := by
    have hc : Continuous fun c : ℝ => 3 / 4 * ‖charFun μ (c • w)‖ ^ 2 := by
      have : Continuous fun c : ℝ => charFun μ (c • w) :=
        continuous_charFun.comp (continuous_id.smul continuous_const)
      fun_prop
    have := hc.tendsto 1
    simp only [one_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ c in 𝓝[<] (1 : ℝ), ‖charFun μ w‖ ^ 2 ≤ 3 / 4 * ‖charFun μ (c • w)‖ ^ 2 := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with c hc
    exact key c hc.1 hc.2
  have hle := ge_of_tendsto hlim hev
  have hpos : 0 < ‖charFun μ w‖ ^ 2 := by positivity
  linarith

end Transform

end ScaleSpace
