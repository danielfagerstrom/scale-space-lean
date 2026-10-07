/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import ScaleSpaceCore.L1OperatorsSpace
import ScaleSpaceCore.BochnerConvolution

/-!
# Convolution on `L¹(E)` as a vector-valued integral, and the kernel of the identity

Q-0332 (SSL-5), the `d`-dimensional counterpart of `ScaleSpaceCore.BochnerConvolution` up to its
`apply_bconv`, with the same proofs over a finite-dimensional space `E` carrying an additive Haar
measure: translation acts continuously on `L¹(E)` (`continuous_transL1E`); `f * g` is the
`L¹(E)`-valued Bochner integral `∫ f(y) T_y g dy` (`bconvE`, identified with the classical
convolution by `coeFn_bconvE`), and a bounded operator commuting with every translation passes
through it (`map_bconvE`, the interchange identity `Φ (f * g) = f * Φ g`); `μ * f = ∫ T_y f dμ(y)`
(`bconvME_eq_mconvL1E`), so a bounded functional pairs against `μ * f` as an integral over `μ`
(`apply_mconvL1E`, `apply_bconvE`).

The last section is the `d`-dimensional `eq_dirac_of_mconvL1_eq_id` of `ScaleSpaceCore.Transport`,
tested at the tent `k(y) = max 0 (1 - ‖y‖)` instead of the line's Gaussian bump, because a
compactly supported continuous function is integrable for every Haar measure.

What stays on the line: the character pairing and `mconvL1_injective` (the Fourier step of
uniqueness), `bconv_comm`, and `setIntegral_bconv`.
-/

namespace ScaleSpace

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-! ## Translation acts continuously on `L¹(E)` -/

/-- `a ↦ (x ↦ x - a)`, as a continuous map into `C(E, E)`. -/
noncomputable def subCME : C(E, C(E, E)) :=
  ContinuousMap.curry ⟨fun p : E × E => p.2 - p.1, by fun_prop⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
@[simp] lemma subCME_apply (a x : E) : subCME a x = x - a := rfl

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma measurePreserving_subCME (a : E) :
    MeasurePreserving (subCME a) volume volume := measurePreserving_sub_constE a

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The hand-built `transL1E` is Mathlib's composition operator. -/
theorem transL1E_eq (a : E) (g : E →₁[volume] ℝ) :
    transL1E a g = Lp.compMeasurePreserving (subCME a) (measurePreserving_subCME a) g := by
  refine Lp.ext ((coeFn_transL1E a g).trans ?_)
  exact (Lp.coeFn_compMeasurePreserving g (measurePreserving_subCME a)).symm

/-- **Translation acts continuously on `L¹(E)`**: `y ↦ T_y g` is continuous. -/
theorem continuous_transL1E (g : E →₁[volume] ℝ) : Continuous fun a : E => transL1E a g := by
  rw [continuous_iff_continuousAt]
  intro a₀
  have h := Filter.Tendsto.compMeasurePreservingLp (l := nhds a₀) (f := fun _ : E => g)
    (f₀ := g) (g := fun a : E => subCME a) (g₀ := subCME a₀) tendsto_const_nhds
    (subCME.continuous.tendsto a₀) (fun a => measurePreserving_subCME a)
    (measurePreserving_subCME a₀) ENNReal.one_ne_top
  simp only [← transL1E_eq] at h
  exact h

/-! ## Convolution as a Bochner integral -/

/-- `f * g = ∫ f(y) · T_y g dy`, as an `L¹(E)`-valued Bochner integral. -/
noncomputable def bconvE (f : E → ℝ) (g : E →₁[volume] ℝ) : E →₁[volume] ℝ :=
  ∫ y, f y • transL1E y g

theorem integrable_smul_transL1E {f : E → ℝ} (hf : Integrable f) (g : E →₁[volume] ℝ) :
    Integrable (fun y => f y • transL1E y g) := by
  have hm : AEStronglyMeasurable (fun y => f y • transL1E y g) volume :=
    hf.aestronglyMeasurable.smul (continuous_transL1E g).aestronglyMeasurable
  refine ⟨hm, ?_⟩
  have hdom : ∀ y, ‖f y • transL1E y g‖ ≤ ‖f y‖ * ‖g‖ := by
    intro y
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_transL1E_le y g) (norm_nonneg _)
  exact ((hf.norm.mul_const ‖g‖).mono' hm (Filter.Eventually.of_forall hdom)).2

/-- **The interchange identity `Φ (f * g) = f * (Φ g)`**, for any bounded operator on `L¹(E)` that
commutes with every translation. -/
theorem map_bconvE (L : (E →₁[volume] ℝ) →L[ℝ] (E →₁[volume] ℝ))
    (hL : ∀ a g, L (transL1E a g) = transL1E a (L g))
    {f : E → ℝ} (hf : Integrable f) (g : E →₁[volume] ℝ) :
    L (bconvE f g) = bconvE f (L g) := by
  rw [bconvE, ← L.integral_comp_comm (integrable_smul_transL1E hf g), bconvE]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change L (f y • transL1E y g) = f y • transL1E y (L g)
  rw [ContinuousLinearMap.map_smul, hL]

/-! ## `bconvE` is the classical convolution -/

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- Integration over a fixed set, as a bounded functional on `L¹(E)`. -/
noncomputable def setIntegralCLME (A : Set E) : (E →₁[volume] ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun h => ∫ x in A, (h : E → ℝ) x
      map_add' := fun h₁ h₂ => by
        rw [← integral_add ((L1.integrable_coeFn h₁).integrableOn)
          ((L1.integrable_coeFn h₂).integrableOn)]
        refine integral_congr_ae ?_
        filter_upwards [(Lp.coeFn_add h₁ h₂).restrict] with x hx
        rw [hx]
        rfl
      map_smul' := fun c h => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [(Lp.coeFn_smul c h).restrict] with x hx
        rw [hx]
        rfl }
    1 fun h => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      calc ‖∫ x in A, (h : E → ℝ) x‖ ≤ ∫ x in A, ‖(h : E → ℝ) x‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x, ‖(h : E → ℝ) x‖ :=
            setIntegral_le_integral (L1.integrable_coeFn h).norm
              (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        _ = ‖h‖ := by
            rw [Lp.norm_def, eLpNorm_one_eq_lintegral_enorm,
              ← integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable h)]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
@[simp] lemma setIntegralCLME_apply (A : Set E) (h : E →₁[volume] ℝ) :
    setIntegralCLME A h = ∫ x in A, (h : E → ℝ) x := rfl

/-- The two-variable integrand of the classical convolution is integrable on the product. -/
theorem integrable_uncurry_pconvE {f : E → ℝ} (hf : Integrable f) (g : E →₁[volume] ℝ) :
    Integrable (fun p : E × E => f p.2 * (g : E → ℝ) (p.1 - p.2)) (volume.prod volume) := by
  have hgm : AEStronglyMeasurable (fun p : E × E => (g : E → ℝ) (p.1 - p.2))
      (volume.prod volume) :=
    (Lp.aestronglyMeasurable g).comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub volume volume)
  have hm : AEStronglyMeasurable (fun p : E × E => f p.2 * (g : E → ℝ) (p.1 - p.2))
      (volume.prod volume) :=
    ((hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd)).mul hgm)
  refine ⟨hm, ?_⟩
  have hme : AEMeasurable
      (Function.uncurry fun x y : E => ‖f y‖ₑ * ‖(g : E → ℝ) (x - y)‖ₑ)
      (volume.prod volume) := by
    have hu : (Function.uncurry fun x y : E => ‖f y‖ₑ * ‖(g : E → ℝ) (x - y)‖ₑ)
        = fun p : E × E => ‖f p.2‖ₑ * ‖(g : E → ℝ) (p.1 - p.2)‖ₑ := rfl
    rw [hu]
    simpa [enorm_mul] using hm.enorm
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hm.enorm]
  calc ∫⁻ x, ∫⁻ y, ‖f y * (g : E → ℝ) (x - y)‖ₑ
      = ∫⁻ y, ∫⁻ x, ‖f y‖ₑ * ‖(g : E → ℝ) (x - y)‖ₑ := by
        simp only [enorm_mul]
        exact lintegral_lintegral_swap hme
    _ = ∫⁻ y, ‖f y‖ₑ * ∫⁻ x, ‖(g : E → ℝ) x‖ₑ := by
        refine lintegral_congr fun y => ?_
        rw [lintegral_const_mul' _ _ (enorm_ne_top),
          lintegral_sub_right_eq_self (fun x => ‖(g : E → ℝ) x‖ₑ) y]
    _ < ⊤ := by
        rw [lintegral_mul_const' _ _ (L1.integrable_coeFn g).2.ne]
        exact ENNReal.mul_lt_top hf.2 (L1.integrable_coeFn g).2

/-- The classical convolution is integrable. -/
theorem integrable_pconvE {f : E → ℝ} (hf : Integrable f) (g : E →₁[volume] ℝ) :
    Integrable (fun x => ∫ y, f y * (g : E → ℝ) (x - y)) :=
  (integrable_uncurry_pconvE hf g).integral_prod_left

/-- **`bconvE` is the classical convolution** `x ↦ ∫ f(y) g(x - y) dy`. -/
theorem coeFn_bconvE {f : E → ℝ} (hf : Integrable f) (g : E →₁[volume] ℝ) :
    (bconvE f g : E → ℝ) =ᵐ[volume] fun x => ∫ y, f y * (g : E → ℝ) (x - y) := by
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun A _ _ => (L1.integrable_coeFn (bconvE f g)).integrableOn)
    (fun A _ _ => (integrable_pconvE hf g).integrableOn) fun A hA _ => ?_
  have hleft : ∫ x in A, (bconvE f g : E → ℝ) x
      = ∫ y, f y * ∫ x in A, (g : E → ℝ) (x - y) := by
    rw [← setIntegralCLME_apply A (bconvE f g), bconvE,
      ← ContinuousLinearMap.integral_comp_comm _ (integrable_smul_transL1E hf g)]
    refine integral_congr_ae ?_
    filter_upwards with y
    rw [ContinuousLinearMap.map_smul, setIntegralCLME_apply, smul_eq_mul]
    congr 1
    exact integral_congr_ae ((coeFn_transL1E y g).restrict)
  have hprodint : Integrable
      (Function.uncurry fun x y : E => A.indicator (fun x' => f y * (g : E → ℝ) (x' - y)) x)
      (volume.prod volume) := by
    have hset : (Function.uncurry fun x y : E =>
          A.indicator (fun x' => f y * (g : E → ℝ) (x' - y)) x)
        = (A ×ˢ (univ : Set E)).indicator
          (fun p : E × E => f p.2 * (g : E → ℝ) (p.1 - p.2)) := by
      funext p
      change A.indicator (fun x' => f p.2 * (g : E → ℝ) (x' - p.2)) p.1
        = (A ×ˢ (univ : Set E)).indicator
          (fun q : E × E => f q.2 * (g : E → ℝ) (q.1 - q.2)) p
      by_cases hp : p.1 ∈ A
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (by simp [hp])]
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (by simp [hp])]
    rw [hset]
    exact (integrable_uncurry_pconvE hf g).indicator (hA.prod MeasurableSet.univ)
  have hright : ∫ x in A, (∫ y, f y * (g : E → ℝ) (x - y))
      = ∫ y, f y * ∫ x in A, (g : E → ℝ) (x - y) := by
    rw [← integral_indicator hA]
    have hswap : ∫ x, A.indicator (fun x => ∫ y, f y * (g : E → ℝ) (x - y)) x
        = ∫ x, ∫ y, A.indicator (fun x' => f y * (g : E → ℝ) (x' - y)) x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ A
      · simp only [Set.indicator_of_mem hx]
      · simp only [Set.indicator_of_notMem hx, integral_zero]
    rw [hswap, integral_integral_swap hprodint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change ∫ x, A.indicator (fun x' => f y * (g : E → ℝ) (x' - y)) x
      = f y * ∫ x in A, (g : E → ℝ) (x - y)
    rw [integral_indicator hA, integral_const_mul]
  rw [hleft, hright]

/-! ## `μ * f` as a Bochner integral -/

/-- `y ↦ T_y f` is `μ`-integrable for every finite `μ`. -/
theorem integrable_transL1E (μ : Measure E) [IsFiniteMeasure μ] (f : E →₁[volume] ℝ) :
    Integrable (fun y => transL1E y f) μ :=
  Integrable.mono' (integrable_const ‖f‖) (continuous_transL1E f).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => norm_transL1E_le y f)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- `∫ T_y f dμ(y)`, as an `L¹(E)`-valued Bochner integral. -/
noncomputable def bconvME (μ : Measure E) (f : E →₁[volume] ℝ) : E →₁[volume] ℝ :=
  ∫ y, transL1E y f ∂μ

/-- **The Bochner form of convolution by a measure**: `μ * f = ∫ T_y f dμ(y)`. -/
theorem bconvME_eq_mconvL1E (μ : Measure E) [IsFiniteMeasure μ] (f : E →₁[volume] ℝ) :
    bconvME μ f = mconvL1E μ f := by
  refine Lp.ext ?_
  refine Filter.EventuallyEq.trans ?_ (coeFn_mconvL1E μ f).symm
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun A _ _ => (L1.integrable_coeFn (bconvME μ f)).integrableOn)
    (fun A _ _ => (integrable_mconvE μ (Lp.aestronglyMeasurable f)
      (L1.integrable_coeFn f)).integrableOn) fun A hA _ => ?_
  have hleft : ∫ x in A, (bconvME μ f : E → ℝ) x
      = ∫ y, (∫ x in A, (f : E → ℝ) (x - y)) ∂μ := by
    rw [← setIntegralCLME_apply A (bconvME μ f), bconvME,
      ← ContinuousLinearMap.integral_comp_comm _ (integrable_transL1E μ f)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change ∫ x in A, ((transL1E y f : E →₁[volume] ℝ) : E → ℝ) x = ∫ x in A, (f : E → ℝ) (x - y)
    exact integral_congr_ae ((coeFn_transL1E y f).restrict)
  have hprodint : Integrable
      (Function.uncurry fun x y : E => A.indicator (fun x' => (f : E → ℝ) (x' - y)) x)
      (volume.prod μ) := by
    have hset : (Function.uncurry fun x y : E =>
          A.indicator (fun x' => (f : E → ℝ) (x' - y)) x)
        = (A ×ˢ (univ : Set E)).indicator
          (Function.uncurry fun x y : E => (f : E → ℝ) (x - y)) := by
      funext p
      change A.indicator (fun x' => (f : E → ℝ) (x' - p.2)) p.1
        = (A ×ˢ (univ : Set E)).indicator
          (fun q : E × E => (f : E → ℝ) (q.1 - q.2)) p
      by_cases hp : p.1 ∈ A
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (by simp [hp])]
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (by simp [hp])]
    rw [hset]
    exact (integrable_uncurry_subE μ (Lp.aestronglyMeasurable f)
      (L1.integrable_coeFn f)).indicator (hA.prod MeasurableSet.univ)
  have hright : ∫ x in A, mconvE μ (f : E → ℝ) x
      = ∫ y, (∫ x in A, (f : E → ℝ) (x - y)) ∂μ := by
    rw [← integral_indicator hA]
    have hswap : ∫ x, A.indicator (mconvE μ (f : E → ℝ)) x
        = ∫ x, ∫ y, A.indicator (fun x' => (f : E → ℝ) (x' - y)) x ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ A
      · simp only [Set.indicator_of_mem hx, mconvE_apply]
      · simp only [Set.indicator_of_notMem hx, integral_zero]
    rw [hswap, integral_integral_swap hprodint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change ∫ x, A.indicator (fun x' => (f : E → ℝ) (x' - y)) x
      = ∫ x in A, (f : E → ℝ) (x - y)
    rw [integral_indicator hA]
  rw [hleft, hright]

/-! ## Pairing with a bounded functional -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **`Ψ (μ * f) = ∫ Ψ (T_y f) dμ(y)`**, for a bounded functional with values in any Banach
space. -/
theorem apply_mconvL1E_general (Ψ : (E →₁[volume] ℝ) →L[ℝ] F) (μ : Measure E) [IsFiniteMeasure μ]
    (f : E →₁[volume] ℝ) :
    Ψ (mconvL1E μ f) = ∫ y, Ψ (transL1E y f) ∂μ := by
  rw [← bconvME_eq_mconvL1E, bconvME,
    ← ContinuousLinearMap.integral_comp_comm _ (integrable_transL1E μ f)]

/-- `y ↦ Ψ (T_y f)`, as a bounded continuous function on `E`. -/
noncomputable def pairTransE (Ψ : (E →₁[volume] ℝ) →L[ℝ] ℝ) (f : E →₁[volume] ℝ) :
    BoundedContinuousFunction E ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun y => Ψ (transL1E y f))
    (Ψ.continuous.comp (continuous_transL1E f)) (‖Ψ‖ * ‖f‖) fun y =>
    (Ψ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_transL1E_le y f) (norm_nonneg _))

@[simp] lemma pairTransE_apply (Ψ : (E →₁[volume] ℝ) →L[ℝ] ℝ) (f : E →₁[volume] ℝ) (y : E) :
    pairTransE Ψ f y = Ψ (transL1E y f) := rfl

/-- **`Ψ (μ * f) = ∫ Ψ (T_y f) dμ(y)`.** -/
theorem apply_mconvL1E (Ψ : (E →₁[volume] ℝ) →L[ℝ] ℝ) (μ : Measure E) [IsFiniteMeasure μ]
    (f : E →₁[volume] ℝ) :
    Ψ (mconvL1E μ f) = ∫ y, pairTransE Ψ f y ∂μ :=
  apply_mconvL1E_general Ψ μ f

/-- **`Ψ (g * f) = ∫ g(y) Ψ (T_y f) dy`**, the density counterpart. -/
theorem apply_bconvE (Ψ : (E →₁[volume] ℝ) →L[ℝ] ℝ) {g : E → ℝ} (hg : Integrable g)
    (f : E →₁[volume] ℝ) :
    Ψ (bconvE g f) = ∫ y, g y * pairTransE Ψ f y := by
  rw [bconvE, ← ContinuousLinearMap.integral_comp_comm _ (integrable_smul_transL1E hg f)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change Ψ (g y • transL1E y f) = g y * Ψ (transL1E y f)
  rw [ContinuousLinearMap.map_smul, smul_eq_mul]

/-! ## The kernel of the identity -/

/-- **The kernel of the identity is `δ₀`**: if convolution by a probability measure fixes every
element of `L¹(E)`, the measure is `δ₀`. Tested at the tent `k(y) = max 0 (1 - ‖y‖)`: `μ * k` is
continuous, so `μ * k = k` holds everywhere, and at the origin it says `∫ k dμ = 1`; since `k < 1`
off the origin, `μ` sits at the origin. -/
theorem eq_dirac_of_mconvL1E_eq_id {μ : Measure E} [IsProbabilityMeasure μ]
    (h : mconvL1E μ = ContinuousLinearMap.id ℝ (E →₁[volume] ℝ)) : μ = Measure.dirac 0 := by
  set k : E → ℝ := fun y => max 0 (1 - ‖y‖) with hk
  have hkc : Continuous k := continuous_const.max (continuous_const.sub continuous_norm)
  have hk0 : k 0 = 1 := by simp [hk]
  have hkb : ∀ y, k y ≤ 1 := fun y =>
    max_le zero_le_one (by linarith [norm_nonneg y])
  have hkn : ∀ y, 0 ≤ k y := fun y => le_max_left _ _
  have hklt : ∀ y : E, y ≠ 0 → k y < 1 := fun y hy =>
    max_lt zero_lt_one (by linarith [norm_pos_iff.mpr hy])
  have hksupp : HasCompactSupport k := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : E) 1) fun y hy => ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
    exact max_eq_left (by linarith)
  have hki : Integrable k := hkc.integrable_of_hasCompactSupport hksupp
  have hkiμ : Integrable k μ :=
    (integrable_const (1 : ℝ)).mono' hkc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hkn y)]; exact hkb y)
  have hae : mconvE μ k =ᵐ[volume] k := by
    have h1 : ((mconvL1E μ (hki.toL1 k) : E →₁[volume] ℝ) : E → ℝ) =ᵐ[volume] mconvE μ k :=
      (coeFn_mconvL1E μ _).trans (mconvE_congr_ae μ (Integrable.coeFn_toL1 hki))
    have h2 : ((mconvL1E μ (hki.toL1 k) : E →₁[volume] ℝ) : E → ℝ) =ᵐ[volume] k := by
      rw [h]; simpa using Integrable.coeFn_toL1 hki
    exact h1.symm.trans h2
  have hcont : Continuous (mconvE μ k) := by
    refine continuous_of_dominated (bound := fun _ => (1 : ℝ)) ?_ ?_ (integrable_const _) ?_
    · exact fun x => (hkc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · exact fun x => Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hkn _)]
        exact hkb _
    · exact Filter.Eventually.of_forall fun y => hkc.comp (continuous_id.sub continuous_const)
  have heq : mconvE μ k = k := (hcont.ae_eq_iff_eq volume hkc).mp hae
  have hint : ∫ y, k y ∂μ = 1 := by
    have h0 : mconvE μ k 0 = k 0 := by rw [heq]
    rw [mconvE_apply, hk0] at h0
    have hsimp : ∫ y, k (0 - y) ∂μ = ∫ y, k y ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp [hk]
    rw [hsimp] at h0
    exact h0
  have hzero : ∀ᵐ y ∂μ, (1 : ℝ) - k y = 0 := by
    refine (integral_eq_zero_iff_of_nonneg (fun y => sub_nonneg.mpr (hkb y))
      ((integrable_const (1 : ℝ)).sub hkiμ)).mp ?_
    rw [integral_sub (integrable_const _) hkiμ, integral_const, hint]
    simp
  have hae0 : ∀ᵐ y ∂μ, y = 0 := by
    filter_upwards [hzero] with y hy
    by_contra hne
    have hlt := hklt y hne
    linarith [sub_eq_zero.mp hy]
  have hnull : μ {y | y ≠ 0} = 0 := ae_iff.mp hae0
  ext s hs
  rw [Measure.dirac_apply' _ hs]
  by_cases h0 : (0 : E) ∈ s
  · rw [Set.indicator_of_mem h0, Pi.one_apply]
    refine (prob_compl_eq_zero_iff hs).mp (measure_mono_null (fun y hy => ?_) hnull)
    rintro rfl
    exact hy h0
  · rw [Set.indicator_of_notMem h0]
    refine measure_mono_null (fun y hy => ?_) hnull
    rintro rfl
    exact h0 hy

/-! ## ℝ is the case `d = 1` -/

theorem bconvE_real (f : ℝ → ℝ) (g : X) : bconvE f g = bconv f g := by
  simp only [bconvE, bconv, transL1E_real]

theorem bconvME_real (μ : Measure ℝ) (f : X) : bconvME μ f = bconvM μ f := by
  simp only [bconvME, bconvM, transL1E_real]

end ScaleSpace
