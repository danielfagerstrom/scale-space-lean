/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import ScaleSpaceCore.L1Operators
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Convolution as a vector-valued integral, and pairing against a bounded functional

Slice 2 of E-0009 (hub `proposals/E-0009.md`), moved from Paper I's `Representation.lean` and
Paper V's `SpatialLine/BochnerConvolution.lean`
(`offices/engineer/notes/2026-09-19-lean-duplication-survey.md` §§ 3, 6). The step every route to
a convolution representation lemma needs first is `Φ (f * g) = f * (Φ g)`, for any bounded
operator `Φ` that commutes with translation. The proof writes `f * g` as the `X`-valued Bochner
integral `∫ f(y) · T_y g dy` and moves `Φ` inside; identifying that integral with the classical
pointwise convolution goes through bounded set-integral functionals, and the same idea gives the
Bochner form `μ * f = ∫ T_y f dμ(y)` of `mconvL1`.

## What stayed behind

Paper V's file continues past `apply_bconv` with a section pairing against the complex
character `e_{-iωx}` and the standard Gaussian density, to prove the uniqueness clause of its own
representation lemma (its own docstring: "no causal twin"), and a second pairing lemma
(`setIntegral_bconv`) feeding a tightness argument specific to Paper V's construction. Neither is
here: both are consumed by one article's own argument, not shared.
-/

namespace ScaleSpace

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## Translation acts continuously on `L¹` -/

/-- `a ↦ (x ↦ x - a)`, as a continuous map into `C(ℝ,ℝ)`. Currying is what makes the
compact-open continuity automatic. -/
noncomputable def subCM : C(ℝ, C(ℝ, ℝ)) :=
  ContinuousMap.curry ⟨fun p : ℝ × ℝ => p.2 - p.1, by fun_prop⟩

@[simp] lemma subCM_apply (a x : ℝ) : subCM a x = x - a := rfl

lemma measurePreserving_subCM (a : ℝ) :
    MeasurePreserving (subCM a) volume volume := measurePreserving_sub_const a

/-- The hand-built `transL1` is Mathlib's composition operator. -/
theorem transL1_eq (a : ℝ) (g : X) :
    transL1 a g = Lp.compMeasurePreserving (subCM a) (measurePreserving_subCM a) g := by
  refine Lp.ext ((coeFn_transL1 a g).trans ?_)
  exact (Lp.coeFn_compMeasurePreserving g (measurePreserving_subCM a)).symm

/-- **Translation acts continuously on `L¹`.** -/
theorem continuous_transL1 (g : X) : Continuous fun a : ℝ => transL1 a g := by
  rw [continuous_iff_continuousAt]
  intro a₀
  have h := Filter.Tendsto.compMeasurePreservingLp (l := nhds a₀) (f := fun _ : ℝ => g)
    (f₀ := g) (g := fun a : ℝ => subCM a) (g₀ := subCM a₀) tendsto_const_nhds
    (subCM.continuous.tendsto a₀) (fun a => measurePreserving_subCM a)
    (measurePreserving_subCM a₀) ENNReal.one_ne_top
  simp only [← transL1_eq] at h
  exact h

lemma norm_transL1_le (a : ℝ) (g : X) : ‖transL1 a g‖ ≤ ‖g‖ := by
  have hop : ‖transL1 a‖ ≤ 1 := by
    rw [transL1]
    exact LinearMap.mkContinuous_norm_le _ zero_le_one _
  calc ‖transL1 a g‖ ≤ ‖transL1 a‖ * ‖g‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖g‖ := by nlinarith [norm_nonneg g]
    _ = ‖g‖ := one_mul _

/-! ## Convolution as a Bochner integral -/

/-- `f * g = ∫ f(y) · T_y g dy`, as an `X`-valued Bochner integral. -/
noncomputable def bconv (f : ℝ → ℝ) (g : X) : X := ∫ y, f y • transL1 y g

theorem integrable_smul_transL1 {f : ℝ → ℝ} (hf : Integrable f) (g : X) :
    Integrable (fun y => f y • transL1 y g) := by
  have hm : AEStronglyMeasurable (fun y => f y • transL1 y g) volume :=
    hf.aestronglyMeasurable.smul (continuous_transL1 g).aestronglyMeasurable
  refine ⟨hm, ?_⟩
  have hdom : ∀ y, ‖f y • transL1 y g‖ ≤ ‖f y‖ * ‖g‖ := by
    intro y
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_transL1_le y g) (norm_nonneg _)
  exact ((hf.norm.mul_const ‖g‖).mono' hm (Filter.Eventually.of_forall hdom)).2

/-- **`Φ (f * g) = f * (Φ g)`**, for any bounded operator that commutes with translation. -/
theorem map_bconv (L : X →L[ℝ] X) (hL : ∀ a g, L (transL1 a g) = transL1 a (L g))
    {f : ℝ → ℝ} (hf : Integrable f) (g : X) :
    L (bconv f g) = bconv f (L g) := by
  rw [bconv, ← L.integral_comp_comm (integrable_smul_transL1 hf g), bconv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change L (f y • transL1 y g) = f y • transL1 y (L g)
  rw [ContinuousLinearMap.map_smul, hL]

/-! ## `bconv` is the classical convolution

The Bochner integral defining `bconv` has no pointwise meaning on the nose — `L¹` has no
evaluation map — so identifying it with `x ↦ ∫ f(y) g(x-y) dy` goes through set integrals: the
two agree on every set of finite measure, and `ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`
concludes.
-/

/-- Integration over a fixed set, as a bounded functional on `L¹`. -/
noncomputable def setIntegralCLM (A : Set ℝ) : X →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun h => ∫ x in A, (h : ℝ → ℝ) x
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
      calc ‖∫ x in A, (h : ℝ → ℝ) x‖ ≤ ∫ x in A, ‖(h : ℝ → ℝ) x‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x, ‖(h : ℝ → ℝ) x‖ :=
            setIntegral_le_integral (L1.integrable_coeFn h).norm
              (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        _ = ‖h‖ := by
            rw [Lp.norm_def, eLpNorm_one_eq_lintegral_enorm,
              ← integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable h)]

@[simp] lemma setIntegralCLM_apply (A : Set ℝ) (h : X) :
    setIntegralCLM A h = ∫ x in A, (h : ℝ → ℝ) x := rfl

/-- The two-variable integrand of the classical convolution is integrable on the product — the
Tonelli bound `‖f‖₁ ‖g‖₁`, by translation invariance in `x`. -/
theorem integrable_uncurry_pconv {f : ℝ → ℝ} (hf : Integrable f) (g : X) :
    Integrable (fun p : ℝ × ℝ => f p.2 * (g : ℝ → ℝ) (p.1 - p.2)) (volume.prod volume) := by
  have hgm : AEStronglyMeasurable (fun p : ℝ × ℝ => (g : ℝ → ℝ) (p.1 - p.2))
      (volume.prod volume) :=
    (Lp.aestronglyMeasurable g).comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub volume volume)
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.2 * (g : ℝ → ℝ) (p.1 - p.2))
      (volume.prod volume) :=
    ((hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd)).mul hgm)
  refine ⟨hm, ?_⟩
  have hme : AEMeasurable
      (Function.uncurry fun x y : ℝ => ‖f y‖ₑ * ‖(g : ℝ → ℝ) (x - y)‖ₑ)
      (volume.prod volume) := by
    have hu : (Function.uncurry fun x y : ℝ => ‖f y‖ₑ * ‖(g : ℝ → ℝ) (x - y)‖ₑ)
        = fun p : ℝ × ℝ => ‖f p.2‖ₑ * ‖(g : ℝ → ℝ) (p.1 - p.2)‖ₑ := rfl
    rw [hu]
    simpa [enorm_mul] using hm.enorm
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hm.enorm]
  calc ∫⁻ x, ∫⁻ y, ‖f y * (g : ℝ → ℝ) (x - y)‖ₑ
      = ∫⁻ y, ∫⁻ x, ‖f y‖ₑ * ‖(g : ℝ → ℝ) (x - y)‖ₑ := by
        simp only [enorm_mul]
        exact lintegral_lintegral_swap hme
    _ = ∫⁻ y, ‖f y‖ₑ * ∫⁻ x, ‖(g : ℝ → ℝ) x‖ₑ := by
        refine lintegral_congr fun y => ?_
        rw [lintegral_const_mul' _ _ (enorm_ne_top),
          lintegral_sub_right_eq_self (fun x => ‖(g : ℝ → ℝ) x‖ₑ) y]
    _ < ⊤ := by
        rw [lintegral_mul_const' _ _ (L1.integrable_coeFn g).2.ne]
        exact ENNReal.mul_lt_top hf.2 (L1.integrable_coeFn g).2

/-- The classical convolution is integrable. -/
theorem integrable_pconv {f : ℝ → ℝ} (hf : Integrable f) (g : X) :
    Integrable (fun x => ∫ y, f y * (g : ℝ → ℝ) (x - y)) :=
  (integrable_uncurry_pconv hf g).integral_prod_left

/-- **`bconv` is the classical convolution.** -/
theorem coeFn_bconv {f : ℝ → ℝ} (hf : Integrable f) (g : X) :
    (bconv f g : ℝ → ℝ) =ᵐ[volume] fun x => ∫ y, f y * (g : ℝ → ℝ) (x - y) := by
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun A _ _ => (L1.integrable_coeFn (bconv f g)).integrableOn)
    (fun A _ _ => (integrable_pconv hf g).integrableOn) fun A hA _ => ?_
  have hleft : ∫ x in A, (bconv f g : ℝ → ℝ) x
      = ∫ y, f y * ∫ x in A, (g : ℝ → ℝ) (x - y) := by
    rw [← setIntegralCLM_apply A (bconv f g), bconv,
      ← ContinuousLinearMap.integral_comp_comm _ (integrable_smul_transL1 hf g)]
    refine integral_congr_ae ?_
    filter_upwards with y
    rw [ContinuousLinearMap.map_smul, setIntegralCLM_apply, smul_eq_mul]
    congr 1
    exact integral_congr_ae ((coeFn_transL1 y g).restrict)
  have hprodint : Integrable
      (Function.uncurry fun x y : ℝ => A.indicator (fun x' => f y * (g : ℝ → ℝ) (x' - y)) x)
      (volume.prod volume) := by
    have hset : (Function.uncurry fun x y : ℝ =>
          A.indicator (fun x' => f y * (g : ℝ → ℝ) (x' - y)) x)
        = (A ×ˢ (univ : Set ℝ)).indicator
          (fun p : ℝ × ℝ => f p.2 * (g : ℝ → ℝ) (p.1 - p.2)) := by
      funext p
      change A.indicator (fun x' => f p.2 * (g : ℝ → ℝ) (x' - p.2)) p.1
        = (A ×ˢ (univ : Set ℝ)).indicator
          (fun q : ℝ × ℝ => f q.2 * (g : ℝ → ℝ) (q.1 - q.2)) p
      by_cases hp : p.1 ∈ A
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (by simp [hp])]
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (by simp [hp])]
    rw [hset]
    exact (integrable_uncurry_pconv hf g).indicator (hA.prod MeasurableSet.univ)
  have hright : ∫ x in A, (∫ y, f y * (g : ℝ → ℝ) (x - y))
      = ∫ y, f y * ∫ x in A, (g : ℝ → ℝ) (x - y) := by
    rw [← integral_indicator hA]
    have hswap : ∫ x, A.indicator (fun x => ∫ y, f y * (g : ℝ → ℝ) (x - y)) x
        = ∫ x, ∫ y, A.indicator (fun x' => f y * (g : ℝ → ℝ) (x' - y)) x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ A
      · simp only [Set.indicator_of_mem hx]
      · simp only [Set.indicator_of_notMem hx, integral_zero]
    rw [hswap, integral_integral_swap hprodint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change ∫ x, A.indicator (fun x' => f y * (g : ℝ → ℝ) (x' - y)) x
      = f y * ∫ x in A, (g : ℝ → ℝ) (x - y)
    rw [integral_indicator hA, integral_const_mul]
  rw [hleft, hright]

/-- `y ↦ x - y` preserves Lebesgue measure. -/
theorem measurePreserving_const_sub (x : ℝ) :
    MeasurePreserving (fun y : ℝ => x - y) volume volume :=
  (volume : Measure ℝ).measurePreserving_sub_left x

/-- Convolution is commutative — the change of variables `y ↦ x - y`. -/
theorem bconv_comm {f : ℝ → ℝ} (hf : Integrable f) (g : X) :
    bconv f g = bconv (g : ℝ → ℝ) (hf.toL1 f) := by
  refine Lp.ext ((coeFn_bconv hf g).trans ?_)
  refine Filter.EventuallyEq.symm
    ((coeFn_bconv (L1.integrable_coeFn g) (hf.toL1 f)).trans ?_)
  filter_upwards with x
  have hswap : ∫ y, (g : ℝ → ℝ) y * ((hf.toL1 f : X) : ℝ → ℝ) (x - y)
      = ∫ y, (g : ℝ → ℝ) y * f (x - y) := by
    refine integral_congr_ae ?_
    filter_upwards [(measurePreserving_const_sub x).quasiMeasurePreserving.ae
      (Integrable.coeFn_toL1 hf)] with y hy
    rw [hy]
  have hkey : ∫ y, (g : ℝ → ℝ) y * f (x - y) = ∫ y, f y * (g : ℝ → ℝ) (x - y) := by
    rw [← integral_sub_left_eq_self (fun y => f y * (g : ℝ → ℝ) (x - y)) volume x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change (g : ℝ → ℝ) y * f (x - y) = f (x - y) * (g : ℝ → ℝ) (x - (x - y))
    rw [sub_sub_cancel, mul_comm]
  rw [hswap, hkey]

/-! ## `μ * f` as a Bochner integral -/

/-- `y ↦ T_y f` is `μ`-integrable for every finite `μ`: continuous, hence strongly measurable,
and bounded by `‖f‖`. -/
theorem integrable_transL1 (μ : Measure ℝ) [IsFiniteMeasure μ] (f : X) :
    Integrable (fun y => transL1 y f) μ :=
  Integrable.mono' (integrable_const ‖f‖) (continuous_transL1 f).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => norm_transL1_le y f)

/-- `μ * f = ∫ T_y f dμ(y)`, as an `X`-valued Bochner integral. -/
noncomputable def bconvM (μ : Measure ℝ) (f : X) : X := ∫ y, transL1 y f ∂μ

/-- **The Bochner form of `mconvL1`.** -/
theorem bconvM_eq_mconvL1 (μ : Measure ℝ) [IsFiniteMeasure μ] (f : X) :
    bconvM μ f = mconvL1 μ f := by
  refine Lp.ext ?_
  refine Filter.EventuallyEq.trans ?_ (coeFn_mconvL1 μ f).symm
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun A _ _ => (L1.integrable_coeFn (bconvM μ f)).integrableOn)
    (fun A _ _ => (integrable_mconv μ (Lp.aestronglyMeasurable f)
      (L1.integrable_coeFn f)).integrableOn) fun A hA _ => ?_
  have hleft : ∫ x in A, (bconvM μ f : ℝ → ℝ) x
      = ∫ y, (∫ x in A, (f : ℝ → ℝ) (x - y)) ∂μ := by
    rw [← setIntegralCLM_apply A (bconvM μ f), bconvM,
      ← ContinuousLinearMap.integral_comp_comm _ (integrable_transL1 μ f)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change ∫ x in A, ((transL1 y f : X) : ℝ → ℝ) x = ∫ x in A, (f : ℝ → ℝ) (x - y)
    exact integral_congr_ae ((coeFn_transL1 y f).restrict)
  have hprodint : Integrable
      (Function.uncurry fun x y : ℝ => A.indicator (fun x' => (f : ℝ → ℝ) (x' - y)) x)
      (volume.prod μ) := by
    have hset : (Function.uncurry fun x y : ℝ =>
          A.indicator (fun x' => (f : ℝ → ℝ) (x' - y)) x)
        = (A ×ˢ (univ : Set ℝ)).indicator
          (Function.uncurry fun x y : ℝ => (f : ℝ → ℝ) (x - y)) := by
      funext p
      change A.indicator (fun x' => (f : ℝ → ℝ) (x' - p.2)) p.1
        = (A ×ˢ (univ : Set ℝ)).indicator
          (fun q : ℝ × ℝ => (f : ℝ → ℝ) (q.1 - q.2)) p
      by_cases hp : p.1 ∈ A
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (by simp [hp])]
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (by simp [hp])]
    rw [hset]
    exact (integrable_uncurry_sub μ (Lp.aestronglyMeasurable f)
      (L1.integrable_coeFn f)).indicator (hA.prod MeasurableSet.univ)
  have hright : ∫ x in A, mconv μ (f : ℝ → ℝ) x
      = ∫ y, (∫ x in A, (f : ℝ → ℝ) (x - y)) ∂μ := by
    rw [← integral_indicator hA]
    have hswap : ∫ x, A.indicator (mconv μ (f : ℝ → ℝ)) x
        = ∫ x, ∫ y, A.indicator (fun x' => (f : ℝ → ℝ) (x' - y)) x ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ A
      · simp only [Set.indicator_of_mem hx, mconv_apply]
      · simp only [Set.indicator_of_notMem hx, integral_zero]
    rw [hswap, integral_integral_swap hprodint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change ∫ x, A.indicator (fun x' => (f : ℝ → ℝ) (x' - y)) x
      = ∫ x in A, (f : ℝ → ℝ) (x - y)
    rw [integral_indicator hA]
  rw [hleft, hright]

/-! ## Pairing with a bounded functional

For `Ψ : X →L[ℝ] F` the map `y ↦ Ψ (T_y f)` is continuous — translation acts continuously on
`L¹` — and bounded by `‖Ψ‖ ‖f‖`. Taking `F = ℝ` it is a legitimate test function for weak
convergence; taking `F` an arbitrary Banach space is what `apply_mconvL1_general` states, a
strict generalization with no article twin.
-/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **`Ψ (μ * f) = ∫ Ψ (T_y f) dμ(y)`**, for a bounded functional with values in any Banach
space. -/
theorem apply_mconvL1_general (Ψ : X →L[ℝ] F) (μ : Measure ℝ) [IsFiniteMeasure μ] (f : X) :
    Ψ (mconvL1 μ f) = ∫ y, Ψ (transL1 y f) ∂μ := by
  rw [← bconvM_eq_mconvL1, bconvM,
    ← ContinuousLinearMap.integral_comp_comm _ (integrable_transL1 μ f)]

/-- `y ↦ Ψ (T_y f)`, as a bounded continuous function. -/
noncomputable def pairTrans (Ψ : X →L[ℝ] ℝ) (f : X) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun y => Ψ (transL1 y f))
    (Ψ.continuous.comp (continuous_transL1 f)) (‖Ψ‖ * ‖f‖) fun y =>
    (Ψ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_transL1_le y f) (norm_nonneg _))

@[simp] lemma pairTrans_apply (Ψ : X →L[ℝ] ℝ) (f : X) (y : ℝ) :
    pairTrans Ψ f y = Ψ (transL1 y f) := rfl

/-- **`Ψ (μ * f) = ∫ Ψ (T_y f) dμ(y)`.** -/
theorem apply_mconvL1 (Ψ : X →L[ℝ] ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] (f : X) :
    Ψ (mconvL1 μ f) = ∫ y, pairTrans Ψ f y ∂μ :=
  apply_mconvL1_general Ψ μ f

/-- **`Ψ (g * f) = ∫ g(y) Ψ (T_y f) dy`**, the density counterpart. -/
theorem apply_bconv (Ψ : X →L[ℝ] ℝ) {g : ℝ → ℝ} (hg : Integrable g) (f : X) :
    Ψ (bconv g f) = ∫ y, g y * pairTrans Ψ f y := by
  rw [bconv, ← ContinuousLinearMap.integral_comp_comm _ (integrable_smul_transL1 hg f)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change Ψ (g y • transL1 y f) = g y * Ψ (transL1 y f)
  rw [ContinuousLinearMap.map_smul, smul_eq_mul]

end ScaleSpace
