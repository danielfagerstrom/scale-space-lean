/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# `L¹(ℝ)`, translation, reflection, dilation, and convolution by a measure

Slice 1 of E-0009 (hub `proposals/E-0009.md`), moved from Paper I's `Operator.lean` /
`OperatorL1.lean` / `Family.lean` and Paper V's `SpatialLine/Basic.lean` /
`ConvolutionOperator.lean` / `Pairing.lean`, where the two developments carried this analysis as
byte-identical copies (`offices/engineer/notes/2026-09-19-lean-duplication-survey.md` §§ 3, 6).
Neither article is `require`d here; the two copies are collapsed into one, under `ScaleSpace`.

## Reflection and dilation (Q-0301)

Q-0187 left Paper V's reflection `reflL1`/`reflₗ` and dilation `dilate`/`dilₗ`/`dilL1` behind as
spatial-specific. Q-0301 moved them in from `SpatialLine/Basic.lean` at Paper V's `v0.1`: a second
spatial module (Paper VII) needs them, with the cascade-family vocabulary stated over them
(`ScaleSpaceCore.Family`), which is case (c) of the second-demand test (hub `RELEASES.md`
§ "Dependencies between modules"). What the convolution operator does against them
(`mconvL1_reflL1`, `dilL1_comp_mconvL1`) is in `ScaleSpaceCore.Transport`, because the reflection
clause is stated with `IsSymmetric` (`ScaleSpaceCore.Transform`).

## Design

* `X = ℝ →₁[volume] ℝ`, real, and the operators are `X →L[ℝ] X`.
* `dilate lam f = lam⁻¹ f (lam⁻¹ ·)` — the mass-preserving normalisation, which is what makes
  `dilL1` an isometry of `L¹` and matches the measure-side dilation, pushforward along
  `x ↦ lam * x`.
* `mconv μ f x = ∫ y, f (x - y) ∂μ`, packaged as the bounded operator `mconvL1`; the six
  properties below are what a translation- and reflection-covariant, positivity- and
  mass-preserving convolution family needs of it, short of the reflection clause.
-/

namespace ScaleSpace

open MeasureTheory Set
open scoped ENNReal

/-- `X = L¹(ℝ)`. -/
noncomputable abbrev X := ℝ →₁[volume] ℝ

/-- The positive cone `L¹₊`. -/
def IsNonneg (f : X) : Prop := 0 ≤ᵐ[volume] (f : ℝ → ℝ)

/-! ## Translation -/

/-- `x ↦ x - a` preserves Lebesgue measure. -/
theorem measurePreserving_sub_const (a : ℝ) :
    MeasurePreserving (fun x : ℝ => x - a) volume volume := by
  simpa [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure ℝ) (-a)

theorem translate_congr_ae (a : ℝ) {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) :
    (fun x => f (x - a)) =ᵐ[volume] fun x => g (x - a) :=
  (measurePreserving_sub_const a).quasiMeasurePreserving.ae h

theorem integrable_translate {f : ℝ → ℝ} (hf : Integrable f) (a : ℝ) :
    Integrable (fun x => f (x - a)) :=
  ((measurePreserving_sub_const a).integrable_comp hf.aestronglyMeasurable).mpr hf

/-- `T_a f = f(· - a)` as a linear map on `L¹`. -/
noncomputable def transₗ (a : ℝ) : (ℝ →₁[volume] ℝ) →ₗ[ℝ] (ℝ →₁[volume] ℝ) where
  toFun f := (integrable_translate (L1.integrable_coeFn f) a).toL1 _
  map_add' f g := by
    rw [← Integrable.toL1_add]
    exact (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr (translate_congr_ae a (Lp.coeFn_add f g))
  map_smul' c f := by
    simp only [RingHom.id_apply]
    rw [← Integrable.toL1_smul']
    exact (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr (translate_congr_ae a (Lp.coeFn_smul c f))

/-- **Translation is an isometry of `L¹`** — Lebesgue measure is translation invariant. -/
noncomputable def transL1 (a : ℝ) : (ℝ →₁[volume] ℝ) →L[ℝ] (ℝ →₁[volume] ℝ) :=
  (transₗ a).mkContinuous 1 fun f => by
    rw [transₗ, LinearMap.coe_mk, AddHom.coe_mk, Integrable.norm_toL1_eq_lintegral_enorm,
      one_mul, Lp.norm_def, eLpNorm_one_eq_lintegral_enorm]
    exact le_of_eq (congrArg ENNReal.toReal
      (lintegral_sub_right_eq_self (fun x => ‖(f : ℝ → ℝ) x‖ₑ) a))

lemma coeFn_transL1 (a : ℝ) (f : ℝ →₁[volume] ℝ) :
    transL1 a f =ᵐ[volume] fun x => (f : ℝ → ℝ) (x - a) :=
  Integrable.coeFn_toL1 (integrable_translate (L1.integrable_coeFn f) a)

/-! ## Reflection

`(R f)(x) = f(-x)`, an isometric involution of `L¹`, because Lebesgue measure on the line is
invariant under `x ↦ -x`.
-/

/-- `x ↦ -x` preserves Lebesgue measure. -/
theorem measurePreserving_neg' : MeasurePreserving (fun x : ℝ => -x) volume volume :=
  Measure.measurePreserving_neg (volume : Measure ℝ)

theorem reflect_congr_ae {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) :
    (fun x => f (-x)) =ᵐ[volume] fun x => g (-x) :=
  measurePreserving_neg'.quasiMeasurePreserving.ae h

theorem integrable_reflect {f : ℝ → ℝ} (hf : Integrable f) :
    Integrable (fun x => f (-x)) :=
  (measurePreserving_neg'.integrable_comp hf.aestronglyMeasurable).mpr hf

/-- `R f = f(-·)` as a linear map on `L¹`. -/
noncomputable def reflₗ : (ℝ →₁[volume] ℝ) →ₗ[ℝ] (ℝ →₁[volume] ℝ) where
  toFun f := (integrable_reflect (L1.integrable_coeFn f)).toL1 _
  map_add' f g := by
    rw [← Integrable.toL1_add]
    exact (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr (reflect_congr_ae (Lp.coeFn_add f g))
  map_smul' c f := by
    simp only [RingHom.id_apply]
    rw [← Integrable.toL1_smul']
    exact (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr (reflect_congr_ae (Lp.coeFn_smul c f))

/-- **Reflection is an isometry of `L¹`.** The change of variables is `x ↦ -x`, a measurable
equivalence preserving Lebesgue measure, so the constant is `1`. -/
noncomputable def reflL1 : (ℝ →₁[volume] ℝ) →L[ℝ] (ℝ →₁[volume] ℝ) :=
  reflₗ.mkContinuous 1 fun f => by
    rw [reflₗ, LinearMap.coe_mk, AddHom.coe_mk, Integrable.norm_toL1_eq_lintegral_enorm,
      one_mul, Lp.norm_def, eLpNorm_one_eq_lintegral_enorm]
    refine le_of_eq (congrArg ENNReal.toReal ?_)
    exact measurePreserving_neg'.lintegral_comp_emb
      (Homeomorph.neg ℝ).toMeasurableEquiv.measurableEmbedding fun x => ‖(f : ℝ → ℝ) x‖ₑ

lemma coeFn_reflL1 (f : ℝ →₁[volume] ℝ) :
    reflL1 f =ᵐ[volume] fun x => (f : ℝ → ℝ) (-x) :=
  Integrable.coeFn_toL1 (integrable_reflect (L1.integrable_coeFn f))

/-! ## Dilation -/

/-- Multiplication by a nonzero constant is quasi-measure-preserving. -/
theorem quasiMeasurePreserving_const_mul {c : ℝ} (hc : c ≠ 0) :
    Measure.QuasiMeasurePreserving (fun x : ℝ => c * x) volume volume := by
  refine ⟨measurable_const_mul c, ?_⟩
  rw [Real.map_volume_mul_left hc]
  exact Measure.smul_absolutelyContinuous

/-- `D_lam f = lam⁻¹ f(lam⁻¹ ·)`, the mass-preserving normalisation. -/
noncomputable def dilate (lam : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun x => lam⁻¹ * f (lam⁻¹ * x)

theorem dilate_congr_ae {lam : ℝ} (hlam : lam ≠ 0) {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) :
    dilate lam f =ᵐ[volume] dilate lam g := by
  filter_upwards [(quasiMeasurePreserving_const_mul (inv_ne_zero hlam)).ae h] with x hx
  simp only [dilate, hx]

theorem integrable_dilate {f : ℝ → ℝ} (hf : Integrable f) {lam : ℝ} (hlam : lam ≠ 0) :
    Integrable (dilate lam f) :=
  (Integrable.comp_mul_left' hf (inv_ne_zero hlam)).const_mul lam⁻¹

/-- The change of variables the isometry rests on: `∫⁻ g(c x) dx = |c⁻¹| ∫⁻ g`. -/
theorem lintegral_comp_const_mul {c : ℝ} (hc : c ≠ 0) {g : ℝ → ℝ≥0∞} (hg : AEMeasurable g) :
    ∫⁻ x, g (c * x) = ENNReal.ofReal |c⁻¹| * ∫⁻ x, g x := by
  have hmap := Real.map_volume_mul_left hc
  calc ∫⁻ x, g (c * x)
      = ∫⁻ y, g y ∂(Measure.map (fun x : ℝ => c * x) volume) := by
        rw [lintegral_map' (hg.mono_ac (by rw [hmap]; exact Measure.smul_absolutelyContinuous))
          (measurable_const_mul c).aemeasurable]
    _ = ENNReal.ofReal |c⁻¹| * ∫⁻ x, g x := by
        rw [hmap, lintegral_smul_measure, smul_eq_mul]

/-- `D_lam` as a linear map on `L¹`. -/
noncomputable def dilₗ {lam : ℝ} (hlam : lam ≠ 0) :
    (ℝ →₁[volume] ℝ) →ₗ[ℝ] (ℝ →₁[volume] ℝ) where
  toFun f := (integrable_dilate (L1.integrable_coeFn f) hlam).toL1 _
  map_add' f g := by
    rw [← Integrable.toL1_add]
    refine (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr ?_
    refine (dilate_congr_ae hlam (Lp.coeFn_add f g)).trans ?_
    filter_upwards with x
    simp only [dilate, Pi.add_apply, mul_add]
  map_smul' c f := by
    simp only [RingHom.id_apply]
    rw [← Integrable.toL1_smul']
    refine (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr ?_
    refine (dilate_congr_ae hlam (Lp.coeFn_smul c f)).trans ?_
    filter_upwards with x
    simp only [dilate, Pi.smul_apply, smul_eq_mul]
    ring

/-- **Dilation is an isometry of `L¹`** for `lam > 0`. -/
noncomputable def dilL1 {lam : ℝ} (hlam : 0 < lam) :
    (ℝ →₁[volume] ℝ) →L[ℝ] (ℝ →₁[volume] ℝ) :=
  (dilₗ hlam.ne').mkContinuous 1 fun f => by
    rw [dilₗ, LinearMap.coe_mk, AddHom.coe_mk, Integrable.norm_toL1_eq_lintegral_enorm,
      one_mul, Lp.norm_def, eLpNorm_one_eq_lintegral_enorm]
    refine le_of_eq (congrArg ENNReal.toReal ?_)
    have henorm : ∀ x : ℝ, ‖dilate lam (f : ℝ → ℝ) x‖ₑ
        = ENNReal.ofReal lam⁻¹ * ‖(f : ℝ → ℝ) (lam⁻¹ * x)‖ₑ := by
      intro x
      simp only [dilate, enorm_mul, Real.enorm_eq_ofReal (inv_nonneg.mpr hlam.le)]
    simp only [henorm]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_comp_const_mul (inv_ne_zero hlam.ne') (Lp.aestronglyMeasurable f).enorm,
      ← mul_assoc, inv_inv, abs_of_pos hlam, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hlam)),
      inv_mul_cancel₀ hlam.ne', ENNReal.ofReal_one, one_mul]

lemma coeFn_dilL1 {lam : ℝ} (hlam : 0 < lam) (f : ℝ →₁[volume] ℝ) :
    dilL1 hlam f =ᵐ[volume] dilate lam (f : ℝ → ℝ) :=
  Integrable.coeFn_toL1 (integrable_dilate (L1.integrable_coeFn f) hlam.ne')

/-! ## Convolution by a measure -/

/-- `(μ * f)(x) = ∫ f(x - y) μ(dy)`. -/
noncomputable def mconv (μ : Measure ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun x => ∫ y, f (x - y) ∂μ

lemma mconv_apply (μ : Measure ℝ) (f : ℝ → ℝ) (x : ℝ) :
    mconv μ f x = ∫ y, f (x - y) ∂μ := rfl

theorem lintegral_lintegral_sub_eq (μ : Measure ℝ) [SFinite μ] {g : ℝ → ℝ≥0∞}
    (hg : AEMeasurable g) :
    ∫⁻ x, (∫⁻ y, g (x - y) ∂μ) = μ univ * ∫⁻ x, g x := by
  have huncurry : AEMeasurable (Function.uncurry fun x y : ℝ => g (x - y)) (volume.prod μ) :=
    hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume μ)
  calc ∫⁻ x, (∫⁻ y, g (x - y) ∂μ)
      = ∫⁻ y, (∫⁻ x, g (x - y) ∂volume) ∂μ := lintegral_lintegral_swap huncurry
    _ = ∫⁻ _, (∫⁻ x, g x) ∂μ := lintegral_congr fun y => lintegral_sub_right_eq_self _ y
    _ = μ univ * ∫⁻ x, g x := by rw [lintegral_const, mul_comm]

theorem lintegral_enorm_mconv_le (μ : Measure ℝ) [SFinite μ] {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f) :
    ∫⁻ x, ‖mconv μ f x‖ₑ ≤ μ univ * ∫⁻ x, ‖f x‖ₑ := by
  calc ∫⁻ x, ‖mconv μ f x‖ₑ ≤ ∫⁻ x, (∫⁻ y, ‖f (x - y)‖ₑ ∂μ) :=
        lintegral_mono fun x => enorm_integral_le_lintegral_enorm _
    _ = μ univ * ∫⁻ x, ‖f x‖ₑ := lintegral_lintegral_sub_eq μ hf.enorm

theorem integrable_uncurry_sub (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f) (hfi : Integrable f) :
    Integrable (Function.uncurry fun x y : ℝ => f (x - y)) (volume.prod μ) := by
  have hm : AEStronglyMeasurable (Function.uncurry fun x y : ℝ => f (x - y)) (volume.prod μ) :=
    hf.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume μ)
  refine ⟨hm, ?_⟩
  have hprod : ∫⁻ p, ‖Function.uncurry (fun x y : ℝ => f (x - y)) p‖ₑ ∂(volume.prod μ)
      = ∫⁻ x, (∫⁻ y, ‖f (x - y)‖ₑ ∂μ) := lintegral_prod _ hm.enorm
  rw [hasFiniteIntegral_iff_enorm, hprod, lintegral_lintegral_sub_eq μ hf.enorm]
  exact ENNReal.mul_lt_top (measure_lt_top μ univ) hfi.2

/-- `μ * f` is integrable. -/
theorem integrable_mconv (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f) (hfi : Integrable f) : Integrable (mconv μ f) :=
  (integrable_uncurry_sub μ hf hfi).integral_prod_left

theorem ae_ae_sub_of_ae (μ : Measure ℝ) [SFinite μ] {p : ℝ → Prop} (h : ∀ᵐ u ∂volume, p u) :
    ∀ᵐ x ∂volume, ∀ᵐ y ∂μ, p (x - y) :=
  Measure.ae_ae_of_ae_prod ((quasiMeasurePreserving_sub volume μ).ae h)

theorem mconv_congr_ae (μ : Measure ℝ) [SFinite μ] {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) :
    mconv μ f =ᵐ[volume] mconv μ g := by
  filter_upwards [ae_ae_sub_of_ae μ h] with x hx
  exact integral_congr_ae hx

theorem mconv_add_ae (μ : Measure ℝ) [IsFiniteMeasure μ] {f g : ℝ → ℝ}
    (hf : AEStronglyMeasurable f) (hfi : Integrable f)
    (hg : AEStronglyMeasurable g) (hgi : Integrable g) :
    mconv μ (f + g) =ᵐ[volume] mconv μ f + mconv μ g := by
  filter_upwards [(integrable_uncurry_sub μ hf hfi).prod_right_ae,
    (integrable_uncurry_sub μ hg hgi).prod_right_ae] with x h1 h2
  simp only [Function.uncurry] at h1 h2
  simp only [mconv_apply, Pi.add_apply]
  exact integral_add h1 h2

theorem mconv_smul (μ : Measure ℝ) (c : ℝ) (f : ℝ → ℝ) :
    mconv μ (c • f) = c • mconv μ f := by
  funext x
  simp only [mconv_apply, Pi.smul_apply, smul_eq_mul, integral_const_mul]

/-- `Φ f = μ * f` as a linear map on `L¹`. -/
noncomputable def mconvₗ (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (ℝ →₁[volume] ℝ) →ₗ[ℝ] (ℝ →₁[volume] ℝ) where
  toFun f := (integrable_mconv μ (Lp.aestronglyMeasurable f) (L1.integrable_coeFn f)).toL1 _
  map_add' f g := by
    rw [← Integrable.toL1_add]
    refine (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr ?_
    refine (mconv_congr_ae μ (Lp.coeFn_add f g)).trans ?_
    exact mconv_add_ae μ (Lp.aestronglyMeasurable f) (L1.integrable_coeFn f)
      (Lp.aestronglyMeasurable g) (L1.integrable_coeFn g)
  map_smul' c f := by
    simp only [RingHom.id_apply]
    rw [← Integrable.toL1_smul']
    refine (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr ?_
    refine (mconv_congr_ae μ (Lp.coeFn_smul c f)).trans ?_
    rw [mconv_smul]

private lemma norm_L1_eq (f : ℝ →₁[volume] ℝ) : ‖f‖ = (∫⁻ x, ‖(f : ℝ → ℝ) x‖ₑ).toReal := by
  rw [Lp.norm_def, eLpNorm_one_eq_lintegral_enorm]

/-- **`Φ` is a bounded operator on `L¹`.** -/
noncomputable def mconvL1 (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (ℝ →₁[volume] ℝ) →L[ℝ] (ℝ →₁[volume] ℝ) :=
  (mconvₗ μ).mkContinuous (μ univ).toReal fun f => by
    rw [mconvₗ, LinearMap.coe_mk, AddHom.coe_mk,
      Integrable.norm_toL1_eq_lintegral_enorm, norm_L1_eq, ← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono ?_ (lintegral_enorm_mconv_le μ (Lp.aestronglyMeasurable f))
    exact ENNReal.mul_ne_top (measure_ne_top μ univ) (L1.integrable_coeFn f).2.ne

lemma coeFn_mconvL1 (μ : Measure ℝ) [IsFiniteMeasure μ] (f : ℝ →₁[volume] ℝ) :
    mconvL1 μ f =ᵐ[volume] mconv μ (f : ℝ → ℝ) :=
  Integrable.coeFn_toL1 (integrable_mconv μ (Lp.aestronglyMeasurable f) (L1.integrable_coeFn f))

/-! ## What `mconvL1` does: translation covariance, positivity, mass, composition -/

variable {μ : Measure ℝ}

theorem mconv_comp_sub (μ : Measure ℝ) (f : ℝ → ℝ) (a : ℝ) :
    mconv μ (fun x => f (x - a)) = fun x => mconv μ f (x - a) := by
  funext x
  simp only [mconv_apply, sub_right_comm]

theorem mconv_nonneg (μ : Measure ℝ) {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (x : ℝ) :
    0 ≤ mconv μ f x := integral_nonneg fun _ => hf _

/-- `∫ (μ * f) = ‖μ‖ ∫ f`. -/
theorem integral_mconv (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f) (hfi : Integrable f) :
    ∫ x, mconv μ f x = (μ univ).toReal * ∫ x, f x := by
  simp only [mconv_apply]
  rw [integral_integral_swap (integrable_uncurry_sub μ hf hfi)]
  simp_rw [integral_sub_right_eq_self]
  rw [integral_const, smul_eq_mul, measureReal_def]

/-- `ν * (μ * f) = (μ ∗ ν) * f`, a.e. -/
theorem mconv_conv (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f) (hfi : Integrable f) :
    mconv ν (mconv μ f) =ᵐ[volume] mconv (μ ∗ ν) f := by
  filter_upwards [(integrable_uncurry_sub (μ ∗ ν) hf hfi).prod_right_ae] with x hx
  simp only [Function.uncurry] at hx
  have hadd : AEMeasurable (fun p : ℝ × ℝ => p.1 + p.2) (μ.prod ν) :=
    (measurable_fst.add measurable_snd).aemeasurable
  have hprod : Integrable (fun p : ℝ × ℝ => f (x - (p.1 + p.2))) (μ.prod ν) := by
    rw [Measure.conv] at hx
    exact (integrable_map_measure hx.aestronglyMeasurable hadd).mp hx
  have hmap : ∫ u, f (x - u) ∂(μ ∗ ν) = ∫ p : ℝ × ℝ, f (x - (p.1 + p.2)) ∂(μ.prod ν) := by
    rw [Measure.conv]
    exact integral_map hadd (by rw [← Measure.conv]; exact hx.aestronglyMeasurable)
  simp only [mconv_apply]
  rw [hmap, integral_prod_symm _ hprod]
  simp only [sub_add_eq_sub_sub, sub_right_comm]

theorem mconv_dirac_zero (f : ℝ → ℝ) : mconv (Measure.dirac 0) f = f := by
  funext x
  rw [mconv_apply, integral_dirac, sub_zero]

/-- Equal measures give equal operators. Needed because `mconvL1` carries an `IsFiniteMeasure`
instance argument, so `rw` on the measure produces an ill-typed motive. -/
theorem mconvL1_congr {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : μ = ν) :
    mconvL1 μ = mconvL1 ν := by
  subst h
  congr 1

/-- `Φ` is a contraction for a probability measure. -/
theorem norm_mconvL1_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : X) :
    ‖mconvL1 μ f‖ ≤ ‖f‖ := by
  have hop : ‖mconvL1 μ‖ ≤ 1 := by
    rw [mconvL1]
    refine le_trans (LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _) ?_
    rw [measure_univ, ENNReal.toReal_one]
  calc ‖mconvL1 μ f‖ ≤ ‖mconvL1 μ‖ * ‖f‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖f‖ := by nlinarith [norm_nonneg f]
    _ = ‖f‖ := one_mul _

/-- `mconvL1` commutes with translation. -/
theorem mconvL1_transL1 [IsFiniteMeasure μ] (a : ℝ) (f : X) :
    mconvL1 μ (transL1 a f) = transL1 a (mconvL1 μ f) := by
  refine Lp.ext ?_
  refine (coeFn_mconvL1 μ (transL1 a f)).trans ?_
  refine (mconv_congr_ae μ (coeFn_transL1 a f)).trans ?_
  rw [mconv_comp_sub]
  refine Filter.EventuallyEq.symm ?_
  refine (coeFn_transL1 a (mconvL1 μ f)).trans ?_
  exact translate_congr_ae a (coeFn_mconvL1 μ f)

theorem isNonneg_mconvL1 [IsFiniteMeasure μ] (f : X) (hf : IsNonneg f) :
    IsNonneg (mconvL1 μ f) := by
  filter_upwards [coeFn_mconvL1 μ f, ae_ae_sub_of_ae μ hf] with x hcoe hx
  rw [Pi.zero_apply, hcoe, mconv_apply]
  exact integral_nonneg_of_ae hx

/-- `mconvL1` preserves total mass, for every `f`: the Tonelli identity does not see the sign. -/
theorem integral_mconvL1 [IsProbabilityMeasure μ] (f : X) :
    ∫ x, ((mconvL1 μ f : X) : ℝ → ℝ) x = ∫ x, (f : ℝ → ℝ) x := by
  rw [integral_congr_ae (coeFn_mconvL1 μ f),
    integral_mconv μ (Lp.aestronglyMeasurable f) (L1.integrable_coeFn f),
    measure_univ, ENNReal.toReal_one, one_mul]

/-- Composing the operators convolves the measures. -/
theorem mconvL1_comp (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (mconvL1 ν).comp (mconvL1 μ) = mconvL1 (μ ∗ ν) := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  refine ((coeFn_mconvL1 ν (mconvL1 μ f)).trans
    (mconv_congr_ae ν (coeFn_mconvL1 μ f))).trans ?_
  refine Filter.EventuallyEq.trans ?_ (coeFn_mconvL1 (μ ∗ ν) f).symm
  exact mconv_conv μ ν (Lp.aestronglyMeasurable f) (L1.integrable_coeFn f)

/-- `δ₀` acts as the identity on `L¹`. -/
theorem mconvL1_dirac_zero : mconvL1 (Measure.dirac (0 : ℝ)) = ContinuousLinearMap.id ℝ X := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  refine (coeFn_mconvL1 _ f).trans ?_
  rw [mconv_dirac_zero]
  rfl

/-! ## Pairing against a bounded test function -/

/-- **Pairing against a bounded function.** `∫ g · (μ * f) = ∫∫ g(t) f(t - r)`. The
integrability Fubini needs is `integrable_uncurry_sub`, dominated by `C`, which is why `g` is
asked to be bounded rather than integrable. -/
theorem integral_mul_mconv (μ : Measure ℝ) [IsFiniteMeasure μ] {f g : ℝ → ℝ}
    (hf : AEStronglyMeasurable f) (hfi : Integrable f)
    (hg : Measurable g) {C : ℝ} (hgb : ∀ t, |g t| ≤ C) :
    ∫ t, g t * mconv μ f t = ∫ r, (∫ t, g t * f (t - r)) ∂μ := by
  have hFm : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1 * f (p.1 - p.2)) (volume.prod μ) :=
    ((hg.comp measurable_fst).aestronglyMeasurable).mul
      (hf.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume μ))
  have hdom : Integrable (fun p : ℝ × ℝ => C * ‖f (p.1 - p.2)‖) (volume.prod μ) :=
    ((integrable_uncurry_sub μ hf hfi).norm).const_mul C
  have hFi : Integrable (fun p : ℝ × ℝ => g p.1 * f (p.1 - p.2)) (volume.prod μ) := by
    refine hdom.mono' hFm (Filter.Eventually.of_forall fun p => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact hgb p.1) (norm_nonneg _)
  calc ∫ t, g t * mconv μ f t
      = ∫ t, (∫ r, g t * f (t - r) ∂μ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        change g t * mconv μ f t = ∫ r, g t * f (t - r) ∂μ
        rw [mconv_apply, integral_const_mul]
    _ = ∫ r, (∫ t, g t * f (t - r)) ∂μ := integral_integral_swap hFi

end ScaleSpace
