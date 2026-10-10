/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import ScaleSpaceCore.InverseGamma
import ScaleSpaceCore.BrownianDensity

/-!
# The Student-t law as a Gaussian variance mixture, and its transform

Home: none (a result of the literature, cited: the classical normal variance-mixture
representation of the Student-t law, and `besselK` by its integral representation, DLMF 10.32.9;
second-demand consumers — Paper V's corner and Student modules, Paper VII's `IsotropicBridge`
`prop:isotropic-bridge-student` — do not yet tag this shared declaration with `\lean`)

The Brownian mixture over the inverse-gamma delay law of shape `a` is the Student-t law with `2a`
degrees of freedom at scale `1` (`bridge_families_bessel`), and its cosine transform is
`2^{1-a}Γ(a)^{-1}|ω|^a K_a(|ω|)` for `ω ≠ 0` (`student_transform`), with `K_ν` the modified
Bessel function of the second kind (`besselK`).

Moved (Q-0363, SSL-8) from Paper V's cone export (`cone-v0.1`, `f28c066e`), statements unchanged
up to the namespace: `besselK` from `SpatialLine.CornerDefs`; `studentDensity` and `studentLaw`
from `SpatialLine.Corners`; `lintegral_exp_mul_of_even` from `SpatialLine.FirstPassage`;
`inverseGamma_brownian_integrand`, `integral_inverseGamma_brownian`, `studentDensity_pos`,
`lintegral_inverseGamma_brownian` and `bridge_families_bessel` from `SpatialLine.BridgeBessel`;
`lintegral_Ioi_rpow_exp_besselKernel`, `lintegral_cosh_exp_eq_besselK`, `besselK_neg`,
`lintegral_exp_neg_inverseGammaLaw`, `besselK_nonneg` and `student_transform` from
`SpatialLine.StudentTransform`. Second demand: Paper V's corner and Student modules, and Paper
VII's `IsotropicBridge` (`prop:isotropic-bridge-student`).

This module imports neither `ScaleSpaceCore.BridgeExponents` nor anything stated in
`CausalAdmissible`: Paper V's package at `cone-v0.1` declares names in
`ScaleSpace.CausalAdmissible` that `ScaleSpaceCore.BridgeExponents` also declares, so a consumer
that imports Paper V's bridge modules can import this one beside them.

## The special function Mathlib does not have

Mathlib (v4.31.0) has no modified Bessel function, so `besselK` is defined by the integral
representation `K_ν(z) = ∫₀^∞ e^{-z\cosh u}\cosh(νu)\,du` (DLMF 10.32.9), valid for `z > 0`. For
`z ≤ 0` the integral diverges and the Bochner integral is junk. Only the two properties the
transform reads are proved here: `besselK_neg` (even in the order) and `besselK_nonneg`.

## The route

The mixture is computed at the densities: the substitution `w = 1/u` (`integral_comp_rpow_Ioi`
at `p = -1`) turns the mixture integral into a Gamma integral, and the computed value being
strictly positive (`studentDensity_pos`) forces the `ℝ≥0∞` integral to be finite without an
integrability proof. The transform conditions on the delay (`fourierCos_bind_brownianLaw`) and
evaluates the Laplace transform of the inverse-gamma law by the substitution `u = c e^v`, which
lands on the defining integral of `K_a` itself, so no Bessel asymptotic is used.
-/

namespace ScaleSpace

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology

/-! ## The modified Bessel function -/

/-- **`K_ν`**, the modified Bessel function of the second kind, by its integral representation
`K_ν(z) = ∫₀^∞ e^{-z\cosh u}\cosh(νu)\,du` (DLMF 10.32.9), valid for `z > 0`. -/
noncomputable def besselK (ν z : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), Real.exp (-(z * Real.cosh u)) * Real.cosh (ν * u)

/-! ## The Student-t law -/

/-- The Student-t density with `2a` degrees of freedom at spatial scale `t`:
`φ_t(x) = \frac{\Gamma(a+1/2)}{\sqrt\pi\,\Gamma(a)}\,t^{-1}(1 + (x/t)^2)^{-a-1/2}`.

The scaling convention is the one that makes the degrees of freedom `2a` rather than `a`; read
it together with the rate in the inverse-gamma law (`inverseGammaDensity`). -/
noncomputable def studentDensity (a t x : ℝ) : ℝ :=
  Real.Gamma (a + 1 / 2) / (Real.sqrt Real.pi * Real.Gamma a) * t⁻¹
    * (1 + (x / t) ^ 2) ^ (-a - 1 / 2)

/-- The Student-t law with `2a` degrees of freedom at spatial scale `t`. -/
noncomputable def studentLaw (a t : ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (studentDensity a t x)

/-! ## The reflection fold -/

/-- **The reflection fold at a general exponential weight.** For an even nonnegative `G`,
`∫_ℝ e^{pv}G(v)\,dv = 2∫_0^∞ \cosh(pv)G(v)\,dv`. -/
theorem lintegral_exp_mul_of_even {p : ℝ} {G : ℝ → ℝ} (hGm : Measurable G)
    (hGnn : ∀ v, 0 ≤ G v) (hGeven : ∀ v, G (-v) = G v) :
    (∫⁻ v, ENNReal.ofReal (Real.exp (p * v) * G v))
      = 2 * ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (Real.cosh (p * v) * G v) := by
  have hemb : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).toMeasurableEquiv.measurableEmbedding
  have hmp : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg volume
  have hpre : (fun x : ℝ => -x) ⁻¹' (Ioi (0 : ℝ)) = Iio (0 : ℝ) := by ext x; simp
  set g : ℝ → ℝ≥0∞ := fun v => ENNReal.ofReal (Real.exp (-(p * v)) * G v) with hgdef
  have hgm : Measurable g := by rw [hgdef]; fun_prop
  have hIio : (∫⁻ v in Iio (0 : ℝ), ENNReal.ofReal (Real.exp (p * v) * G v))
      = ∫⁻ v in Ioi (0 : ℝ), g v := by
    have hkey := hmp.setLIntegral_comp_preimage_emb hemb g (Ioi (0 : ℝ))
    rw [hpre] at hkey
    rw [← hkey]
    refine setLIntegral_congr_fun measurableSet_Iio fun v _ => ?_
    rw [hgdef]
    simp only
    rw [hGeven v, show -(p * -v) = p * v by ring]
  have hsplit := lintegral_add_compl (μ := (volume : Measure ℝ))
    (fun v => ENNReal.ofReal (Real.exp (p * v) * G v)) (measurableSet_Iio (a := (0 : ℝ)))
  rw [compl_Iio] at hsplit
  have hIci : (∫⁻ v in Ici (0 : ℝ), ENNReal.ofReal (Real.exp (p * v) * G v))
      = ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (p * v) * G v) :=
    setLIntegral_congr Ioi_ae_eq_Ici.symm
  rw [hIio, hIci] at hsplit
  rw [← hsplit, ← lintegral_add_left' (hgm.aemeasurable.restrict)]
  have hpt : ∀ v : ℝ, g v + ENNReal.ofReal (Real.exp (p * v) * G v)
      = 2 * ENNReal.ofReal (Real.cosh (p * v) * G v) := by
    intro v
    rw [hgdef]
    simp only
    rw [← ENNReal.ofReal_add (mul_nonneg (Real.exp_pos _).le (hGnn v))
        (mul_nonneg (Real.exp_pos _).le (hGnn v)),
      show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    rw [Real.cosh_eq]
    ring
  simp only [hpt]
  rw [lintegral_const_mul' _ _ (by norm_num)]

/-! ## The Brownian mixture over the inverse-gamma law is the Student-t law -/

/-- The mixture integrand of the Bessel corner, in the form the substitution wants:
`C·u^{-a-3/2}e^{-r/u}` with `r = (1+x²)/2`. -/
theorem inverseGamma_brownian_integrand (a x : ℝ) {u : ℝ} (hu : 0 < u) :
    inverseGammaDensity a u * brownianDensity u x
      = (2 ^ a * Real.Gamma a * Real.sqrt (2 * Real.pi))⁻¹
        * u ^ (-a - 3 / 2) * Real.exp (-((1 + x ^ 2) / 2 / u)) := by
  have hsqrt2pi : (0 : ℝ) < Real.sqrt (2 * Real.pi) := by
    apply Real.sqrt_pos.mpr; nlinarith [Real.two_le_pi]
  have hpow : u ^ (-a - 3 / 2 : ℝ) = u ^ (-a - 1 : ℝ) * (u ^ ((1 : ℝ) / 2))⁻¹ := by
    rw [← Real.rpow_neg hu.le, ← Real.rpow_add hu]
    congr 1
    ring
  have hexp : Real.exp (-(2 * u)⁻¹) * Real.exp (-x ^ 2 / (2 * u))
      = Real.exp (-((1 + x ^ 2) / 2 / u)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [inverseGammaDensity, Set.indicator_of_mem (mem_Ioi.mpr hu), brownianDensity_eq hu,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi), ← Real.sqrt_eq_rpow] at *
  rw [hpow, ← hexp]
  have hupos : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu
  field_simp

/-- **The normal variance-mixture computation.** The inverse-gamma mixture of Gaussian
densities is the Student-t density with `2a` degrees of freedom at scale `1`.

The substitution is `integral_comp_rpow_Ioi` at `p = -1`, which is exactly `w = 1/u`, and what
it leaves is `Real.integral_rpow_mul_exp_neg_mul_Ioi` at shape `a + 1/2` and rate
`(1+x²)/2`. -/
theorem integral_inverseGamma_brownian {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (∫ u in Ioi (0 : ℝ), inverseGammaDensity a u * brownianDensity u x)
      = studentDensity a 1 x := by
  set C : ℝ := (2 ^ a * Real.Gamma a * Real.sqrt (2 * Real.pi))⁻¹ with hC
  set r : ℝ := (1 + x ^ 2) / 2 with hr
  have hrpos : (0 : ℝ) < r := by rw [hr]; positivity
  have hstep1 : (∫ u in Ioi (0 : ℝ), inverseGammaDensity a u * brownianDensity u x)
      = ∫ u in Ioi (0 : ℝ), C * u ^ (-a - 3 / 2) * Real.exp (-(r / u)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    exact inverseGamma_brownian_integrand a x hu
  have hsub := integral_comp_rpow_Ioi
    (fun y : ℝ => C * y ^ (-a - 3 / 2) * Real.exp (-(r / y))) (p := -1) (by norm_num)
  have hstep2 : (∫ t in Ioi (0 : ℝ),
        (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) •
          (C * (t ^ (-1 : ℝ)) ^ (-a - 3 / 2) * Real.exp (-(r / t ^ (-1 : ℝ)))))
      = ∫ t in Ioi (0 : ℝ), C * (t ^ (a + 1 / 2 - 1) * Real.exp (-(r * t))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    have hinv : t ^ (-1 : ℝ) = t⁻¹ := Real.rpow_neg_one t
    have hpow : (t ^ (-1 : ℝ)) ^ (-a - 3 / 2 : ℝ) = t ^ (a + 3 / 2 : ℝ) := by
      rw [← Real.rpow_mul ht0.le]
      congr 1
      ring
    have hmul : t ^ ((-1 : ℝ) - 1) * t ^ (a + 3 / 2 : ℝ) = t ^ (a + 1 / 2 - 1 : ℝ) := by
      rw [← Real.rpow_add ht0]
      congr 1
      ring
    rw [hinv] at hpow
    rw [hinv, hpow, smul_eq_mul]
    have hdiv : r / t⁻¹ = r * t := by field_simp
    rw [hdiv]
    have h1 : |(-1 : ℝ)| = 1 := by norm_num
    rw [h1, one_mul, ← hmul]
    ring
  rw [hstep1, ← hsub, hstep2, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith : (0 : ℝ) < a + 1 / 2) hrpos]
  have h2 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hGa : (0 : ℝ) < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hpi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h2a : (0 : ℝ) < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
  have hone : (1 / r : ℝ) = 2 / (1 + x ^ 2) := by rw [hr]; field_simp
  have hsplit : (2 : ℝ) ^ (a + 1 / 2) = 2 ^ a * Real.sqrt 2 := by
    rw [Real.rpow_add (by norm_num), Real.sqrt_eq_rpow]
  have hneg : ((1 + x ^ 2) : ℝ) ^ (-a - 1 / 2) = (((1 + x ^ 2) : ℝ) ^ (a + 1 / 2))⁻¹ := by
    rw [← Real.rpow_neg h2.le]
    congr 1
    ring
  have hsq2pi : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
    Real.sqrt_mul (by norm_num) _
  rw [studentDensity, hone, Real.div_rpow (by norm_num) h2.le, hsplit, hC, hsq2pi]
  simp only [div_one, inv_one]
  rw [hneg]
  have hd : (0 : ℝ) < ((1 + x ^ 2) : ℝ) ^ (a + 1 / 2) := Real.rpow_pos_of_pos h2 _
  field_simp

/-- The Student-t density is strictly positive. This is what makes the `ℝ≥0∞` integral finite
without an integrability proof: `∫⁻` infinite would read as `0` after `toReal`. -/
theorem studentDensity_pos {a : ℝ} (ha : 0 < a) (x : ℝ) : 0 < studentDensity a 1 x := by
  unfold studentDensity
  have h1 : (0 : ℝ) < Real.Gamma (a + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  have h2 : (0 : ℝ) < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have h3 : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h4 : (0 : ℝ) < (1 + (x / 1) ^ 2) ^ (-a - 1 / 2) :=
    Real.rpow_pos_of_pos (by positivity) _
  positivity

theorem lintegral_inverseGamma_brownian {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (inverseGammaDensity a u * brownianDensity u x))
      = ENNReal.ofReal (studentDensity a 1 x) := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun u => inverseGammaDensity a u * brownianDensity u x :=
    .of_forall fun u =>
      mul_nonneg (inverseGammaDensity_nonneg ha u) (brownianDensity_nonneg u x)
  have hmeas : AEStronglyMeasurable
      (fun u => inverseGammaDensity a u * brownianDensity u x)
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((measurable_inverseGammaDensity a).mul
      (measurable_brownianDensity_time x)).aestronglyMeasurable
  have heq := integral_eq_lintegral_of_nonneg_ae hnn hmeas
  rw [integral_inverseGamma_brownian ha x] at heq
  have hpos := studentDensity_pos ha x
  have hne : (∫⁻ u in Ioi (0 : ℝ),
      ENNReal.ofReal (inverseGammaDensity a u * brownianDensity u x)) ≠ ⊤ := by
    intro h
    rw [h] at heq
    simp at heq
    linarith
  rw [heq, ENNReal.ofReal_toReal hne]

/-- **The causal Bessel family maps to the Student-t family with `2a` degrees of freedom**: the
Brownian mixture over the inverse-gamma delay law of shape `a` is the Student-t law at scale `1`.
-/
theorem bridge_families_bessel (a : ℝ) (ha : 0 < a) :
    (inverseGammaLaw a).bind brownianLaw = studentLaw a 1 := by
  refine Measure.ext fun s hs => ?_
  have hdens : Measurable fun u : ℝ => ENNReal.ofReal (inverseGammaDensity a u) :=
    (measurable_inverseGammaDensity a).ennreal_ofReal
  have hcoe : Measurable fun u : ℝ => brownianLaw u s :=
    Measure.measurable_coe hs |>.comp measurable_brownianLaw
  rw [Measure.bind_apply hs measurable_brownianLaw.aemeasurable, inverseGammaLaw,
    lintegral_withDensity_eq_lintegral_mul₀ hdens.aemeasurable hcoe.aemeasurable]
  have hind : ∀ u : ℝ,
      (fun u : ℝ => ENNReal.ofReal (inverseGammaDensity a u)) u * (fun u => brownianLaw u s) u
        = Set.indicator (Ioi (0 : ℝ))
            (fun u => ENNReal.ofReal (inverseGammaDensity a u) * brownianLaw u s) u := by
    intro u
    by_cases h : u ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h]
      show ENNReal.ofReal (inverseGammaDensity a u) * brownianLaw u s = 0
      rw [inverseGammaDensity, Set.indicator_of_notMem h]
      simp
  simp only [Pi.mul_apply] at *
  rw [lintegral_congr hind, lintegral_indicator measurableSet_Ioi]
  have hstep : (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (inverseGammaDensity a u) * brownianLaw u s)
      = ∫⁻ u in Ioi (0 : ℝ), ∫⁻ x in s,
          ENNReal.ofReal (inverseGammaDensity a u) * ENNReal.ofReal (brownianDensity u x) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    rw [brownianLaw_eq_withDensity hu0, withDensity_apply _ hs,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [hstep]
  have huncurry : Measurable (Function.uncurry fun u x : ℝ =>
      ENNReal.ofReal (inverseGammaDensity a u) * ENNReal.ofReal (brownianDensity u x)) := by
    refine Measurable.mul ?_ ?_
    · exact hdens.comp measurable_fst
    · exact measurable_brownianDensity_uncurry.ennreal_ofReal
  rw [lintegral_lintegral_swap huncurry.aemeasurable, studentLaw, withDensity_apply _ hs]
  refine setLIntegral_congr_fun hs fun x _ => ?_
  rw [← lintegral_inverseGamma_brownian ha x]
  refine setLIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [← ENNReal.ofReal_mul (inverseGammaDensity_nonneg ha u)]

/-! ## The Bessel–Laplace integral -/

/-- **The Bessel–Laplace integral, in `ℝ≥0∞` and down to the defining integral of `K_p`.**

`∫_0^∞ u^{p-1}e^{-A/u - Bu}\,du = 2c^pK_p(2s)` for `A, B > 0`, every real `p`, and
`c = \sqrt A/\sqrt B`, `s = \sqrt A\sqrt B` — here with the right-hand side left as the integral
that *defines* `besselK`, and with the constants written in the coordinates that keep fourth
roots out. -/
theorem lintegral_Ioi_rpow_exp_besselKernel {p A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (p - 1) * Real.exp (-(A / u + B * u))))
      = ENNReal.ofReal ((Real.sqrt A / Real.sqrt B) ^ p) * (2 * ∫⁻ v in Ioi (0 : ℝ),
          ENNReal.ofReal (Real.cosh (p * v)
            * Real.exp (-(2 * (Real.sqrt A * Real.sqrt B) * Real.cosh v)))) := by
  have hsA : (0 : ℝ) < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hsB : (0 : ℝ) < Real.sqrt B := Real.sqrt_pos.mpr hB
  set c : ℝ := Real.sqrt A / Real.sqrt B with hcdef
  set s : ℝ := Real.sqrt A * Real.sqrt B with hsdef
  have hc : (0 : ℝ) < c := by rw [hcdef]; positivity
  have hs : (0 : ℝ) < s := by rw [hsdef]; positivity
  have hcp : (0 : ℝ) < c ^ p := Real.rpow_pos_of_pos hc p
  have hAA : A / Real.sqrt A = Real.sqrt A := by
    rw [eq_comm, eq_div_iff hsA.ne']
    exact Real.mul_self_sqrt hA.le
  have hBB : B / Real.sqrt B = Real.sqrt B := by
    rw [eq_comm, eq_div_iff hsB.ne']
    exact Real.mul_self_sqrt hB.le
  have hAc : A / c = s := by
    rw [hcdef, hsdef, div_div_eq_mul_div,
      show A * Real.sqrt B / Real.sqrt A = (A / Real.sqrt A) * Real.sqrt B by ring, hAA]
  have hBc : B * c = s := by
    rw [hcdef, hsdef,
      show B * (Real.sqrt A / Real.sqrt B) = (B / Real.sqrt B) * Real.sqrt A by ring, hBB]
    ring
  have hpt : ∀ v : ℝ, ENNReal.ofReal (c * Real.exp v)
        * ENNReal.ofReal ((c * Real.exp v) ^ (p - 1)
            * Real.exp (-(A / (c * Real.exp v) + B * (c * Real.exp v))))
      = ENNReal.ofReal (Real.exp (p * v)
          * (c ^ p * Real.exp (-(2 * s * Real.cosh v)))) := by
    intro v
    have hev : (0 : ℝ) < Real.exp v := Real.exp_pos v
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.mul_rpow hc.le hev.le, exp_rpow]
    have harg : A / (c * Real.exp v) + B * (c * Real.exp v) = 2 * s * Real.cosh v := by
      rw [show A / (c * Real.exp v) = (A / c) * Real.exp (-v) by
            rw [Real.exp_neg]; field_simp,
        show B * (c * Real.exp v) = (B * c) * Real.exp v by ring, hAc, hBc, Real.cosh_eq]
      ring
    rw [harg]
    have hcpow : c * c ^ (p - 1) = c ^ p := by
      nth_rewrite 1 [← Real.rpow_one c]
      rw [← Real.rpow_add hc]
      norm_num
    calc c * Real.exp v * (c ^ (p - 1) * Real.exp (v * (p - 1))
            * Real.exp (-(2 * s * Real.cosh v)))
        = (c * c ^ (p - 1)) * (Real.exp v * Real.exp (v * (p - 1)))
            * Real.exp (-(2 * s * Real.cosh v)) := by ring
      _ = c ^ p * Real.exp (p * v) * Real.exp (-(2 * s * Real.cosh v)) := by
          rw [hcpow, ← Real.exp_add, show v + v * (p - 1) = p * v by ring]
      _ = Real.exp (p * v) * (c ^ p * Real.exp (-(2 * s * Real.cosh v))) := by ring
  rw [lintegral_Ioi_comp_exp hc, funext hpt,
    lintegral_exp_mul_of_even (G := fun v => c ^ p * Real.exp (-(2 * s * Real.cosh v)))
      (by fun_prop) (fun v => by positivity) (fun v => by rw [Real.cosh_neg])]
  have hconst : ∀ v : ℝ, ENNReal.ofReal (Real.cosh (p * v)
        * (c ^ p * Real.exp (-(2 * s * Real.cosh v))))
      = ENNReal.ofReal (c ^ p)
        * ENNReal.ofReal (Real.cosh (p * v) * Real.exp (-(2 * s * Real.cosh v))) := by
    intro v
    rw [← ENNReal.ofReal_mul hcp.le]
    congr 1
    ring
  simp only [hconst]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← mul_assoc,
    mul_comm (2 : ℝ≥0∞) (ENNReal.ofReal (c ^ p)), mul_assoc]

/-- **The cosh-integral is `K_p`**, once it is known to be finite.

`besselK` is a Bochner integral and returns junk when its integrand is not integrable, so the
identification is stated with finiteness as a hypothesis; every consumer gets it by comparison
with a convergent integral. -/
theorem lintegral_cosh_exp_eq_besselK (p : ℝ) {z : ℝ}
    (hfin : (∫⁻ v in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.cosh (p * v) * Real.exp (-(z * Real.cosh v)))) ≠ ⊤) :
    (∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (Real.cosh (p * v) * Real.exp (-(z * Real.cosh v))))
      = ENNReal.ofReal (besselK p z) := by
  have hb : besselK p z
      = (∫⁻ v in Ioi (0 : ℝ),
          ENNReal.ofReal (Real.cosh (p * v) * Real.exp (-(z * Real.cosh v)))).toReal := by
    rw [besselK]
    have hcongr : (∫ u in Ioi (0 : ℝ), Real.exp (-(z * Real.cosh u)) * Real.cosh (p * u))
        = ∫ u in Ioi (0 : ℝ), Real.cosh (p * u) * Real.exp (-(z * Real.cosh u)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      ring
    rw [hcongr]
    refine integral_eq_lintegral_of_nonneg_ae ?_ (by fun_prop)
    exact .of_forall fun u => by positivity
  rw [hb, ENNReal.ofReal_toReal hfin]

/-- `K_{-p} = K_p`: the defining integral is even in the order. -/
theorem besselK_neg (p z : ℝ) : besselK (-p) z = besselK p z := by
  rw [besselK, besselK]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [show -p * u = -(p * u) by ring, Real.cosh_neg]

theorem besselK_nonneg (p z : ℝ) : 0 ≤ besselK p z := by
  rw [besselK]
  refine setIntegral_nonneg measurableSet_Ioi fun u _ => ?_
  positivity

/-! ## The transform -/

/-- **The Laplace transform of the inverse-gamma law at `\sigma = \omega^2/2`.**

The delay law has Laplace transform `2^{1-a}\Gamma(a)^{-1}\sigma^{a/2}K_a(\sqrt{2\sigma})`, written
here at `\sigma = \omega^2/2`, where `\sqrt{2\sigma} = |\omega|`. -/
theorem lintegral_exp_neg_inverseGammaLaw {a ω : ℝ} (ha : 0 < a) (hω : ω ≠ 0) :
    (∫⁻ u, ENNReal.ofReal (Real.exp (-(ω ^ 2 / 2 * u))) ∂(inverseGammaLaw a))
      = ENNReal.ofReal (2 ^ (1 - a) / Real.Gamma a * |ω| ^ a * besselK a |ω|) := by
  have hΓ : (0 : ℝ) < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hK : (0 : ℝ) < 2 ^ a * Real.Gamma a := by positivity
  have habs : (0 : ℝ) < |ω| := abs_pos.mpr hω
  have hB : (0 : ℝ) < ω ^ 2 / 2 := by positivity
  have hprob := isProbabilityMeasure_inverseGammaLaw ha
  -- the substitution constants
  have hsqrtinv : (0 : ℝ) < Real.sqrt 2⁻¹ := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt (ω ^ 2 / 2) = |ω| * Real.sqrt 2⁻¹ := by
    rw [show ω ^ 2 / 2 = ω ^ 2 * 2⁻¹ by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq_eq_abs]
  have hc : Real.sqrt 2⁻¹ / Real.sqrt (ω ^ 2 / 2) = |ω|⁻¹ := by
    rw [hsq]
    field_simp
  have hs : 2 * (Real.sqrt 2⁻¹ * Real.sqrt (ω ^ 2 / 2)) = |ω| := by
    rw [hsq, show Real.sqrt 2⁻¹ * (|ω| * Real.sqrt 2⁻¹)
        = |ω| * (Real.sqrt 2⁻¹ * Real.sqrt 2⁻¹) by ring,
      Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2⁻¹)]
    ring
  have hcpow : (|ω|⁻¹ : ℝ) ^ (-a) = |ω| ^ a := by
    rw [Real.inv_rpow habs.le, Real.rpow_neg habs.le, inv_inv]
  -- the integral, rewritten against Lebesgue measure
  have hdens : Measurable fun u : ℝ => ENNReal.ofReal (inverseGammaDensity a u) :=
    (measurable_inverseGammaDensity a).ennreal_ofReal
  have hstep : (∫⁻ u, ENNReal.ofReal (Real.exp (-(ω ^ 2 / 2 * u))) ∂(inverseGammaLaw a))
      = ENNReal.ofReal (2 ^ a * Real.Gamma a)⁻¹
        * ∫⁻ u in Ioi (0 : ℝ),
            ENNReal.ofReal (u ^ (-a - 1) * Real.exp (-(2⁻¹ / u + ω ^ 2 / 2 * u))) := by
    rw [inverseGammaLaw, lintegral_withDensity_eq_lintegral_mul₀ hdens.aemeasurable (by fun_prop),
      inverseGammaDensity_eq_indicator]
    have hind : ∀ u : ℝ,
        (Set.indicator (Ioi (0 : ℝ))
          (fun u => ENNReal.ofReal (u ^ (-a - 1) * Real.exp (-(2 * u)⁻¹)
            * (2 ^ a * Real.Gamma a)⁻¹)) * fun u => ENNReal.ofReal
              (Real.exp (-(ω ^ 2 / 2 * u)))) u
        = Set.indicator (Ioi (0 : ℝ))
            (fun u => ENNReal.ofReal (2 ^ a * Real.Gamma a)⁻¹
              * ENNReal.ofReal (u ^ (-a - 1)
                  * Real.exp (-(2⁻¹ / u + ω ^ 2 / 2 * u)))) u := by
      intro u
      by_cases h : u ∈ Ioi (0 : ℝ)
      · have hu : (0 : ℝ) < u := h
        rw [Pi.mul_apply, Set.indicator_of_mem h, Set.indicator_of_mem h,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [show -(2⁻¹ / u + ω ^ 2 / 2 * u) = -(2 * u)⁻¹ + -(ω ^ 2 / 2 * u) by
          field_simp; ring, Real.exp_add]
        ring
      · rw [Pi.mul_apply, Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
    simp only [hind]
    rw [lintegral_indicator measurableSet_Ioi,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- the substituted form, and the comparison that makes it finite
  have hsub := lintegral_Ioi_rpow_exp_besselKernel (p := -a) (A := 2⁻¹) (B := ω ^ 2 / 2)
    (by norm_num) hB
  rw [hc, hs, hcpow] at hsub
  have hYle : (∫⁻ u in Ioi (0 : ℝ),
        ENNReal.ofReal (u ^ (-a - 1) * Real.exp (-(2⁻¹ / u + ω ^ 2 / 2 * u))))
      ≤ ENNReal.ofReal (2 ^ a * Real.Gamma a) := by
    rw [← lintegral_Ioi_inverseGammaKernel ha]
    refine setLIntegral_mono_ae (by fun_prop) (.of_forall fun u hu => ?_)
    have hu0 : (0 : ℝ) < u := hu
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine Real.exp_le_exp.mpr ?_
    have hhalf : ((2 : ℝ) * u)⁻¹ = 2⁻¹ / u := by field_simp
    rw [hhalf]
    have : (0 : ℝ) ≤ ω ^ 2 / 2 * u := by positivity
    linarith
  have hXne : (∫⁻ v in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.cosh (-a * v) * Real.exp (-(|ω| * Real.cosh v)))) ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top (by norm_num : (2 : ℝ≥0∞) ≠ 0),
      ENNReal.mul_top (by
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        positivity)] at hsub
    rw [hsub] at hYle
    exact absurd (top_le_iff.mp hYle) (by simp)
  rw [hstep, hsub, lintegral_cosh_exp_eq_besselK (-a) hXne, besselK_neg,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
    ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ |ω| ^ a),
    ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2 ^ a * Real.Gamma a)⁻¹)]
  congr 1
  rw [Real.rpow_sub (by norm_num), Real.rpow_one]
  field_simp

/-- **The transform of the Student-t law at canonical scale.** `\hat\phi_1(\omega) =
\frac{2^{1-a}}{\Gamma(a)}|\omega|^aK_a(|\omega|)` for `\omega \ne 0`.

At the origin the identity is false, `|0|^a` being `0` while the transform of a probability law
is `1`; hence the quantifier `ω ≠ 0`. The proof conditions on the delay
(`bridge_families_bessel`, `fourierCos_bind_brownianLaw`) and evaluates the Laplace transform of
the inverse-gamma law (`lintegral_exp_neg_inverseGammaLaw`); no Bessel asymptotic is used,
because `besselK` is *defined* by the integral that the substitution produces. -/
theorem student_transform {a : ℝ} (ha : 0 < a) :
    ∀ ω : ℝ, ω ≠ 0 → fourierCos (studentLaw a 1) ω
      = 2 ^ (1 - a) / Real.Gamma a * |ω| ^ a * besselK a |ω| := by
  intro ω hω
  have hprob := isProbabilityMeasure_inverseGammaLaw ha
  have hval : (0 : ℝ) ≤ 2 ^ (1 - a) / Real.Gamma a * |ω| ^ a * besselK a |ω| := by
    have hΓ : (0 : ℝ) < Real.Gamma a := Real.Gamma_pos_of_pos ha
    have := besselK_nonneg a |ω|
    positivity
  rw [← bridge_families_bessel a ha,
    fourierCos_bind_brownianLaw (inverseGammaLaw_Iio_zero a) ω]
  have hb : (∫ u, Real.exp (-(ω ^ 2 / 2 * u)) ∂(inverseGammaLaw a))
      = (∫⁻ u, ENNReal.ofReal (Real.exp (-(ω ^ 2 / 2 * u))) ∂(inverseGammaLaw a)).toReal := by
    refine integral_eq_lintegral_of_nonneg_ae (.of_forall fun u => (Real.exp_pos _).le)
      (by fun_prop)
  rw [hb, lintegral_exp_neg_inverseGammaLaw ha hω, ENNReal.toReal_ofReal hval]

end ScaleSpace
