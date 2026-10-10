/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import ScaleSpaceCore.BochnerConvolutionSpace

/-!
# The Fourier pairing on `L¹(E)`: `(μ * f)^ = μ̂ f̂`

Home: none (standard analysis in Mathlib's types: the `d`-dimensional counterpart of
`ScaleSpaceCore.BochnerConvolution`'s character pairing, with no programme vocabulary; ref:
@larsen1971introduction, p. 2)

Q-0332 (SSL-5, stretch), the `d`-dimensional counterpart of `charCLM`/`charCLM_transL1`/
`charCLM_mconvL1` of `ScaleSpaceCore.BochnerConvolution`, over a finite-dimensional real inner
product space `E` with an additive Haar measure as its `volume`. The pairing is
`f̂(ω) = ∫ e^{i⟨x, ω⟩} f(x) dx`, Mathlib's `charFun` convention (`charFun μ ω = ∫ e^{i⟨x, ω⟩} dμ`),
which is how Paper VII's blueprint writes it. `charCLME_mconvL1E` is the identity
`(μ * f)^(ω) = μ̂(ω) f̂(ω)`; it is proved, as on the line, by pairing the bounded functional
`charCLME ω` through the Bochner form `μ * f = ∫ T_y f dμ(y)` (`apply_mconvL1E_general`).

What is not here: a test function with a zero-free transform and the injectivity of
`μ ↦ mconvL1E μ` that follows (the line's `gaussL1`, `mconvL1_injective`). Paper VII reads them
with its own Gaussian density.

## References

* @larsen1971introduction, p. 2 (F.5, F.6): the Fourier and Fourier–Stieltjes transforms on a
  locally compact Abelian group are homomorphisms, `(f * g)^ = f̂ ĝ` and `(μ * ν)^ = μ̂ ν̂` — the
  convolution theorem `charCLME_mconvL1E` restates with `charFun`'s sign and `E` in place of `G`.
-/

namespace ScaleSpace

open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] in
/-- The integrand of the character pairing is integrable: a unit-modulus continuous factor times
an `L¹` function. -/
theorem integrable_char_mulE (ω : E) (f : E →₁[volume] ℝ) :
    Integrable (fun x : E => Complex.exp (⟪x, ω⟫ * Complex.I) * ((f : E → ℝ) x : ℂ)) := by
  refine Integrable.bdd_mul (c := 1) (L1.integrable_coeFn f).ofReal ?_ ?_
  · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards with x
    rw [Complex.norm_exp]
    simp

omit [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] in
/-- **The character pairing** `f ↦ f̂(ω) = ∫ e^{i⟨x, ω⟩} f(x) dx`, as an `ℝ`-linear bounded
functional on `L¹(E)` with values in `ℂ`. -/
noncomputable def charCLME (ω : E) : (E →₁[volume] ℝ) →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x : E, Complex.exp (⟪x, ω⟫ * Complex.I) * ((f : E → ℝ) x : ℂ)
      map_add' := fun f g => by
        rw [← integral_add (integrable_char_mulE ω f) (integrable_char_mulE ω g)]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add f g] with x hx
        rw [hx]
        push_cast [Pi.add_apply]
        ring
      map_smul' := fun c f => by
        simp only [RingHom.id_apply]
        rw [← integral_smul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c f] with x hx
        rw [hx]
        simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.real_smul]
        ring }
    1 fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      calc ‖∫ x : E, Complex.exp (⟪x, ω⟫ * Complex.I) * ((f : E → ℝ) x : ℂ)‖
          ≤ ∫ x : E, ‖Complex.exp (⟪x, ω⟫ * Complex.I) * ((f : E → ℝ) x : ℂ)‖ :=
            norm_integral_le_integral_norm _
        _ = ‖f‖ := by
            rw [Lp.norm_def, eLpNorm_one_eq_lintegral_enorm,
              ← integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f)]
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            simp [Complex.norm_exp]

omit [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] in
lemma charCLME_apply (ω : E) (f : E →₁[volume] ℝ) :
    charCLME ω f = ∫ x : E, Complex.exp (⟪x, ω⟫ * Complex.I) * ((f : E → ℝ) x : ℂ) := rfl

omit [FiniteDimensional ℝ E] in
/-- **The character pairing turns translation into multiplication** by `e^{i⟨a, ω⟩}`. -/
theorem charCLME_transL1E (ω a : E) (f : E →₁[volume] ℝ) :
    charCLME ω (transL1E a f) = Complex.exp (⟪a, ω⟫ * Complex.I) * charCLME ω f := by
  rw [charCLME_apply, charCLME_apply]
  have hrepr : ∫ x : E, Complex.exp (⟪x, ω⟫ * Complex.I) * ((transL1E a f : E →₁[volume] ℝ) x : ℂ)
      = ∫ x : E, Complex.exp (⟪x, ω⟫ * Complex.I) * ((f : E → ℝ) (x - a) : ℂ) := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_transL1E a f] with x hx
    rw [hx]
  rw [hrepr, ← integral_add_right_eq_self
    (fun x : E => Complex.exp (⟪x, ω⟫ * Complex.I) * ((f : E → ℝ) (x - a) : ℂ)) a,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [add_sub_cancel_right, inner_add_left]
  rw [← mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf

/-- **`(μ * f)^ = μ̂ f̂`**: pairing the convolution operator against a character factorises into
the characteristic function of the measure times the transform of the function. -/
theorem charCLME_mconvL1E (μ : Measure E) [IsFiniteMeasure μ] (ω : E) (f : E →₁[volume] ℝ) :
    charCLME ω (mconvL1E μ f) = charFun μ ω * charCLME ω f := by
  rw [apply_mconvL1E_general (charCLME ω) μ f]
  simp only [charCLME_transL1E]
  rw [integral_mul_const, charFun_apply]

end ScaleSpace
