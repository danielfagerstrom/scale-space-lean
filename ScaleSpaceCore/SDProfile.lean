/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# The admissible cone on the line: `SDProfile`

The data of a symmetric self-decomposable law on the line, in the form the spatial articles
quantify over: a Gaussian coefficient `a ≥ 0` and a nonincreasing folded profile `k ≥ 0` on
`(0,∞)`, with exponent

`F(ω) = aω² + ∫₀^∞ (1 - cos ωx)\,k(x)\,dx/x`.

This is the line's analogue of `CausalAdmissible` (`CausalCone`), and the field layout is parallel
to it: `b₀ ↦ a`, then `k`, its sign, monotonicity and normalisation, and the two integrability
windows. `bridge_exponents` (`BridgeExponents`) is the map from the causal cone into this one.

Moved from the spatial article's export (`SpatialLine.Exponent`, `Growth`, `ProfileIntegrability`,
and `SDProfile.exponent_zero` from `SelfDecomposable`, at `cone-v0.1`) together with what it
needs: the folding predicate `IsFolded`, the symmetric Lévy pair `SymLevyPair` with its quadratic
growth bound, and the half of `lem:profile-integrability` that rests on Lean core
(`profile_integrability_pair`). The half that spends the article's ledger
(`profile_integrability_mem`) stayed behind, as did `IsSelfDecomposable`, `IsSymNegDef` and the
positive-definiteness vocabulary. Docstrings name the source article's blueprint labels.

## Two `ℝ≥0∞`-first definitions

`SymLevyPair.exponentL` and `SDProfile.exponentL` are `lintegral`s, so they need no
integrability side condition and the elementary facts about them are unconditional; the
real-valued versions are `.toReal` of those. Finiteness is not a field of either structure: it
is `lem:quadratic-growth`.
-/

namespace ScaleSpace

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## Folded measures -/

/-- A measure on `ℝ` is *folded* when it is carried by `(0,∞)`.

This is the blueprint's "measure on `(0,∞)`" — the folding convention of Chapter 2, under which
a symmetric Lévy measure on `ℝ ∖ {0}` is written as its image under `x ↦ |x|`. Carrying a
predicate keeps the ambient space `ℝ`, so that `Measure.conv` and the dilation pushforward stay
applicable, exactly as `Hemigroup.IsCausal` does on the half-line.

twin: `Hemigroup.IsCausal`, with `Iio 0` replaced by `Iic 0` — the origin carries no weight
here, because `1 - cos 0 = 0` and the blueprint's `ν` lives on the *open* half-line. -/
def IsFolded (m : Measure ℝ) : Prop := m (Iic 0) = 0

/-! ## `LEₛ`: the symmetric Lévy–Khintchine form (2.2) -/

/-- **The data of the symmetric Lévy–Khintchine representation `eq:levy-khintchine`**: a Gaussian
coefficient `a ≥ 0` and a folded Lévy measure `ν` on `(0,∞)` with `∫ (1 ∧ x²) ν(dx) < ∞`.

The blueprint's `ν` lives on `(0,∞)`; here it is a measure on `ℝ` carrying `IsFolded`, so that
dilation (pushforward along `x ↦ c x`) and the folding convention stay expressible in the
ambient space. `σ`-finiteness of `ν` on `(0,∞)` is a consequence of `ν_integrable`, not a
field. -/
structure SymLevyPair where
  /-- The Gaussian coefficient `a`. -/
  a : ℝ
  /-- The folded Lévy measure `ν`, carried by `(0,∞)`. -/
  ν : Measure ℝ
  a_nonneg : 0 ≤ a
  ν_folded : IsFolded ν
  ν_integrable : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν ≠ ⊤

namespace SymLevyPair

/-- **`eq:levy-khintchine`**, `ℝ≥0∞`-valued: `a ω² + ∫ (1 - cos ωx) ν(dx)`. -/
noncomputable def exponentL (P : SymLevyPair) (ω : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (P.a * ω ^ 2) + ∫⁻ x, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂P.ν

/-- The real-valued exponent. Equal to `exponentL` under `lem:quadratic-growth`, which is the
only regime this article uses. -/
noncomputable def exponent (P : SymLevyPair) (ω : ℝ) : ℝ := (P.exponentL ω).toReal

end SymLevyPair

/-! ## The profile form (2.5) -/

/-- The Lévy measure of a profile: density `k(x)/x` against Lebesgue measure on `(0,∞)`.

twin: `Hemigroup.levyMeasureOfDensity`, verbatim. -/
noncomputable def profileMeasure (k : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity fun x => ENNReal.ofReal (k x / x)

/-- **The data of `eq:sd-profile`**: a Gaussian coefficient `a ≥ 0` and a nonincreasing profile
`k ≥ 0` on `(0,∞)` satisfying the two integrability conditions of `lem:profile-integrability`.

The pair `(a, k)` is what `thm:main-characterization` says the axioms leave free: a jitter
variance and a nonincreasing displacement profile.

twin: `Hemigroup.SelfDecomposableExponent`, field for field — see the module docstring for the
one deliberate divergence in the last field. -/
structure SDProfile where
  /-- The Gaussian coefficient `a`; the slot the causal drift `b₀` occupies. -/
  a : ℝ
  /-- The folded profile `k`, a density against `dx/x` on `(0,∞)`. -/
  k : ℝ → ℝ
  a_nonneg : 0 ≤ a
  k_nonneg : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ k x
  k_antitone : AntitoneOn k (Ioi (0 : ℝ))
  /-- A normalisation, not a constraint (Paper I's `k_zero`): every other field leaves `k 0`
  free, and fixing it to `0` makes the lower endpoint `s = 0` a special case of the general
  formula rather than a separate definition. -/
  k_zero : k 0 = 0
  /-- `∫₀¹ x k(x) dx < ∞`, the first half of `lem:profile-integrability`. -/
  integrable_near_zero : ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x * k x) ≠ ⊤
  /-- `∫₁^∞ k(x)/x dx < ∞`, the second half. -/
  integrable_at_top : ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (k x / x) ≠ ⊤

namespace SDProfile

/-- **`eq:sd-profile`**, `ℝ≥0∞`-valued: `a ω² + ∫₀^∞ (1 - cos ωx) k(x) dx/x`. -/
noncomputable def exponentL (P : SDProfile) (ω : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (P.a * ω ^ 2)
    + ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.cos (ω * x)) * P.k x / x)

/-- The real-valued exponent of `eq:sd-profile`. -/
noncomputable def exponent (P : SDProfile) (ω : ℝ) : ℝ := (P.exponentL ω).toReal

/-- The Lévy measure attached to the profile. -/
noncomputable def levyMeasure (P : SDProfile) : Measure ℝ := profileMeasure P.k

end SDProfile

/-- **The admissible exponents** of `thm:main-characterization`: the functions of the form
`eq:sd-profile`.

This is the class the main theorem's `F` ranges over, the cone of `lem:admissible-cone`, and
the hypothesis of `prop:strict-positivity`. -/
def IsAdmissibleExponent (F : ℝ → ℝ) : Prop := ∃ P : SDProfile, ∀ ω, F ω = P.exponent ω

/-! ## `lem:quadratic-growth` -/

namespace SymLevyPair

/-! ### The two pieces of the constant are finite -/

/-- The near-origin half of the constant of `lem:quadratic-growth` is finite: on `(0,1]` the
integrand `x²/2` is dominated by `1 ∧ x²`, whose integral is a field of the structure. -/
theorem lintegral_sq_div_two_ne_top (P : SymLevyPair) :
    (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ 2 / 2) ∂P.ν) ≠ ⊤ := by
  refine ne_top_of_le_ne_top P.ν_integrable ?_
  calc (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ 2 / 2) ∂P.ν)
      ≤ ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (min 1 (x ^ 2)) ∂P.ν := by
        refine setLIntegral_mono' measurableSet_Ioc fun x hx => ENNReal.ofReal_le_ofReal ?_
        have hx1 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
        rw [min_eq_right hx1]
        nlinarith [sq_nonneg x]
    _ ≤ ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂P.ν := setLIntegral_le_lintegral _ _

/-- The far half of the constant is finite: on `(1,∞)` the constant `1` is exactly `1 ∧ x²`. -/
theorem measure_Ioi_one_ne_top (P : SymLevyPair) : P.ν (Ioi (1 : ℝ)) ≠ ⊤ := by
  refine ne_top_of_le_ne_top P.ν_integrable ?_
  calc P.ν (Ioi (1 : ℝ))
      = ∫⁻ _ in Ioi (1 : ℝ), 1 ∂P.ν := by
        rw [lintegral_one, Measure.restrict_apply_univ]
    _ ≤ ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (min 1 (x ^ 2)) ∂P.ν := by
        refine setLIntegral_mono' measurableSet_Ioi fun x hx => ?_
        have hx' : (1 : ℝ) < x := hx
        have hx1 : (1 : ℝ) ≤ x ^ 2 := by nlinarith [hx']
        rw [min_eq_left hx1, ENNReal.ofReal_one]
    _ ≤ ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂P.ν := setLIntegral_le_lintegral _ _

/-! ### The bound -/

/-- **`lem:quadratic-growth`.** The constant
`C = a + ½∫_{(0,1]} x² ν + 2 ν((1,∞))` is finite, and `ψ(ω) ≤ C(1 + ω²)` for every `ω`.

The proof is the truncation split of `eq:levy-khintchine` at `x = 1`: below it
`1 - cos ωx ≤ ω²x²/2`, above it `1 - cos ωx ≤ 2`. -/
theorem quadratic_growth (P : SymLevyPair) :
    (ENNReal.ofReal P.a + (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ 2 / 2) ∂P.ν)
        + 2 * P.ν (Ioi 1)) ≠ ⊤ ∧
      ∀ ω : ℝ, P.exponentL ω
        ≤ (ENNReal.ofReal P.a + (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ 2 / 2) ∂P.ν)
            + 2 * P.ν (Ioi 1)) * ENNReal.ofReal (1 + ω ^ 2) := by
  set I : ℝ≥0∞ := ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ 2 / 2) ∂P.ν with hI
  set J : ℝ≥0∞ := P.ν (Ioi 1) with hJ
  have hIne : I ≠ ⊤ := P.lintegral_sq_div_two_ne_top
  have hJne : J ≠ ⊤ := P.measure_Ioi_one_ne_top
  refine ⟨by finiteness, fun ω => ?_⟩
  -- The Lévy measure is carried by `(0,∞)`, which splits as `(0,1] ∪ (1,∞)`.
  have hres : P.ν.restrict (Ioi (0 : ℝ)) = P.ν := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    have hc : P.ν {a : ℝ | a ≤ 0} = 0 := P.ν_folded
    rw [ae_iff]
    simpa using hc
  have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := Ioc_disjoint_Ioi le_rfl
  have hint : (∫⁻ x, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂P.ν)
      = (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂P.ν)
        + ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (1 - Real.cos (ω * x)) ∂P.ν := by
    conv_lhs => rw [← hres]
    rw [hsplit, lintegral_union measurableSet_Ioi hdisj]
  -- Below the truncation: `1 - cos ωx ≤ ω²·(x²/2)`.
  have hnear : (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂P.ν)
      ≤ ENNReal.ofReal (ω ^ 2) * I := by
    rw [hI, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioc fun x _ => ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hcos := Real.one_sub_sq_div_two_le_cos (x := ω * x)
    nlinarith [hcos]
  -- Above it: `1 - cos ωx ≤ 2`.
  have hfar : (∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (1 - Real.cos (ω * x)) ∂P.ν) ≤ 2 * J := by
    calc (∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (1 - Real.cos (ω * x)) ∂P.ν)
        ≤ ∫⁻ _ in Ioi (1 : ℝ), (2 : ℝ≥0∞) ∂P.ν := by
          refine setLIntegral_mono' measurableSet_Ioi fun x _ => ?_
          have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by
            rw [ENNReal.ofReal_ofNat]
          rw [h2]
          exact ENNReal.ofReal_le_ofReal (by linarith [Real.neg_one_le_cos (ω * x)])
      _ = 2 * J := by rw [setLIntegral_const, hJ]
  -- Assemble, comparing each term with its share of `C (1 + ω²)`.
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + ω ^ 2) :=
    ENNReal.one_le_ofReal.mpr (by nlinarith [sq_nonneg ω])
  have hsq : ENNReal.ofReal (ω ^ 2) ≤ ENNReal.ofReal (1 + ω ^ 2) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hgauss : ENNReal.ofReal (P.a * ω ^ 2) ≤ ENNReal.ofReal P.a * ENNReal.ofReal (1 + ω ^ 2) := by
    rw [ENNReal.ofReal_mul P.a_nonneg]
    gcongr
  calc P.exponentL ω
      = ENNReal.ofReal (P.a * ω ^ 2) + ∫⁻ x, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂P.ν := rfl
    _ ≤ ENNReal.ofReal P.a * ENNReal.ofReal (1 + ω ^ 2)
        + (ENNReal.ofReal (ω ^ 2) * I + 2 * J) := by
        rw [hint]; exact add_le_add hgauss (add_le_add hnear hfar)
    _ ≤ ENNReal.ofReal P.a * ENNReal.ofReal (1 + ω ^ 2)
        + (I * ENNReal.ofReal (1 + ω ^ 2) + 2 * J * ENNReal.ofReal (1 + ω ^ 2)) := by
        refine add_le_add le_rfl (add_le_add ?_ ?_)
        · rw [mul_comm]
          gcongr
        · calc 2 * J = 2 * J * 1 := (mul_one _).symm
            _ ≤ 2 * J * ENNReal.ofReal (1 + ω ^ 2) := by gcongr
    _ = (ENNReal.ofReal P.a + I + 2 * J) * ENNReal.ofReal (1 + ω ^ 2) := by
        rw [add_mul, add_mul, add_assoc]

/-- **`lem:quadratic-growth`, the corollary that makes `exponent` faithful.** The exponent of a
pair is finite at every frequency, so `SymLevyPair.exponent`, a `.toReal`, is the real number
`eq:levy-khintchine` writes.

Helper, named by no node. -/
theorem exponentL_ne_top (P : SymLevyPair) (ω : ℝ) : P.exponentL ω ≠ ⊤ := by
  obtain ⟨hC, hbound⟩ := P.quadratic_growth
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) (hbound ω)

end SymLevyPair

/-! ## `lem:profile-integrability` -/

/-- **`lem:profile-integrability`.** The Lévy condition `∫ (1 ∧ x²) ν < ∞` on the profile measure
`ν(dx) = k(x) x⁻¹ dx` is the conjunction of the two conditions of `eq:sd-profile`. -/
theorem profile_integrability {k : ℝ → ℝ} (hk : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ k x)
    (hkm : AEMeasurable k (volume.restrict (Ioi (0 : ℝ)))) :
    (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(profileMeasure k)) ≠ ⊤
      ↔ ((∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x * k x)) ≠ ⊤
          ∧ (∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (k x / x)) ≠ ⊤) := by
  have hdens : AEMeasurable (fun x : ℝ => ENNReal.ofReal (k x / x))
      (volume.restrict (Ioi (0 : ℝ))) := (hkm.div aemeasurable_id).ennreal_ofReal
  have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := Ioc_disjoint_Ioi le_rfl
  have hkey : (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(profileMeasure k))
      = (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x * k x))
        + ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (k x / x) := by
    rw [profileMeasure, lintegral_withDensity_eq_lintegral_mul₀ hdens (by fun_prop),
      hsplit, lintegral_union measurableSet_Ioi hdisj]
    congr 1
    · -- Below the truncation `1 ∧ x² = x²`, and `(k(x)/x)·x² = x·k(x)`.
      rw [setLIntegral_congr (μ := volume) (f := fun x => ENNReal.ofReal (x * k x))
        Ioo_ae_eq_Ioc]
      refine setLIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
      have hx0 : (0 : ℝ) < x := hx.1
      have hx1 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
      have hkx : 0 ≤ k x := hk x hx0
      simp only [Pi.mul_apply, min_eq_right hx1]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    · -- Above it `1 ∧ x² = 1`.
      refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hx' : (1 : ℝ) < x := hx
      have hx1 : (1 : ℝ) ≤ x ^ 2 := by nlinarith [hx']
      rw [Pi.mul_apply, min_eq_left hx1, ENNReal.ofReal_one, mul_one]
  rw [hkey, ENNReal.add_ne_top]

/-- The profile measure of an `SDProfile` is carried by `(0,∞)`. -/
theorem isFolded_profileMeasure (k : ℝ → ℝ) : IsFolded (profileMeasure k) := by
  refine (withDensity_absolutelyContinuous _ _) ?_
  rw [Measure.restrict_apply measurableSet_Iic]
  convert measure_empty (μ := (volume : Measure ℝ))
  ext x
  simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false, not_and, not_lt]
  exact fun h => h

/-- A symmetric Lévy pair carrying a profile's data has the profile's exponent. The two are the
same `lintegral` once `withDensity` is unfolded: `(k(x)/x)·(1 - cos ωx)` is the integrand of
`eq:sd-profile`. -/
theorem exponentL_eq_of_profileMeasure (P : SDProfile) (Q : SymLevyPair) (ha : Q.a = P.a)
    (hν : Q.ν = profileMeasure P.k) (ω : ℝ) : P.exponentL ω = Q.exponentL ω := by
  have hkm : AEMeasurable P.k (volume.restrict (Ioi (0 : ℝ))) :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioi P.k_antitone
  have hdens : AEMeasurable (fun x : ℝ => ENNReal.ofReal (P.k x / x))
      (volume.restrict (Ioi (0 : ℝ))) := (hkm.div aemeasurable_id).ennreal_ofReal
  rw [SDProfile.exponentL, SymLevyPair.exponentL, ha, hν, profileMeasure,
    lintegral_withDensity_eq_lintegral_mul₀ hdens (by fun_prop)]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  have hkx : 0 ≤ P.k x := P.k_nonneg x hx
  have hcos : 0 ≤ 1 - Real.cos (ω * x) := by linarith [Real.cos_le_one (ω * x)]
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- **`lem:profile-integrability`, the pair.** The data of `eq:sd-profile` is a symmetric Lévy
pair with the same Gaussian coefficient and the same exponent.

This is the half of the node's "consequently" clause that rests on Lean core alone: the Lévy
condition is `profile_integrability` read right to left from the structure's two integrability
fields. -/
theorem profile_integrability_pair (P : SDProfile) :
    ∃ Q : SymLevyPair, Q.a = P.a ∧ Q.ν = profileMeasure P.k ∧ ∀ ω, P.exponent ω = Q.exponent ω := by
  have hkm : AEMeasurable P.k (volume.restrict (Ioi (0 : ℝ))) :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioi P.k_antitone
  have hint : (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(profileMeasure P.k)) ≠ ⊤ :=
    (profile_integrability P.k_nonneg hkm).mpr ⟨P.integrable_near_zero, P.integrable_at_top⟩
  set Q : SymLevyPair :=
    ⟨P.a, profileMeasure P.k, P.a_nonneg, isFolded_profileMeasure P.k, hint⟩ with hQ
  have hQa : Q.a = P.a := rfl
  have hQν : Q.ν = profileMeasure P.k := rfl
  refine ⟨Q, hQa, hQν, fun ω => ?_⟩
  rw [SDProfile.exponent, SymLevyPair.exponent,
    exponentL_eq_of_profileMeasure P Q hQa hQν ω]

/-- A profile exponent vanishes at the origin. -/
@[simp] theorem SDProfile.exponent_zero (Q : SDProfile) : Q.exponent 0 = 0 := by
  have h : Q.exponentL 0 = 0 := by
    rw [SDProfile.exponentL]
    simp
  rw [SDProfile.exponent, h, ENNReal.toReal_zero]

end ScaleSpace
