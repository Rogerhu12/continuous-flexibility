module

public import ContinuousFlexibility.Statements.Radial
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Actual logarithmic coordinates for the second-mode Morse tail

A single signed logarithmic change of variables treats both orientations.
The transformed density has mass proportional to w r^6 dr and resistance
proportional to dr/(w r^8); the endpoint normalization cancels in products.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

/-- The signed physical logarithm; the sign has square one. -/
def morseSecondModeDensity (w : ℝ → ℝ) (R s x : ℝ) : ℝ :=
  w (exp (s * x)) * exp (s * x) ^ 7 / R ^ 8

theorem morseSecondModeDensity_continuous {w : ℝ → ℝ} (hw : Continuous w)
    (R s : ℝ) : Continuous (morseSecondModeDensity w R s) := by
  have he : Continuous (fun x : ℝ => exp (s * x)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  exact ((hw.comp he).mul (he.pow 7)).div_const _

theorem morseSecondModeDensity_log {w : ℝ → ℝ} {R s r : ℝ}
    (hs : s ^ 2 = 1) (hr : 0 < r) :
    morseSecondModeDensity w R s (s * log r) = w r * r ^ 7 / R ^ 8 := by
  have he : s * (s * log r) = log r := by
    calc
      _ = s ^ 2 * log r := by ring
      _ = _ := by rw [hs, one_mul]
  simp only [morseSecondModeDensity, he, exp_log hr]

/-- Signed substitution for the physical mass density. The source interval
may be oriented in either direction. -/
theorem morseSecondMode_signed_mass {w : ℝ → ℝ} {R s a b : ℝ}
    (hw : Continuous w) (hR : R ≠ 0) (hs : s ^ 2 = 1)
    (ha : 0 < a) (hb : 0 < b) :
    (∫ x in s * log a..s * log b, morseSecondModeDensity w R s x) =
      s / R ^ 8 * (∫ r in a..b, w r * r ^ 6) := by
  have hpos (r : ℝ) (hr : r ∈ uIcc a b) : 0 < r :=
    (lt_min ha hb).trans_le hr.1
  have hd : ∀ r ∈ uIcc a b, HasDerivAt (fun t : ℝ => s * log t) (s / r) r := by
    intro r hr
    simpa only [div_eq_mul_inv] using (Real.hasDerivAt_log (hpos r hr).ne').const_mul s
  have hv : ContinuousOn (fun r : ℝ => s / r) (uIcc a b) :=
    continuousOn_const.div continuousOn_id (fun r hr => (hpos r hr).ne')
  have hp : ContinuousOn (morseSecondModeDensity w R s)
      ((fun r : ℝ => s * log r) '' uIcc a b) :=
    (morseSecondModeDensity_continuous hw R s).continuousOn
  calc
    _ = ∫ r in a..b, morseSecondModeDensity w R s (s * log r) * (s / r) :=
      (intervalIntegral.integral_comp_mul_deriv' hd hv hp).symm
    _ = ∫ r in a..b, (s / R ^ 8) * (w r * r ^ 6) := by
      apply intervalIntegral.integral_congr
      intro r hr
      dsimp only
      rw [morseSecondModeDensity_log hs (hpos r hr)]
      field_simp [hR, (hpos r hr).ne']
      <;> ring
    _ = _ := by rw [intervalIntegral.integral_const_mul]

/-- Signed substitution for the physical resistance density. -/
theorem morseSecondMode_signed_resistance {w : ℝ → ℝ} {R s a b : ℝ}
    (hw : Continuous w) (hR : R ≠ 0) (hs : s ^ 2 = 1)
    (ha : 0 < a) (hb : 0 < b)
    (hw₀ : ∀ r ∈ uIcc a b, w r ≠ 0) :
    (∫ x in s * log a..s * log b, (morseSecondModeDensity w R s x)⁻¹) =
      (s * R ^ 8) * (∫ r in a..b, (w r * r ^ 8)⁻¹) := by
  have hpos (r : ℝ) (hr : r ∈ uIcc a b) : 0 < r :=
    (lt_min ha hb).trans_le hr.1
  have hd : ∀ r ∈ uIcc a b, HasDerivAt (fun t : ℝ => s * log t) (s / r) r := by
    intro r hr
    simpa only [div_eq_mul_inv] using (Real.hasDerivAt_log (hpos r hr).ne').const_mul s
  have hv : ContinuousOn (fun r : ℝ => s / r) (uIcc a b) :=
    continuousOn_const.div continuousOn_id (fun r hr => (hpos r hr).ne')
  have hp₀ : ∀ x ∈ (fun r : ℝ => s * log r) '' uIcc a b,
      morseSecondModeDensity w R s x ≠ 0 := by
    rintro x ⟨r, hr, rfl⟩
    rw [morseSecondModeDensity_log hs (hpos r hr)]
    exact div_ne_zero (mul_ne_zero (hw₀ r hr) (pow_ne_zero 7 (hpos r hr).ne'))
      (pow_ne_zero 8 hR)
  have hp : ContinuousOn (fun x => (morseSecondModeDensity w R s x)⁻¹)
      ((fun r : ℝ => s * log r) '' uIcc a b) :=
    (morseSecondModeDensity_continuous hw R s).continuousOn.inv₀ hp₀
  calc
    _ = ∫ r in a..b, (morseSecondModeDensity w R s (s * log r))⁻¹ * (s / r) :=
      (intervalIntegral.integral_comp_mul_deriv' hd hv hp).symm
    _ = ∫ r in a..b, (s * R ^ 8) * (w r * r ^ 8)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro r hr
      dsimp only
      rw [morseSecondModeDensity_log hs (hpos r hr)]
      field_simp [hR, hw₀ r hr, (hpos r hr).ne']
      <;> ring
    _ = _ := by rw [intervalIntegral.integral_const_mul]

/-- Both endpoint orientations have the same positive physical mass. -/
theorem morseSecondMode_outward_mass {w : ℝ → ℝ} {R a b : ℝ}
    (right : Bool) (hw : Continuous w) (hR : R ≠ 0)
    (ha : 0 < a) (hb : 0 < b) :
    (∫ x in (if right then log a else -log b)..(if right then log b else -log a),
      morseSecondModeDensity w R (if right then 1 else -1) x) =
      (R ^ 8)⁻¹ * (∫ r in a..b, w r * r ^ 6) := by
  cases right
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have h := morseSecondMode_signed_mass (s := (-1 : ℝ)) hw hR (by norm_num) ha hb
    simp only [neg_one_mul] at h
    rw [intervalIntegral.integral_symm, h]
    ring
  · simp only [↓reduceIte]
    simpa only [one_mul, one_div] using
      morseSecondMode_signed_mass (s := (1 : ℝ)) hw hR (by norm_num) ha hb

/-- Both endpoint orientations have the same positive physical resistance. -/
theorem morseSecondMode_outward_resistance {w : ℝ → ℝ} {R a b : ℝ}
    (right : Bool) (hw : Continuous w) (hR : R ≠ 0)
    (ha : 0 < a) (hb : 0 < b)
    (hw₀ : ∀ r ∈ uIcc a b, w r ≠ 0) :
    (∫ x in (if right then log a else -log b)..(if right then log b else -log a),
      (morseSecondModeDensity w R (if right then 1 else -1) x)⁻¹) =
      R ^ 8 * (∫ r in a..b, (w r * r ^ 8)⁻¹) := by
  cases right
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have h := morseSecondMode_signed_resistance (s := (-1 : ℝ))
      hw hR (by norm_num) ha hb hw₀
    simp only [neg_one_mul] at h
    rw [intervalIntegral.integral_symm, h]
    ring
  · simp only [↓reduceIte]
    simpa only [one_mul] using
      morseSecondMode_signed_resistance (s := (1 : ℝ)) hw hR (by norm_num) ha hb hw₀

/-- The inward endpoint of the mass interval in increasing physical radius. -/
def morseSecondModeMassLeft (T : MorseChainData) (right : Bool) (n : ℕ) : ℝ :=
  T.radius right n (T.leftX right n)

/-- Actual outward tail data. On the left the initial resistance interval
is the full original interval J_N, and the n-th following edge is J_(N+n+1).
The geometry hypotheses will be proved after discarding finitely many cells. -/
def morseSecondModeTail (D : ReferenceData) (T : MorseChainData) (N : ℕ)
    (right : Bool) : DeepTailData where
  entrance := if right then log (morseSecondModeMassLeft T right N)
    else -log (morseSecondModeMassLeft T right (N - 1))
  endpoint := if right then log D.b else -log D.a
  p := morseSecondModeDensity D.w (if right then D.b else D.a)
    (if right then 1 else -1)
  node := fun n => if right then log (morseSecondModeMassLeft T right (N + n))
    else -log (morseChainMassEnd T right (N + n))
  massEnd := fun n => if right then log (morseChainMassEnd T right (N + n))
    else -log (morseSecondModeMassLeft T right (N + n))
  Λ := 12
  η := 1 / 16
  K := 32

end ContinuousFlexibility.Radial
