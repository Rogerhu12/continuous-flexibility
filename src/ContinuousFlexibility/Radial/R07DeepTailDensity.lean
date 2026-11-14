module

public import ContinuousFlexibility.Radial.R07DeepTailBridge

/-!
# Comparing the physical deep-tail densities at different frequencies

The mass and resistance bounds in `R05` are stated in the frequency-two
gauge.  The physical density required by `R06` at frequency `j` is different.
The lemmas below keep the normalization at the endpoint explicit and prove
the exact density ratio and its bounds from a logarithmic radius estimate.
Thus a bound for `j^2 * |log (r / r_endpoint)|` is a concrete analytic input,
rather than being silently inferred from the frequency-two estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- The normalized density appearing literally in `TailPhysicalRelation`. -/
def r07PhysicalDensity (D : ReferenceData) (right : Bool) (j : ℕ) (x : ℝ) : ℝ :=
  (tailPhysicalRadius right x / (if right then D.b else D.a)) ^
    (2 * (j : ℝ) ^ 2) * D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x

theorem r07_contDiff_radius (right : Bool) :
    ContDiff ℝ ∞ (tailPhysicalRadius right) := by
  cases right
  · exact contDiff_exp.comp contDiff_id.neg
  · exact contDiff_exp

theorem r07_contDiff_physicalDensity {D : ReferenceData} (right : Bool) (j : ℕ)
    (he : 0 < (if right then D.b else D.a)) (hw : ContDiff ℝ ∞ D.w) :
    ContDiff ℝ ∞ (r07PhysicalDensity D right j) := by
  have hr := r07_contDiff_radius right
  have hg : ContDiff ℝ ∞ (fun x : ℝ =>
      (tailPhysicalRadius right x / (if right then D.b else D.a)) ^ (2 * (j : ℝ) ^ 2)) :=
    (hr.div_const _).rpow_const_of_ne
      (fun x => (div_pos (r07_radius_pos right x) he).ne')
  exact (hg.mul (hw.comp hr)).div hr (fun x => (r07_radius_pos right x).ne')

theorem r07_physicalDensity_pos {D : ReferenceData} {right : Bool} {j : ℕ} {x : ℝ}
    (he : 0 < (if right then D.b else D.a)) (hw : 0 < D.w (tailPhysicalRadius right x)) :
    0 < r07PhysicalDensity D right j x :=
  div_pos (mul_pos (rpow_pos_of_pos (div_pos (r07_radius_pos right x) he) _) hw)
    (r07_radius_pos right x)

/-- All frequency dependence beyond the frequency-two density is carried by
one positive radial power. -/
theorem r07_physicalDensity_factor {D : ReferenceData} (right : Bool) (j : ℕ) (x : ℝ)
    (he : 0 < (if right then D.b else D.a)) :
    r07PhysicalDensity D right j x =
      (tailPhysicalRadius right x / (if right then D.b else D.a)) ^
        (2 * (j : ℝ) ^ 2 - 8) * r07PhysicalDensity D right 2 x := by
  let q : ℝ := tailPhysicalRadius right x / (if right then D.b else D.a)
  have hq : 0 < q := div_pos (r07_radius_pos right x) he
  have hp : q ^ (2 * (j : ℝ) ^ 2) = q ^ (2 * (j : ℝ) ^ 2 - 8) * q ^ (8 : ℝ) := by
    rw [← rpow_add hq]
    congr 1
    ring
  change q ^ (2 * (j : ℝ) ^ 2) * D.w (tailPhysicalRadius right x) /
      tailPhysicalRadius right x =
    q ^ (2 * (j : ℝ) ^ 2 - 8) *
      (q ^ (2 * (2 : ℝ) ^ 2) * D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x)
  norm_num only [show 2 * (2 : ℝ) ^ 2 = 8 by norm_num]
  rw [hp]
  ring

/-- A logarithmic radius bound controls every nonnegative real power. -/
theorem r07_rpow_bounds_of_log {q p L : ℝ} (hq : 0 < q) (hp : 0 ≤ p)
    (hlog : |log q| ≤ L) :
    exp (-p * L) ≤ q ^ p ∧ q ^ p ≤ exp (p * L) := by
  rw [rpow_def_of_pos hq]
  constructor
  · apply exp_le_exp.mpr
    calc
      -p * L = -L * p := by ring
      _ ≤ log q * p := mul_le_mul_of_nonneg_right (abs_le.mp hlog).1 hp
  · apply exp_le_exp.mpr
    calc
      log q * p ≤ L * p := mul_le_mul_of_nonneg_right (abs_le.mp hlog).2 hp
      _ = p * L := mul_comm _ _

/-- Uniform comparison with the frequency-two density in a deep region.
The same exponential factor bounds masses and, after inversion, resistances. -/
theorem r07_physicalDensity_bounds {D : ReferenceData} {right : Bool} {j : ℕ} {x L : ℝ}
    (hj : 2 ≤ j) (he : 0 < (if right then D.b else D.a))
    (hw : 0 ≤ D.w (tailPhysicalRadius right x))
    (hlog : |log (tailPhysicalRadius right x / (if right then D.b else D.a))| ≤ L) :
    exp (-(2 * (j : ℝ) ^ 2) * L) * r07PhysicalDensity D right 2 x ≤
      r07PhysicalDensity D right j x ∧
    r07PhysicalDensity D right j x ≤
      exp ((2 * (j : ℝ) ^ 2) * L) * r07PhysicalDensity D right 2 x := by
  have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hp : 0 ≤ 2 * (j : ℝ) ^ 2 - 8 := by nlinarith
  have hL : 0 ≤ L := (abs_nonneg _).trans hlog
  have hq := div_pos (r07_radius_pos right x) he
  have hbounds := r07_rpow_bounds_of_log hq hp hlog
  have hbase : 0 ≤ r07PhysicalDensity D right 2 x :=
    div_nonneg (mul_nonneg (rpow_nonneg hq.le _) hw) (r07_radius_pos right x).le
  rw [r07_physicalDensity_factor right j x he]
  constructor
  · apply mul_le_mul_of_nonneg_right _ hbase
    refine le_trans (exp_le_exp.mpr ?_) hbounds.1
    nlinarith only [hL]
  · apply mul_le_mul_of_nonneg_right _ hbase
    refine le_trans hbounds.2 (exp_le_exp.mpr ?_)
    nlinarith only [hL]

/-- The same multiplicative comparison controls the reciprocal densities. -/
theorem r07_inverse_density_bounds {p q E : ℝ} (hp : 0 < p) (hq : 0 < q)
    (h : exp (-E) * q ≤ p ∧ p ≤ exp E * q) :
    exp (-E) * q⁻¹ ≤ p⁻¹ ∧ p⁻¹ ≤ exp E * q⁻¹ := by
  constructor
  · have h' := inv_anti₀ hp h.2
    rw [mul_inv_rev, ← exp_neg] at h'
    simpa only [mul_comm] using h'
  · have h' := inv_anti₀ (mul_pos (exp_pos (-E)) hq) h.1
    rw [mul_inv_rev, ← exp_neg, neg_neg] at h'
    simpa only [mul_comm] using h'

/-- Integrating a density comparison preserves its constants. -/
theorem r07_integral_density_bounds {p q : ℝ → ℝ} {a b E : ℝ} (hab : a ≤ b)
    (hp : IntervalIntegrable p volume a b) (hq : IntervalIntegrable q volume a b)
    (h : ∀ x ∈ Icc a b, exp (-E) * q x ≤ p x ∧ p x ≤ exp E * q x) :
    exp (-E) * (∫ x in a..b, q x) ≤ (∫ x in a..b, p x) ∧
      (∫ x in a..b, p x) ≤ exp E * (∫ x in a..b, q x) := by
  constructor
  · have h' := intervalIntegral.integral_mono_on hab (hq.const_mul (exp (-E))) hp
      (fun x hx => (h x hx).1)
    simpa only [intervalIntegral.integral_const_mul] using h'
  · have h' := intervalIntegral.integral_mono_on hab hp (hq.const_mul (exp E))
      (fun x hx => (h x hx).2)
    simpa only [intervalIntegral.integral_const_mul] using h'

/-- Mass and resistance use one comparison argument, with the reciprocal
density handled by the same estimate rather than by a second coordinate case. -/
theorem r07_mass_resistance_comparison {p q : ℝ → ℝ} {a b E : ℝ} (hab : a ≤ b)
    (hp : ContinuousOn p (Icc a b)) (hq : ContinuousOn q (Icc a b))
    (hp0 : ∀ x ∈ Icc a b, 0 < p x) (hq0 : ∀ x ∈ Icc a b, 0 < q x)
    (h : ∀ x ∈ Icc a b, exp (-E) * q x ≤ p x ∧ p x ≤ exp E * q x) :
    (exp (-E) * (∫ x in a..b, q x) ≤ (∫ x in a..b, p x) ∧
      (∫ x in a..b, p x) ≤ exp E * (∫ x in a..b, q x)) ∧
    (exp (-E) * (∫ x in a..b, (q x)⁻¹) ≤ (∫ x in a..b, (p x)⁻¹) ∧
      (∫ x in a..b, (p x)⁻¹) ≤ exp E * (∫ x in a..b, (q x)⁻¹)) := by
  refine ⟨r07_integral_density_bounds hab
    (ContinuousOn.intervalIntegrable_of_Icc hab hp)
    (ContinuousOn.intervalIntegrable_of_Icc hab hq) h, ?_⟩
  apply r07_integral_density_bounds hab
    (ContinuousOn.intervalIntegrable_of_Icc hab (hp.inv₀ (fun x hx => (hp0 x hx).ne')))
    (ContinuousOn.intervalIntegrable_of_Icc hab (hq.inv₀ (fun x hx => (hq0 x hx).ne')))
  exact fun x hx => r07_inverse_density_bounds (hp0 x hx) (hq0 x hx) (h x hx)

/-- The physical general-frequency mass and resistance are uniformly
comparable to the normalized frequency-two quantities whenever the whole
interval satisfies one logarithmic radius bound. -/
theorem r07_physical_mass_resistance_comparison {D : ReferenceData} {right : Bool}
    {j : ℕ} {a b L : ℝ} (hj : 2 ≤ j) (hab : a ≤ b)
    (he : 0 < (if right then D.b else D.a)) (hw : ContDiff ℝ ∞ D.w)
    (hw0 : ∀ x ∈ Icc a b, 0 < D.w (tailPhysicalRadius right x))
    (hlog : ∀ x ∈ Icc a b,
      |log (tailPhysicalRadius right x / (if right then D.b else D.a))| ≤ L) :
    let E := (2 * (j : ℝ) ^ 2) * L
    (exp (-E) * (∫ x in a..b, r07PhysicalDensity D right 2 x) ≤
        (∫ x in a..b, r07PhysicalDensity D right j x) ∧
      (∫ x in a..b, r07PhysicalDensity D right j x) ≤
        exp E * (∫ x in a..b, r07PhysicalDensity D right 2 x)) ∧
    (exp (-E) * (∫ x in a..b, (r07PhysicalDensity D right 2 x)⁻¹) ≤
        (∫ x in a..b, (r07PhysicalDensity D right j x)⁻¹) ∧
      (∫ x in a..b, (r07PhysicalDensity D right j x)⁻¹) ≤
        exp E * (∫ x in a..b, (r07PhysicalDensity D right 2 x)⁻¹)) := by
  apply r07_mass_resistance_comparison hab
    (r07_contDiff_physicalDensity right j he hw).continuous.continuousOn
    (r07_contDiff_physicalDensity right 2 he hw).continuous.continuousOn
    (fun x hx => r07_physicalDensity_pos he (hw0 x hx))
    (fun x hx => r07_physicalDensity_pos he (hw0 x hx))
  intro x hx
  simpa only [neg_mul] using r07_physicalDensity_bounds hj he (hw0 x hx).le (hlog x hx)

end ContinuousFlexibility.Radial
