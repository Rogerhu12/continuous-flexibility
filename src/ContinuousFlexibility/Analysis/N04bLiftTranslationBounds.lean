module

public import Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Translation-number bounds from an actual conjugacy defect

Mathlib's lifts have period one. The physical angular coordinate in this
project has period π, so its translation number is π times that of the
normalized lift. Conjugacy invariance and comparison with translations
give a quantitative bound from a uniformly bounded conjugacy defect.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open CircleDeg1Lift

/-- Normalize an actual π-periodic lift to mathlib's period-one lift. -/
def n04bPiLift (F : ℝ → ℝ) (hmono : Monotone F)
    (hperiod : ∀ θ : ℝ, F (θ + Real.pi) = F θ + Real.pi) : CircleDeg1Lift where
  toFun x := F (Real.pi * x) / Real.pi
  monotone' := by
    intro x y hxy
    exact div_le_div_of_nonneg_right
      (hmono (mul_le_mul_of_nonneg_left hxy Real.pi_pos.le)) Real.pi_pos.le
  map_add_one' := by
    intro x
    rw [mul_add, mul_one, hperiod]
    field_simp [Real.pi_ne_zero]
    <;> ring

theorem n04bPiLift_apply (F : ℝ → ℝ) (hmono : Monotone F)
    (hperiod : ∀ θ : ℝ, F (θ + Real.pi) = F θ + Real.pi) (x : ℝ) :
    n04bPiLift F hmono hperiod x = F (Real.pi * x) / Real.pi := rfl

/-- The actual physical map associated with a normalized lift. -/
def n04bPhysicalLift (f : CircleDeg1Lift) (θ : ℝ) : ℝ :=
  Real.pi * f (θ / Real.pi)

theorem n04bPhysicalLift_pi (f : CircleDeg1Lift) (x : ℝ) :
    n04bPhysicalLift f (Real.pi * x) = Real.pi * f x := by
  have hx : (Real.pi * x) / Real.pi = x := by field_simp [Real.pi_ne_zero]
  rw [n04bPhysicalLift, hx]

theorem n04bPhysicalLift_normalize (F : ℝ → ℝ) (hmono : Monotone F)
    (hperiod : ∀ θ : ℝ, F (θ + Real.pi) = F θ + Real.pi) (θ : ℝ) :
    n04bPhysicalLift (n04bPiLift F hmono hperiod) θ = F θ := by
  have hθ : Real.pi * (θ / Real.pi) = θ := by field_simp [Real.pi_ne_zero]
  rw [n04bPhysicalLift, n04bPiLift_apply, hθ]
  field_simp [Real.pi_ne_zero]

/-- Translation number in the physical angular units. -/
def n04bPhysicalTranslationNumber (f : CircleDeg1Lift) : ℝ :=
  Real.pi * f.translationNumber

/-- A uniformly bounded defect of an actual conjugacy bounds the
translation number by the same error. -/
theorem n04b_translationNumber_bound_of_conjugacy_defect
    (f : CircleDeg1Lift) (h : CircleDeg1Liftˣ) (t δ : ℝ)
    (hdefect : ∀ x : ℝ, |h (f x) - h x - t| ≤ δ) :
    |f.translationNumber - t| ≤ δ := by
  let g : CircleDeg1Lift := (h : CircleDeg1Lift) * f * (h⁻¹ : CircleDeg1Liftˣ)
  have hg (y : ℝ) : g y = h (f (h⁻¹ y)) := by
    simp only [g, CircleDeg1Lift.mul_apply]
  have hbound (y : ℝ) : -δ ≤ g y - y - t ∧ g y - y - t ≤ δ := by
    have hb := abs_le.mp (hdefect (h⁻¹ y))
    rw [CircleDeg1Lift.units_apply_inv_apply] at hb
    simpa only [hg y] using hb
  have hlo : t - δ ≤ g.translationNumber :=
    g.le_translationNumber_of_add_le (fun y => by have := (hbound y).1; linarith)
  have hhi : g.translationNumber ≤ t + δ :=
    g.translationNumber_le_of_le_add (fun y => by have := (hbound y).2; linarith)
  have he : g.translationNumber = f.translationNumber :=
    CircleDeg1Lift.translationNumber_conj_eq h f
  rw [he] at hlo hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end ContinuousFlexibility.Analysis
