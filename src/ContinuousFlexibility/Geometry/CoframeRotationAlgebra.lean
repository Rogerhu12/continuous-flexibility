module

public import ContinuousFlexibility.Geometry.CartesianCoframe
public import Mathlib.Tactic.Linarith

/-! # The actual relative rotation of equally oriented orthonormal coframes -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

def relativeCoframeCos (η₁ η₂ ξ₁ : PlaneOneForm) (x : PolarPoint) : ℝ :=
  (ξ₁.radial x * η₂.angular x - ξ₁.angular x * η₂.radial x) /
    wedgeCoefficient η₁ η₂ x

def relativeCoframeSin (η₁ η₂ ξ₁ : PlaneOneForm) (x : PolarPoint) : ℝ :=
  (ξ₁.radial x * η₁.angular x - ξ₁.angular x * η₁.radial x) /
    wedgeCoefficient η₁ η₂ x

theorem oriented_coframe_rotation_algebra
    {a b c d u v s t : ℝ}
    (h1 : u ^ 2 + s ^ 2 = a ^ 2 + c ^ 2)
    (h2 : v ^ 2 + t ^ 2 = b ^ 2 + d ^ 2)
    (h3 : u * v + s * t = a * b + c * d)
    (hor : 0 < (a * d - b * c) * (u * t - v * s)) :
    let C := (u * d - v * c) / (a * d - b * c)
    let S := (u * b - v * a) / (a * d - b * c)
    C ^ 2 + S ^ 2 = 1 ∧ u = C * a - S * c ∧ v = C * b - S * d ∧
      s = S * a + C * c ∧ t = S * b + C * d := by
  have hD : a * d - b * c ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hor
    exact (lt_irrefl 0) hor
  have hsq : (u * t - v * s) ^ 2 = (a * d - b * c) ^ 2 := by
    calc
      _ = (u ^ 2 + s ^ 2) * (v ^ 2 + t ^ 2) - (u * v + s * t) ^ 2 := by ring
      _ = (a ^ 2 + c ^ 2) * (b ^ 2 + d ^ 2) - (a * b + c * d) ^ 2 := by rw [h1, h2, h3]
      _ = _ := by ring
  have hdet : u * t - v * s = a * d - b * c := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with heq | hneg
    · exact heq
    · rw [hneg] at hor
      nlinarith [sq_nonneg (a * d - b * c)]
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [div_pow, div_pow, ← add_div]
    apply (div_eq_one_iff_eq (pow_ne_zero 2 hD)).mpr
    calc
      _ = u ^ 2 * (b ^ 2 + d ^ 2) + v ^ 2 * (a ^ 2 + c ^ 2) -
          2 * u * v * (a * b + c * d) := by ring
      _ = u ^ 2 * (v ^ 2 + t ^ 2) + v ^ 2 * (u ^ 2 + s ^ 2) -
          2 * u * v * (u * v + s * t) := by rw [← h1, ← h2, ← h3]
      _ = (u * t - v * s) ^ 2 := by ring
      _ = _ := by rw [hdet]
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← sub_div]
    apply (eq_div_iff hD).mpr
    ring
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← sub_div]
    apply (eq_div_iff hD).mpr
    ring
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    apply (eq_div_iff hD).mpr
    calc
      _ = s * (u * t - v * s) := by rw [hdet]
      _ = u * (a * b + c * d) - v * (a ^ 2 + c ^ 2) := by rw [← h1, ← h3]; ring
      _ = _ := by ring
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    apply (eq_div_iff hD).mpr
    calc
      _ = t * (u * t - v * s) := by rw [hdet]
      _ = u * (b ^ 2 + d ^ 2) - v * (a * b + c * d) := by rw [← h2, ← h3]; ring
      _ = _ := by ring

theorem relativeCoframe_rotation
    {η₁ η₂ ξ₁ ξ₂ : PlaneOneForm} {x : PolarPoint}
    (hmetric : ∀ v : PolarPoint, formValue ξ₁ x v ^ 2 + formValue ξ₂ x v ^ 2 =
      formValue η₁ x v ^ 2 + formValue η₂ x v ^ 2)
    (hor : 0 < wedgeCoefficient η₁ η₂ x * wedgeCoefficient ξ₁ ξ₂ x) :
    let C := relativeCoframeCos η₁ η₂ ξ₁ x
    let S := relativeCoframeSin η₁ η₂ ξ₁ x
    C ^ 2 + S ^ 2 = 1 ∧
      ξ₁.radial x = C * η₁.radial x - S * η₂.radial x ∧
      ξ₁.angular x = C * η₁.angular x - S * η₂.angular x ∧
      ξ₂.radial x = S * η₁.radial x + C * η₂.radial x ∧
      ξ₂.angular x = S * η₁.angular x + C * η₂.angular x := by
  have h1 := hmetric (1, 0)
  have h2 := hmetric (0, 1)
  have h3 := hmetric (1, 1)
  simp only [formValue, mul_one, mul_zero, add_zero, zero_add] at h1 h2 h3
  have hcross : ξ₁.radial x * ξ₁.angular x + ξ₂.radial x * ξ₂.angular x =
      η₁.radial x * η₁.angular x + η₂.radial x * η₂.angular x := by
    nlinarith
  exact oriented_coframe_rotation_algebra h1 h2 hcross hor

end ContinuousFlexibility
