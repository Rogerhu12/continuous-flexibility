import ContinuousFlexibility.Statements.RadialTargets
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Tactic.FieldSimp

/-!
# Radius and height transport of selected radial states

The same physical dilation transports the profile by `β κ` and a solution
by `α`. The resulting Jacobi expression has the exact factor `β α / κ`.
The derivative identities use mathlib's derivative of composition with a
scalar map, which is valid for arbitrary functions.

The state identity only needs the profile height at the comparison point.
A version for prescribed first jets also applies when the target solution
agrees with the scaled one only near that point.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

/-- Physical radius dilation together with an independent amplitude. -/
def radialRadiusScale (κ α : ℝ) (u : ℝ → ℝ) (r : ℝ) : ℝ :=
  α * u (r / κ)

private theorem radiusScale_div_cancel {κ : ℝ} (hκ : κ ≠ 0) (r : ℝ) :
    κ * r / κ = r := by
  field_simp [hκ] <;> ring

theorem radialRadiusScale_apply_mul {κ : ℝ} (hκ : κ ≠ 0)
    (α : ℝ) (u : ℝ → ℝ) (r : ℝ) :
    radialRadiusScale κ α u (κ * r) = α * u r := by
  unfold radialRadiusScale
  rw [radiusScale_div_cancel hκ r]

/-- The actual derivative scales without any differentiability premise. -/
theorem deriv_radialRadiusScale (κ α : ℝ) (u : ℝ → ℝ) (r : ℝ) :
    deriv (radialRadiusScale κ α u) r = α / κ * deriv u (r / κ) := by
  have hcomp : (fun t : ℝ => u (t / κ)) = fun t => u (κ⁻¹ * t) := by
    funext t
    congr 1
    simpa only [div_eq_mul_inv] using mul_comm t κ⁻¹
  have hr : κ⁻¹ * r = r / κ := by
    simpa only [div_eq_mul_inv] using mul_comm κ⁻¹ r
  unfold radialRadiusScale
  rw [deriv_const_mul_field, hcomp, deriv_comp_mul_left]
  simp only [smul_eq_mul, hr, div_eq_mul_inv]
  ring

theorem deriv_radialRadiusScale_apply_mul {κ : ℝ} (hκ : κ ≠ 0)
    (α : ℝ) (u : ℝ → ℝ) (r : ℝ) :
    deriv (radialRadiusScale κ α u) (κ * r) = α / κ * deriv u r := by
  rw [deriv_radialRadiusScale, radiusScale_div_cancel hκ r]

/-- The physical flux has amplitude `β α`, with no remaining radius
factor. This function identity is also used under the outer derivative. -/
theorem radialRadiusScale_flux {κ : ℝ} (hκ : κ ≠ 0)
    (α β : ℝ) (w u : ℝ → ℝ) :
    (fun r => radialRadiusScale κ (β * κ) w r *
      deriv (radialRadiusScale κ α u) r) =
      radialRadiusScale κ (β * α) (fun r => w r * deriv u r) := by
  funext r
  rw [deriv_radialRadiusScale]
  unfold radialRadiusScale
  field_simp [hκ] <;> ring

/-- Exact covariance of the radial Jacobi expression. Both the profile
and solution are arbitrary functions; no smoothness assumption is hidden. -/
theorem radialJacobi_radialRadiusScale {κ : ℝ} (hκ : κ ≠ 0)
    (J α β : ℝ) (w u : ℝ → ℝ) (r : ℝ) :
    radialJacobi J (radialRadiusScale κ (β * κ) w)
      (radialRadiusScale κ α u) (κ * r) =
      (β * α / κ) * radialJacobi J w u r := by
  unfold radialJacobi
  rw [radialRadiusScale_flux hκ α β w u,
    deriv_radialRadiusScale_apply_mul hκ (β * α) (fun t => w t * deriv u t) r,
    deriv_radialRadiusScale_apply_mul hκ (β * κ) w r,
    radialRadiusScale_apply_mul hκ α u r]
  by_cases hr : r = 0
  · subst r
    simp only [mul_zero, div_zero, zero_mul, sub_zero]
  · field_simp [hκ, hr] <;> ring

theorem radialJacobi_radialRadiusScale_eq_zero {κ J α β r : ℝ}
    {w u : ℝ → ℝ} (hκ : κ ≠ 0) (hzero : radialJacobi J w u r = 0) :
    radialJacobi J (radialRadiusScale κ (β * κ) w)
      (radialRadiusScale κ α u) (κ * r) = 0 := by
  rw [radialJacobi_radialRadiusScale hκ J α β w u r, hzero, mul_zero]

/-- Nonzero amplitudes preserve and reflect the homogeneous equation. -/
theorem radialJacobi_radialRadiusScale_eq_zero_iff {κ J α β r : ℝ}
    {w u : ℝ → ℝ} (hκ : κ ≠ 0) (hα : α ≠ 0) (hβ : β ≠ 0) :
    radialJacobi J (radialRadiusScale κ (β * κ) w)
      (radialRadiusScale κ α u) (κ * r) = 0 ↔ radialJacobi J w u r = 0 := by
  rw [radialJacobi_radialRadiusScale hκ J α β w u r]
  have hfactor : β * α / κ ≠ 0 := div_ne_zero (mul_ne_zero hβ hα) hκ
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hfactor
  · intro h
    rw [h, mul_zero]

/-- A pointwise height identity and the actual first jet suffice to
transport the boundary state. No equality of complete references is used. -/
theorem radialState_eq_of_scaled_jet {D D' : ReferenceData} (j : ℕ)
    {κ α β r scale : ℝ} {u v : ℝ → ℝ} (hκ : κ ≠ 0) (hβ : β ≠ 0)
    (hprofile : D'.w (κ * r) = (β * κ) * D.w r)
    (hvalue : v (κ * r) = α * u r)
    (hderiv : deriv v (κ * r) = α / κ * deriv u r) :
    radialState D' j (κ * r) ((β * κ) * scale) v =
      (α * (radialState D j r scale u).1, α * (radialState D j r scale u).2) := by
  have hratio : D'.w (κ * r) / ((β * κ) * scale) = D.w r / scale := by
    rw [hprofile]
    by_cases hs : scale = 0
    · simp [hs]
    · field_simp [hβ, hκ, hs] <;> ring
  have hjet : (κ * r) * (α / κ * deriv u r) = α * (r * deriv u r) := by
    field_simp [hκ] <;> ring
  apply Prod.ext
  · exact hvalue
  · change D'.w (κ * r) / ((β * κ) * scale) *
        ((κ * r) * deriv v (κ * r) / (j : ℝ) ^ 2 - v (κ * r)) =
      α * (D.w r / scale * (r * deriv u r / (j : ℝ) ^ 2 - u r))
    rw [hratio, hvalue, hderiv, hjet]
    ring

/-- The state covariance required by an actual radius/height transport
in R08. The reference scale is transported by the same factor as the profile. -/
theorem radialState_radialRadiusScale {D D' : ReferenceData} (j : ℕ)
    {κ α β r scale : ℝ} (hκ : κ ≠ 0) (hβ : β ≠ 0)
    (hprofile : D'.w (κ * r) = (β * κ) * D.w r) (u : ℝ → ℝ) :
    radialState D' j (κ * r) ((β * κ) * scale) (radialRadiusScale κ α u) =
      (α * (radialState D j r scale u).1, α * (radialState D j r scale u).2) :=
  radialState_eq_of_scaled_jet j hκ hβ hprofile
    (radialRadiusScale_apply_mul hκ α u r)
    (deriv_radialRadiusScale_apply_mul hκ α u r)

end ContinuousFlexibility.Radial
