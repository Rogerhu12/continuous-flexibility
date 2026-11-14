module

public import ContinuousFlexibility.Radial.SelectedBoundaryMargin

/-!
# Actual normalized boundary data under a radius dilation

The same incoming function and the same natural representative are
transported. Radius dilation preserves the stand-in slope, while the
physical matching scale is computed from the actual target profile.
The full natural state is normalized, without dividing by its value.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real
open ContinuousFlexibility.Statements

theorem standInBoundarySlope_radialRadiusScale_one {κ : ℝ} (hκ : κ ≠ 0)
    (ε J p : ℝ) (u : ℝ → ℝ) :
    standInBoundarySlope ε J (κ * p) (radialRadiusScale κ 1 u) =
      standInBoundarySlope ε J p u := by
  unfold standInBoundarySlope
  rw [deriv_radialRadiusScale_apply_mul hκ, radialRadiusScale_apply_mul hκ, one_mul]
  have hnum : ε * (κ * p) * (1 / κ * deriv u p) = ε * p * deriv u p := by
    field_simp [hκ] <;> ring
  rw [hnum]

/-- Actual positive target geometry, the actual incoming normalization,
its proved slope interval and the transported selected angle give all
normalized matching data at the rescaled cut. -/
theorem selectedBoundaryRadiusScale_data {D E : ReferenceData}
    {κ β p ε δ : ℝ} {j : ℕ} {u v : ℝ → ℝ}
    (hκ : κ ≠ 0) (hβ : β ≠ 0) (hj : (j : ℝ) ≠ 0)
    (hp : 0 < κ * p) (hW : 0 < E.w (κ * p))
    (hε : ε = 1 ∨ ε = -1) (hprofile : E.w (κ * p) = (β * κ) * D.w p)
    (hu : u p = 1)
    (hd : 0 < standInBoundarySlope ε ((j : ℝ) ^ 2) p u ∧
      standInBoundarySlope ε ((j : ℝ) ^ 2) p u ≤ 1 / 2)
    (hδ : 0 < δ)
    (hsep : δ ≤ radialAngleSine (radialState D j p (D.w p) v) (radialState D j p (D.w p) u)) :
    let U := radialRadiusScale κ 1 u
    let V := radialRadiusScale κ 1 v
    let d := standInBoundarySlope ε ((j : ℝ) ^ 2) (κ * p) U
    let AB := outerUnitState (selectedBoundaryState E j ε (κ * p) V)
    U (κ * p) = 1 ∧
      0 < standInBoundaryScale ((j : ℝ) ^ 2) (E.w (κ * p)) (κ * p) ∧
      0 < d ∧ d ≤ 1 / 2 ∧
      selectedBoundaryState E j ε (κ * p) V ≠ 0 ∧
      AB.1 ^ 2 + AB.2 ^ 2 = 1 ∧ δ / 4 ≤ |AB.1 * d - AB.2| := by
  let U := radialRadiusScale κ 1 u
  let V := radialRadiusScale κ 1 v
  have hU : U (κ * p) = 1 := by
    simpa only [U, radialRadiusScale_apply_mul hκ, one_mul] using hu
  have hdU : 0 < standInBoundarySlope ε ((j : ℝ) ^ 2) (κ * p) U ∧
      standInBoundarySlope ε ((j : ℝ) ^ 2) (κ * p) U ≤ 1 / 2 := by
    simpa only [U, standInBoundarySlope_radialRadiusScale_one hκ] using hd
  have hsepE : δ ≤ radialAngleSine
      (radialState E j (κ * p) (E.w (κ * p)) V)
      (radialState E j (κ * p) (E.w (κ * p)) U) := by
    have heq := radialState_radiusScale_angle (D := D) (E := E) j
      (κ := κ) (β := β) (α := 1) (γ := 1) (r := p) (scale := D.w p)
      hκ hβ one_ne_zero one_ne_zero hprofile v u
    rw [← hprofile] at heq
    exact hsep.trans_eq heq.symm
  obtain ⟨hunit, hmargin⟩ := selectedBoundaryState_matching_margin E hj hp.ne' hW.ne'
    hε (by rw [hU]; exact one_ne_zero) hδ hsepE
  have hne : selectedBoundaryState E j ε (κ * p) V ≠ 0 := by
    intro hz
    simpa [outerUnitState, hz] using hunit
  exact ⟨hU, standInBoundaryScale_pos (sq_pos_of_ne_zero hj) hW hp,
    hdU.1, hdU.2, hne, hunit, hmargin⟩

end ContinuousFlexibility.Radial
