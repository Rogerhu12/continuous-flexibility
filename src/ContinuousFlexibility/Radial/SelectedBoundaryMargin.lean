module

public import ContinuousFlexibility.Radial.SelectedReferenceTransport
public import ContinuousFlexibility.Radial.SelectedStateMargin
public import ContinuousFlexibility.Radial.StandInBoundarySlope
public import ContinuousFlexibility.Radial.R07AngleScale
public import ContinuousFlexibility.Radial.OuterNormalizedState

/-!
# The actual normalized boundary state and the selected margin

The radius/height transport preserves the selected angle exactly.
At a matching cut, the physical state is normalized by its full Euclidean
length. Its first coordinate may vanish. The stand-in logarithmic slope
then gives the actual diagonal matching margin, with the fixed frame
factor and no division by the natural solution's boundary value.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real
open ContinuousFlexibility.Statements

/-- Independent nonzero solution amplitudes and the actual profile
dilation preserve the angle used in the selected-tail statement. -/
theorem radialState_radiusScale_angle {D E : ReferenceData} (j : ℕ)
    {κ β α γ r scale : ℝ} (hκ : κ ≠ 0) (hβ : β ≠ 0)
    (hα : α ≠ 0) (hγ : γ ≠ 0)
    (hprofile : E.w (κ * r) = (β * κ) * D.w r) (u v : ℝ → ℝ) :
    radialAngleSine
      (radialState E j (κ * r) ((β * κ) * scale) (radialRadiusScale κ α u))
      (radialState E j (κ * r) ((β * κ) * scale) (radialRadiusScale κ γ v)) =
      radialAngleSine (radialState D j r scale u) (radialState D j r scale v) := by
  rw [radialState_radialRadiusScale j hκ hβ hprofile u,
    radialState_radialRadiusScale j hκ hβ hprofile v,
    radialAngleSine_scale hα hγ]

/-- Value and physical outward flux divided by the matching scale. -/
def selectedBoundaryState (D : ReferenceData) (j : ℕ) (ε r : ℝ)
    (u : ℝ → ℝ) : ℝ × ℝ :=
  outerFluxState (standInBoundaryScale ((j : ℝ) ^ 2) (D.w r) r)
    (fun t => ε * D.w t) u r

theorem radialState_eq_selectedBoundaryFrame (D : ReferenceData)
    {j : ℕ} {r ε : ℝ} (hj : (j : ℝ) ≠ 0) (hr : r ≠ 0)
    (hw : D.w r ≠ 0) (hε : ε = 1 ∨ ε = -1) (u : ℝ → ℝ) :
    radialState D j r (D.w r) u =
      selectedStateFrame ε (selectedBoundaryState D j ε r u) :=
  radialState_eq_selectedStateFrame D hj hr hw hε u

/-- The incoming physical state is its nonzero value times the slope
state. This also handles a stand-in normalized at a different cut. -/
theorem selectedBoundaryState_eq_value_slope (D : ReferenceData)
    {j : ℕ} {r ε : ℝ} {u : ℝ → ℝ}
    (hj : (j : ℝ) ≠ 0) (hr : r ≠ 0) (hw : D.w r ≠ 0) (hu : u r ≠ 0) :
    selectedBoundaryState D j ε r u =
      (u r * 1, u r * standInBoundarySlope ε ((j : ℝ) ^ 2) r u) := by
  apply Prod.ext
  · change u r = u r * 1
    exact (mul_one _).symm
  · change ε * D.w r * deriv u r / (((j : ℝ) ^ 2) * D.w r / r) =
        u r * (ε * r * deriv u r / (((j : ℝ) ^ 2) * u r))
    field_simp [hj, hr, hw, hu] <;> ring

theorem selectedStateFrame_const_mul (ε c : ℝ) (v : ℝ × ℝ) :
    selectedStateFrame ε (c * v.1, c * v.2) =
      (c * (selectedStateFrame ε v).1, c * (selectedStateFrame ε v).2) := by
  apply Prod.ext <;>
    simp only [selectedStateFrame, selectedStateTransfer] <;> ring

/-- Full-state normalization can be performed before or after passing
to the selected frame, with exactly the same angle. -/
theorem radialAngleSine_frame_outerUnitState (ε : ℝ)
    {v : ℝ × ℝ} (hv : v ≠ 0) (w : ℝ × ℝ) :
    radialAngleSine (selectedStateFrame ε (outerUnitState v)) w =
      radialAngleSine (selectedStateFrame ε v) w := by
  have hlen : sqrt (v.1 ^ 2 + v.2 ^ 2) ≠ 0 := (sqrt_pos.mpr (outerState_sq_pos hv)).ne'
  have heq : outerUnitState v =
      ((sqrt (v.1 ^ 2 + v.2 ^ 2))⁻¹ * v.1,
       (sqrt (v.1 ^ 2 + v.2 ^ 2))⁻¹ * v.2) := by
    apply Prod.ext <;> simp only [outerUnitState, div_eq_mul_inv] <;> ring
  rw [heq, selectedStateFrame_const_mul, radialAngleSine_scale_left (inv_ne_zero hlen)]

/-- The selected angle at the actual cut produces the normalized diagonal
matching margin. The natural boundary value is allowed to be zero. -/
theorem selectedBoundaryState_matching_margin (D : ReferenceData)
    {j : ℕ} {r ε δ : ℝ} {u v : ℝ → ℝ}
    (hj : (j : ℝ) ≠ 0) (hr : r ≠ 0) (hw : D.w r ≠ 0)
    (hε : ε = 1 ∨ ε = -1) (hu : u r ≠ 0) (hδ : 0 < δ)
    (hsep : δ ≤ radialAngleSine
      (radialState D j r (D.w r) v) (radialState D j r (D.w r) u)) :
    let V := outerUnitState (selectedBoundaryState D j ε r v)
    V.1 ^ 2 + V.2 ^ 2 = 1 ∧
      δ / 4 ≤ |V.1 * standInBoundarySlope ε ((j : ℝ) ^ 2) r u - V.2| := by
  let d := standInBoundarySlope ε ((j : ℝ) ^ 2) r u
  let V₀ := selectedBoundaryState D j ε r v
  have hselected : δ ≤ radialAngleSine
      (selectedStateFrame ε V₀) (selectedStateFrame ε (1, d)) := by
    rw [radialState_eq_selectedBoundaryFrame D hj hr hw hε v,
      radialState_eq_selectedBoundaryFrame D hj hr hw hε u,
      selectedBoundaryState_eq_value_slope D hj hr hw hu] at hsep
    change δ ≤ radialAngleSine (selectedStateFrame ε V₀)
      (selectedStateFrame ε (u r * (1, d).1, u r * (1, d).2)) at hsep
    rw [selectedStateFrame_const_mul, radialAngleSine_scale_right hu] at hsep
    exact hsep
  have hV₀ : V₀ ≠ 0 := by
    intro hz
    have hframe : selectedStateFrame ε V₀ = (0, 0) := by
      rw [hz]
      simp only [selectedStateFrame, selectedStateTransfer, Prod.fst_zero,
        Prod.snd_zero, mul_zero, add_zero]
    rw [hframe] at hselected
    have hzangle : δ ≤ 0 := by simpa [radialAngleSine] using hselected
    exact (not_le_of_gt hδ) hzangle
  have hunit := outerUnitState_unit hV₀
  refine ⟨hunit, ?_⟩
  apply normalized_matching_margin_of_frame hε hunit
  rw [radialAngleSine_frame_outerUnitState ε hV₀]
  exact hselected

end ContinuousFlexibility.Radial
