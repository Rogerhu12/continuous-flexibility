module

public import ContinuousFlexibility.Analysis.N01cNormalizedCoefficients
public import ContinuousFlexibility.Analysis.N01cCommonType

/-!
# The original minus speed in normalized physical variables

The corrected determinant identity separates the square root into the
actual optical square and the already positive height discriminant.
This is an identity for the original speed, with the original profile,
height and controls. Positivity of the optical square is supplied by the
common geometric neighbourhood, separately from this algebraic identity.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

/-- Exact scalar normalization of the ordinary minus characteristic.
The optical square is allowed to be arbitrary here: the square-root
identity itself uses only the positive profile and height discriminant. -/
theorem minusSpeed_normalized_of_determinant
    {w wr r d Q E pr c : ℝ}
    (hw : 0 < w) (hr : r ≠ 0) (hd : 0 < d) (hQ : Q ≠ 0)
    (hdet : (Q * inverseDThreeHalves d) * c -
        (-E * pr * inverseDThreeHalves d) ^ 2 = (w * wr / r) / d ^ 2) :
    (-E * pr * inverseDThreeHalves d) / (Q * inverseDThreeHalves d) -
        Real.sqrt ((-E * pr * inverseDThreeHalves d) ^ 2 -
          (Q * inverseDThreeHalves d) * c) / (Q * inverseDThreeHalves d) =
      -E * pr / (w * (Q / w)) -
        (Real.sqrt d / (Q / w)) * Real.sqrt (-wr / (r * w)) := by
  have hs : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  have hdisc : (-E * pr * inverseDThreeHalves d) ^ 2 -
        (Q * inverseDThreeHalves d) * c =
      (w / d) ^ 2 * (-wr / (r * w)) := by
    calc
      _ = -((w * wr / r) / d ^ 2) := by linarith only [hdet]
      _ = _ := by field_simp [hr, hw.ne', hd.ne'] <;> ring
  rw [hdisc, Real.sqrt_mul (sq_nonneg (w / d)),
    Real.sqrt_sq (div_nonneg hw.le hd.le)]
  unfold inverseDThreeHalves
  field_simp [hw.ne', hr, hd.ne', hs, hQ]
  <;> ring

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The ordinary minus speed has exactly the normalized drift and optical
factors used in the physical-coordinate estimates. -/
theorem n01_minusCharacteristicSpeed_normalized
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    let w := stateProfile D S C z.1
    let h := stateHeight D S C z
    let E := profileEnergy w p
    let Q := heightQ E (heightRadial h p) (angularPartial (heightAngular h) p)
    let pr := radialPartial (heightAngular h) p
    let d := polarDiscriminant w h p
    minusCharacteristicSpeed (originalCoefficients D S C z) p =
      -E * pr / (w p.1 * (Q / w p.1)) -
        (Real.sqrt d / (Q / w p.1)) *
          Real.sqrt (-deriv w p.1 / (p.1 * w p.1)) := by
  obtain ⟨_, hRef⟩ := hA.1.1
  have hr : p.1 ≠ 0 := (hRef.1.1.trans hp.1.1).ne'
  have hden := n01PartB_denominators_pos hRef.1 hS hA.2.1 hB hz hp
  have hw : DifferentiableAt ℝ (stateProfile D S C z.1) p.1 :=
    (contDiff_stateProfile_of_partA hS hT hA z.1).differentiable (by simp) p.1
  have hdet := polar_corrected_determinant (stateHeight D S C z) hw hr
    hden.2.2 hden.2.1.ne'
  exact minusSpeed_normalized_of_determinant hden.1 hr hden.2.2 hden.2.1.ne' hdet

/-- One genuine common radius gives the spatial-smoothness clause of the
speed stage at every order and on every original negative component. -/
theorem n01_exists_common_speedSpatialSmoothness
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε₀ : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε₀ : 0 < ε₀)
    (hB : N01PartB D S C base ε₀)
    (hlower : ∃ K : ℝ, 0 < K ∧ ∀ m r,
      r ∈ Ioo (C.left m) (C.right m) →
      K⁻¹ * T.E0 (T.sample (C.cell m)) ^ (-K) *
          min (r - C.left m) (C.right m - r) ≤
        -deriv D.w r / (r * D.w r)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε₀ ∧
      ∀ z ∈ stateNeighborhood S C base ε, ∀ m,
        ContDiffOn ℝ ∞ (minusCharacteristicSpeed (originalCoefficients D S C z))
          (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) := by
  obtain ⟨ε₁, hε₁, hnegative⟩ :=
    n01_exists_common_negativeType_of_referenceLower hS hT hA hlower
  refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, min_le_left _ _, ?_⟩
  intro z hz m
  have hz₀ : z ∈ stateNeighborhood S C base ε₀ :=
    ⟨hz.1.trans_le (min_le_left _ _), hz.2.trans_le (min_le_left _ _)⟩
  have hz₁ : z ∈ stateNeighborhood S C base ε₁ :=
    ⟨hz.1.trans_le (min_le_right _ _), hz.2.trans_le (min_le_right _ _)⟩
  exact n01_minusCharacteristicSpeed_contDiffOn_component hS hT hA hB hz₀ m
    (hnegative base z hz₁ m)

end ContinuousFlexibility.Statements
