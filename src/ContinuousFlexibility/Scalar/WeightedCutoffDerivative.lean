import ContinuousFlexibility.Scalar.WeightedCompactRadial
import ContinuousFlexibility.Scalar.WeightedDecodeLift

/-!
# The actual cutoff derivative in the weighted height space

The prescribed cutoff has derivative supported in a compact subset of the
physical core. This supplies a fixed vector in every weight, using the
original Sobolev decoder and its exact range theorem.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The true derivative of a prescribed cutoff is a height member at every
weight exponent. Compact support is part of the original cutoff data. -/
theorem cutoffDerivative_heightMember
    {D : ReferenceData} {T : MaterialData} {χ : ℝ → ℝ}
    (hT : IsMaterialData D T) (hχ : CutoffConditions D χ) (γ : ℝ) :
    HeightMember D T γ (fun p => deriv χ p.1) := by
  have hd : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ.1).2
  obtain ⟨K, hK, hKcore, _, hzero⟩ := hχ.2.2
  exact heightMember_radial_of_compact_support hT hd
    ⟨K, hK, hKcore, fun r hr _ => hzero r hr⟩

/-- The fixed weighted vector representing the derivative of the actual left
cutoff. It is independent of the scalar state. -/
def scalarCutoffDerivativeHeight
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (γ : ℝ) :
    (S.height γ).Space :=
  SobolevModelData.liftHeight (hS.1 γ) (fun p => deriv S.chiLeft p.1)
    (cutoffDerivative_heightMember hT hS.2.2.1 γ)

theorem decode_scalarCutoffDerivativeHeight
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (γ : ℝ) :
    (S.height γ).decode (scalarCutoffDerivativeHeight hT hS γ) =
      fun p => deriv S.chiLeft p.1 :=
  SobolevModelData.decode_liftHeight (hS.1 γ) _ _

theorem decode_smul_scalarCutoffDerivativeHeight
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (γ c : ℝ) :
    (S.height γ).decode (c • scalarCutoffDerivativeHeight hT hS γ) =
      fun p => c * deriv S.chiLeft p.1 := by
  rw [map_smul, decode_scalarCutoffDerivativeHeight]
  rfl

theorem grading_scalarCutoffDerivativeHeight
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (γ : ℝ) (s : ℕ) :
    (S.height γ).grading s (scalarCutoffDerivativeHeight hT hS γ) =
      physicalNorm T γ s (fun p => deriv S.chiLeft p.1) := by
  rw [sobolevGrading_eq_physicalNorm (hS.1 γ), decode_scalarCutoffDerivativeHeight]

end ContinuousFlexibility.Statements
