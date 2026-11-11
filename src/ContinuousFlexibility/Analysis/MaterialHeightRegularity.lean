import ContinuousFlexibility.Analysis.MaterialCylinderPointwise
import ContinuousFlexibility.Analysis.MaterialOrdinaryJets
import ContinuousFlexibility.Analysis.MaterialHeightExtension
import ContinuousFlexibility.Analysis.WeakBranchCore

/-!
# Smooth flat extensions of actual material heights

The weighted cylinder norms control the material jets. The ordinary jets
then decay at the actual radial endpoints. This removes the height
regularity premise from the weak-branch construction at a fixed nonzero
parameter.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open scoped ContDiff

theorem heightMember_contDiff_and_flatJets {D : ReferenceData} {T : MaterialData}
    {γ : ℝ} {f : PolarPoint → ℝ} (hT : IsMaterialData D T) (hγ : 0 < γ)
    (hf : HeightMember D T γ f) : ContDiff ℝ ∞ f ∧ UniformFlatJets D f := by
  apply material_height_extension_of_ordinary_bounds hT hγ hf
  intro a b
  obtain ⟨K, hK, hbound⟩ := mixedDerivative_bound_of_materialPullback hT hf.1
    (heightMember_materialPullback_mixedDerivative_uniform_bound hT hf) a b
  exact ⟨K, 1, hK, fun p hp => by simpa only [Real.rpow_one] using hbound p hp⟩

theorem physical_height_contDiff_and_flatJets {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ : ℝ} (hγ : 0 < γ) (u : (S.height γ).Space) :
    ContDiff ℝ ∞ ((S.height γ).decode u) ∧ UniformFlatJets D ((S.height γ).decode u) :=
  heightMember_contDiff_and_flatJets hT hγ ((hS.1 γ).2.2.2.1 u)

theorem physical_height_with_cutoff_contDiff {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ : ℝ} (hγ : 0 < γ) (u : (S.height γ).Space) (c : ℝ) :
    ContDiff ℝ ∞ (fun p : PolarPoint => (S.height γ).decode u p + c * S.chiLeft p.1) :=
  (physical_height_contDiff_and_flatJets hT hS hγ u).1.add
    (contDiff_const.mul (hS.2.2.1.1.comp contDiff_fst))

theorem IsWeakBranch.nonempty_flatAnnularCore_of_profile_smooth
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {base loss : ℕ} {ε : ℝ} {B : WeakBranchData S}
    (hB : IsWeakBranch D S C R base ε B) (hN : N01Properties D T S C base loss ε)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) {q : ℝ}
    (hq : |q| < B.radius) (hq₀ : q ≠ 0)
    (hw : ContDiff ℝ ∞ (stateProfile D S C (B.state q))) : Nonempty FlatAnnularCore :=
  hB.nonempty_flatAnnularCore_of_smooth hN hS hq hq₀ hw
    (physical_height_contDiff_and_flatJets hT hS (by norm_num : (0 : ℝ) < 3 / 4)
      (B.state q).1.1).1

end ContinuousFlexibility.Statements
