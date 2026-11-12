import ContinuousFlexibility.Analysis.N08WeakControlMaterialJets
import ContinuousFlexibility.Analysis.N08RadialFamilyHeightBounds

/-! # Actual weighted height membership and norms of weak control profiles -/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ENNReal ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n08WeakControlField_weightedJet_L2_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (a b c : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ControlBanach,
      MemLp (weightedPhysicalJet T n08WeakControlWeight a b c (n08WeakControlField T C u))
        2 materialCylinderMeasure ∧
      (eLpNorm (weightedPhysicalJet T n08WeakControlWeight a b c (n08WeakControlField T C u))
        2 materialCylinderMeasure).toReal ≤ K * ‖u‖ :=
  n08RadialFamilyField_weightedJet_L2_bound hT
    (fun u => n08WeakControlProfile_contDiffOn hN.2.2.2.1 u)
    (n08WeakControlProfile_jet_bound hT hS hN) a b c

theorem n08WeakControlField_heightMember
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (u : ControlBanach) :
    HeightMember D T n08WeakControlWeight (n08WeakControlField T C u) :=
  n08RadialFamilyField_heightMember hT
    (fun u => n08WeakControlProfile_contDiffOn hN.2.2.2.1 u)
    (n08WeakControlProfile_jet_bound hT hS hN)
    (fun u _ hr => n08ControlSeries_zero_off_core hN.2.2.2.1 _ hr) u

theorem n08WeakControlField_physicalNorm_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ControlBanach,
      physicalNorm T n08WeakControlWeight s (n08WeakControlField T C u) ≤ K * ‖u‖ :=
  n08RadialFamilyField_physicalNorm_bound hT
    (fun u => n08WeakControlProfile_contDiffOn hN.2.2.2.1 u)
    (n08WeakControlProfile_jet_bound hT hS hN) s

end ContinuousFlexibility.Statements
