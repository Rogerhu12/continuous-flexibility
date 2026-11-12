import ContinuousFlexibility.Analysis.N08WeakControlProfile
import ContinuousFlexibility.Analysis.N08RadialFamilyMaterialJets

/-! # The generic material-jet estimates for the actual weak control series -/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n08WeakControlField_weightedJet_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (a b c : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ControlBanach, ∀ p : PolarPoint,
      |weightedPhysicalJet T n08WeakControlWeight a b c (n08WeakControlField T C u) p| ≤
        K * ‖u‖ * T.H (T.radius p.1) ^ (n08WeakControlWeight / 2) :=
  n08RadialFamilyField_weightedJet_bound hT
    (fun u => n08WeakControlProfile_contDiffOn hN.2.2.2.1 u)
    (n08WeakControlProfile_jet_bound hT hS hN) a b c

end ContinuousFlexibility.Statements
