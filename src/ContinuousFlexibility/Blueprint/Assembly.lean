import ContinuousFlexibility.Blueprint.S01
import ContinuousFlexibility.Blueprint.S02
import ContinuousFlexibility.Blueprint.R01
import ContinuousFlexibility.Blueprint.R02
import ContinuousFlexibility.Blueprint.R03
import ContinuousFlexibility.Blueprint.R04
import ContinuousFlexibility.Blueprint.W01
import ContinuousFlexibility.Blueprint.ScalarCalculus
import ContinuousFlexibility.Blueprint.ScalarWeighted
import ContinuousFlexibility.Blueprint.Tame
import ContinuousFlexibility.Blueprint.Spaces
import ContinuousFlexibility.Blueprint.R05a
import ContinuousFlexibility.Blueprint.R05b
import ContinuousFlexibility.Blueprint.R06a
import ContinuousFlexibility.Blueprint.R06b
import ContinuousFlexibility.Blueprint.R06c
import ContinuousFlexibility.Blueprint.R07
import ContinuousFlexibility.Blueprint.R08
import ContinuousFlexibility.Blueprint.R09
import ContinuousFlexibility.Blueprint.R10a
import ContinuousFlexibility.Blueprint.R10b
import ContinuousFlexibility.Blueprint.R11a
import ContinuousFlexibility.Blueprint.R11b
import ContinuousFlexibility.Blueprint.R12
import ContinuousFlexibility.Blueprint.N01a
import ContinuousFlexibility.Blueprint.N01b
import ContinuousFlexibility.Blueprint.N01c
import ContinuousFlexibility.Blueprint.N02N03
import ContinuousFlexibility.Blueprint.N04Root
import ContinuousFlexibility.Blueprint.N04Cubic
import ContinuousFlexibility.Blueprint.N04Transmission
import ContinuousFlexibility.Blueprint.N04a
import ContinuousFlexibility.Blueprint.N04b
import ContinuousFlexibility.Blueprint.N04Coordinates
import ContinuousFlexibility.Blueprint.N05
import ContinuousFlexibility.Blueprint.N06
import ContinuousFlexibility.Blueprint.N07a
import ContinuousFlexibility.Blueprint.N07b
import ContinuousFlexibility.Blueprint.N08
import ContinuousFlexibility.Blueprint.N09N10
import ContinuousFlexibility.Blueprint.Solve
import ContinuousFlexibility.Blueprint.N12

/-!
# Blueprint assembly

The blueprint nodes compose to `Nonempty FlatAnnularCore`. This file contains no `sorry`;
the result depends on `sorryAx` exactly through the nodes that are still open.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem S03_of_nodes : S03Statement := ⟨ScalarCalculus.1, ScalarWeighted.1⟩
theorem S04_of_nodes : S04Statement := ⟨ScalarCalculus.2.1, ScalarWeighted.2.1⟩
theorem S05_of_nodes : S05Statement := ⟨ScalarCalculus.2.2, ScalarWeighted.2.2⟩

theorem R05_of_nodes (hA : R05aStatement) (hB : R05bStatement) : R05Statement := by
  intro initial
  obtain ⟨T, hT, C, family, hreal, hind⟩ := hA initial
  obtain ⟨C', hC'⟩ := hB T C family hreal
  exact ⟨T, hT, C', family, hC', hind⟩

theorem R06_of_nodes (hA : R06aStatement) (hB : R06bStatement) (hC : R06cStatement) :
    R06Statement := by
  -- All stages use the same corrected Friedrichs core and distribution tests:
  -- their closed support is compactly contained in the open tail interval.
  -- Ordinary support does not suffice at the degenerate endpoint.
  obtain ⟨C, η, K, h1, h2, h3, h4, hop⟩ := hA
  obtain ⟨C₁, η₁, K₁, h1', h2', h3', h4', hfull⟩ := hB C η K h1 h2 h3 h4 hop
  obtain ⟨C₂, η₂, K₂, g1, g2, g3, g4, hfull', hphys, hcont⟩ := hC C₁ η₁ K₁ h1' h2' h3' h4' hfull
  exact ⟨C₂, η₂, K₂, g1, g2, g3, g4, hfull', hphys, hcont⟩

theorem R10_of_nodes (hA : R10aStatement) (hB : R10bStatement) : R10Statement := by
  obtain ⟨D, hacc, hborder, hpieces⟩ := hA
  refine ⟨D, hacc, hborder, fun j hj he => ?_⟩
  obtain ⟨M, hM, hp⟩ := hpieces j hj he
  exact hB D hacc hborder j hj he M hM hp

theorem N04_of_nodes (hc : N04cStatement) (hroot : RootCompositionTarget)
    (hcubic : CubicDivisionTarget) (htrans : PhysicalTransmissionTarget) : N04Statement := by
  obtain ⟨A, T, S, C, R, L, K, base, loss, ε, h1, h2, h3, h4⟩ := hc
  exact ⟨A, T, S, C, R, L, K, base, loss, ε, h1, h2, h3, hroot, hcubic, htrans, h4⟩

/-- The analytic existence statement, assembled from the blueprint nodes. -/
theorem flatAnnularCore_nonempty : Nonempty FlatAnnularCore := by
  have hS03 : S03Statement := S03_of_nodes
  have hS04 : S04Statement := S04_of_nodes
  have hS05 : S05Statement := S05_of_nodes
  have hR03 : R03Statement := R03 (R02 R01)
  have hR04 : R04Statement := R04 (R02 R01)
  have hTame : H01Statement ∧ H02Statement := Tame
  have hR05 : R05Statement := R05_of_nodes (R05a hR04) R05b
  have hR06 : R06Statement := R06_of_nodes R06a R06b R06c
  have hR07 : R07Statement := R07 hR04 hR05 hR06
  have hR08 : R08Statement := R08 hR03 hR07
  have hR09 : R09Statement := R09
  have hR10 : R10Statement := R10_of_nodes (R10a hR06 hR07 hR08 hR09) R10b
  have hR11 : R11Statement := R11b (R11a hR05 hR10)
  have hR12 : R12Statement := R12 hR06 hR08 hR10 hR11
  have hW01 : W01Statement := W01
  have hSpaces : W02Statement ∧ W03Statement := Spaces hW01 hTame
  -- Retain the strict support certificates through the reference/control
  -- construction and the common-neighbourhood flow construction.
  have hN01a : N01aStatement := N01a hR12 hW01 hSpaces.1
  have hN01b : N01bStatement := N01b hN01a hS05
  have hN01 : N01Statement := N01c hN01b
  have hN03 : N03Statement := N02N03 hN01 hS05
  have hN04 : N04Statement := N04_of_nodes (N04Coordinates (N04b (N04a hN03))) N04Root N04Cubic N04Transmission
  have hN05 : N05Statement := N05 hN04
  have hN06 : N06Statement := N06 hN05
  have hN07 : N07Statement := N07b (N07a hN06 hTame)
  have hN08 : N08Statement := N08 hN07 hS04
  have hN10 : N10Statement := N09N10 hN08 hTame
  have hBranch : PointBranchStatement := Solve hN10 hTame
  exact N12 hBranch hSpaces.2 hS03

end ContinuousFlexibility.Blueprint
