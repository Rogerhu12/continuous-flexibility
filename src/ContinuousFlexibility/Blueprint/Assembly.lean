import ContinuousFlexibility.Blueprint.S01
import ContinuousFlexibility.Blueprint.S02
import ContinuousFlexibility.Blueprint.R01
import ContinuousFlexibility.Blueprint.S03
import ContinuousFlexibility.Blueprint.S04
import ContinuousFlexibility.Blueprint.S05
import ContinuousFlexibility.Blueprint.R02
import ContinuousFlexibility.Blueprint.R03
import ContinuousFlexibility.Blueprint.R04
import ContinuousFlexibility.Blueprint.R05
import ContinuousFlexibility.Blueprint.R06
import ContinuousFlexibility.Blueprint.R07
import ContinuousFlexibility.Blueprint.R08
import ContinuousFlexibility.Blueprint.R09
import ContinuousFlexibility.Blueprint.R10
import ContinuousFlexibility.Blueprint.R11
import ContinuousFlexibility.Blueprint.R12
import ContinuousFlexibility.Blueprint.W01
import ContinuousFlexibility.Blueprint.H01
import ContinuousFlexibility.Blueprint.W02
import ContinuousFlexibility.Blueprint.W03
import ContinuousFlexibility.Blueprint.N01
import ContinuousFlexibility.Blueprint.N02
import ContinuousFlexibility.Blueprint.N03
import ContinuousFlexibility.Blueprint.N04
import ContinuousFlexibility.Blueprint.N05
import ContinuousFlexibility.Blueprint.N06
import ContinuousFlexibility.Blueprint.H02
import ContinuousFlexibility.Blueprint.N07
import ContinuousFlexibility.Blueprint.N08
import ContinuousFlexibility.Blueprint.N09
import ContinuousFlexibility.Blueprint.N10
import ContinuousFlexibility.Blueprint.H03
import ContinuousFlexibility.Blueprint.N11
import ContinuousFlexibility.Blueprint.N12

/-!
# Blueprint assembly

The blueprint nodes compose to `Nonempty FlatAnnularCore`. This file contains no
`sorry`; the result depends on `sorryAx` exactly through the nodes that are still open.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

/-- The analytic existence statement, assembled from the blueprint nodes. -/
theorem flatAnnularCore_nonempty : Nonempty FlatAnnularCore := by
  have hS01 : S01Statement := S01
  have hS02 : S02Statement := S02
  have hR01 : R01Statement := R01
  have hS03 : S03Statement := S03 hS01 hS02
  have hS04 : S04Statement := S04 hS03
  have hS05 : S05Statement := S05 hS02 hS03 hS04
  have hR02 : R02Statement := R02 hR01
  have hR03 : R03Statement := R03 hR02
  have hR04 : R04Statement := R04 hR02
  have hR05 : R05Statement := R05 hR04 hR01
  have hR06 : R06Statement := R06 hR01 hR05
  have hR07 : R07Statement := R07 hR04 hR05 hR06
  have hR08 : R08Statement := R08 hR03 hR07
  have hR09 : R09Statement := R09 hR03 hR04
  have hR10 : R10Statement := R10 hR06 hR07 hR08 hR09
  have hR11 : R11Statement := R11 hR05 hR10
  have hR12 : R12Statement := R12 hR06 hR08 hR10 hR11
  have hW01 : W01Statement := W01 hR05
  have hH01 : H01Statement := H01
  have hW02 : W02Statement := W02 hW01 hH01
  have hW03 : W03Statement := W03 hW01 hW02
  have hN01 : N01Statement := N01 hR12 hW01 hW02 hS05
  have hN02 : N02Statement := N02 hR12 hN01 hW02
  have hN03 : N03Statement := N03 hN01 hN02 hW02 hS05
  have hN04 : N04Statement := N04 hN01 hN03 hW01 hW02
  have hN05 : N05Statement := N05 hR12 hN04 hW02
  have hN06 : N06Statement := N06 hN01 hN04 hN05 hW01
  have hH02 : H02Statement := H02 hH01
  have hN07 : N07Statement := N07 hN05 hN06 hH02 hW02
  have hN08 : N08Statement := N08 hS04 hN01 hN02 hN07 hW02
  have hN09 : N09Statement := N09 hN02 hN07 hN08 hH02
  have hN10 : N10Statement := N10 hN03 hN08 hN09 hS05 hW02
  have hH03 : H03Statement := H03 hH01
  have hN11 : N11Statement := N11 hH03 hN08 hN09 hN10
  have hN12 : N12Statement := N12 hN11 hW03 hN01 hR12 hS03
  exact hN12

end ContinuousFlexibility.Blueprint
