import ContinuousFlexibility.Statements.Scalar
import ContinuousFlexibility.Statements.ScalarWeighted
import ContinuousFlexibility.Statements.FiniteFourier
import ContinuousFlexibility.Statements.RadialTargets
import ContinuousFlexibility.Statements.Analysis
import ContinuousFlexibility.Statements.Nonlinear
import ContinuousFlexibility.Statements.NonlinearCompletion
import ContinuousFlexibility.Statements.MainGeometry

/-!
# Exhaustive typed registry of the 58 blueprint milestone goals

Every entry reduces to an explicit closed proposition. This registry asserts
no milestone proposition: constructing its type is separate from proving it.
MAIN has no analytic input and expands to `Nonempty ClosedBending`.
-/

namespace ContinuousFlexibility.Statements

inductive Milestone where
  | C00
  | S01
  | S02
  | R01
  | S03
  | S04
  | S05
  | R02
  | R03
  | R04
  | R05
  | R06
  | R07
  | R08
  | R09
  | R10
  | R11
  | R12
  | W01
  | H01
  | W02
  | W03
  | N01
  | N02
  | N03
  | N04
  | N05
  | N06
  | H02
  | N07
  | N08
  | N09
  | N10
  | H03
  | N11
  | N12
  | D01
  | D02
  | G01
  | G02
  | G03
  | G04
  | G05
  | G06
  | G07
  | G08
  | G09
  | G10
  | G11
  | G12
  | G13
  | G14
  | G15
  | G16
  | MAIN
  | X01
  | X02
  | X03
  deriving DecidableEq, Repr

/-- The actual proposition to be proved at each blueprint milestone. -/
def Milestone.statement : Milestone → Prop
  | .C00 => C00Statement
  | .S01 => S01Statement
  | .S02 => S02Statement
  | .R01 => R01Statement
  | .S03 => S03Statement
  | .S04 => S04Statement
  | .S05 => S05Statement
  | .R02 => R02Statement
  | .R03 => R03Statement
  | .R04 => R04Statement
  | .R05 => R05Statement
  | .R06 => R06Statement
  | .R07 => R07Statement
  | .R08 => R08Statement
  | .R09 => R09Statement
  | .R10 => R10Statement
  | .R11 => R11Statement
  | .R12 => R12Statement
  | .W01 => W01Statement
  | .H01 => H01Statement
  | .W02 => W02Statement
  | .W03 => W03Statement
  | .N01 => N01Statement
  | .N02 => N02Statement
  | .N03 => N03Statement
  | .N04 => N04Statement
  | .N05 => N05Statement
  | .N06 => N06Statement
  | .H02 => H02Statement
  | .N07 => N07Statement
  | .N08 => N08Statement
  | .N09 => N09Statement
  | .N10 => N10Statement
  | .H03 => H03Statement
  | .N11 => N11Statement
  | .N12 => N12Statement
  | .D01 => D01Statement
  | .D02 => D02Statement
  | .G01 => G01Statement
  | .G02 => G02Statement
  | .G03 => G03Statement
  | .G04 => G04Statement
  | .G05 => G05Statement
  | .G06 => G06Statement
  | .G07 => G07Statement
  | .G08 => G08Statement
  | .G09 => G09Statement
  | .G10 => G10Statement
  | .G11 => G11Statement
  | .G12 => G12Statement
  | .G13 => G13Statement
  | .G14 => G14Statement
  | .G15 => G15Statement
  | .G16 => G16Statement
  | .MAIN => MAINStatement
  | .X01 => X01Statement
  | .X02 => X02Statement
  | .X03 => X03Statement

/-- Explicit enumeration for machine checks and downstream proof planning. -/
def Milestone.all : List Milestone :=
  [.C00, .S01, .S02, .R01, .S03, .S04, .S05, .R02, .R03, .R04, .R05, .R06, .R07, .R08, .R09, .R10, .R11, .R12, .W01, .H01, .W02, .W03, .N01, .N02, .N03, .N04, .N05, .N06, .H02, .N07, .N08, .N09, .N10, .H03, .N11, .N12, .D01, .D02, .G01, .G02, .G03, .G04, .G05, .G06, .G07, .G08, .G09, .G10, .G11, .G12, .G13, .G14, .G15, .G16, .MAIN, .X01, .X02, .X03]

end ContinuousFlexibility.Statements

