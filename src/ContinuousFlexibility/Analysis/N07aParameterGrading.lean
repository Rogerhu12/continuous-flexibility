import ContinuousFlexibility.Analysis.N07aNormalizedSpaces

/-!
# Gradings of the normalized scalar-inverse parameters

The sector parameter and its two evaluation products use the exact sum
gradings in the frozen scalar-inverse target. Naming them keeps later
operator statements from repeatedly elaborating the nested state kernel.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

-- `Seminorm` asks for these smaller structures directly. Retain their
-- inherited instances instead of searching through every nested lp layer.
local instance (S : PhysicalSpacesData) : AddGroup (StateDirections S) :=
  (Submodule.addCommGroup (stateSectorSubmodule S)).toAddGroup

local instance (S : PhysicalSpacesData) : SMul ℝ (StateDirections S) :=
  (Submodule.module (stateSectorSubmodule S)).toSMul

/-- The sector state variation together with the scalar equation parameter. -/
def n07aParameterGrading (S : PhysicalSpacesData) :
    ℕ → Seminorm ℝ (StateDirections S × ℝ) :=
  pairGrading (E := StateDirections S) (F := ℝ) (sectorGrading S) realGrading

theorem n07aParameterGrading_monotone (S : PhysicalSpacesData) :
    Monotone (n07aParameterGrading S) :=
  tamePairGrading_monotone (solve_sectorGrading_monotone S)
    weighted_realGrading_monotone

theorem n07aParameterGrading_withSeminorms (S : PhysicalSpacesData) :
    WithSeminorms (n07aParameterGrading S) :=
  withSeminorms_pairGrading (solve_sectorGrading_withSeminorms S)
    weighted_realGrading_withSeminorms

/-- The parameter and height variation grading in the forward evaluation. -/
def n07aParameterHeightGrading (S : PhysicalSpacesData) :
    ℕ → Seminorm ℝ ((StateDirections S × ℝ) × HeightPair S) :=
  pairGrading (E := StateDirections S × ℝ) (F := HeightPair S)
    (n07aParameterGrading S) (heightPairGrading S)

/-- The parameter and source grading in the actual inverse evaluation. -/
def n07aParameterSourceGrading (S : PhysicalSpacesData) :
    ℕ → Seminorm ℝ ((StateDirections S × ℝ) × S.Source) :=
  pairGrading (E := StateDirections S × ℝ) (F := S.Source)
    (n07aParameterGrading S) S.sourceGrading

/-- The parameter and normalized height grading in the forward evaluation. -/
def n07aParameterNormalizedGrading
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hD : IsRadialReference D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) :
    ℕ → Seminorm ℝ ((StateDirections S × ℝ) × N07aNormalizedUnknown hD hT hS) :=
  pairGrading (E := StateDirections S × ℝ) (F := N07aNormalizedUnknown hD hT hS)
    (n07aParameterGrading S) (n07aNormalizedGrading hD hT hS)

end ContinuousFlexibility.Analysis
