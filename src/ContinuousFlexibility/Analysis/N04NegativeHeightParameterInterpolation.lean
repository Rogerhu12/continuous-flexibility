import ContinuousFlexibility.Analysis.SectorParameterGeometry
import ContinuousFlexibility.Analysis.TameSmoothingCalculus

/-! The actual sector smoothing family supplies interpolation for the
parameter grading used by the negative-height calculation. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements CanonicalGeometry

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

theorem n04NegativeHeight_parameterInterpolation
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) : HasInterpolation (parameterGrading S) :=
  hasInterpolation_of_hasSmoothing (sectorPairGrading_monotone S)
    (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading)

end ContinuousFlexibility.Analysis
