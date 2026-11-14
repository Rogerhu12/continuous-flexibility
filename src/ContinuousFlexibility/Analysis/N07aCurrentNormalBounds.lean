module

public import ContinuousFlexibility.Analysis.N07aPrincipalJetBounds
public import ContinuousFlexibility.Analysis.N07aSampleJetAlgebra
public import ContinuousFlexibility.Analysis.N07aCurrentQualitativeRegularity
public import ContinuousFlexibility.Analysis.SolveStateSpaces

/-!
# The six actual normal coefficients have one fixed loss

The coefficients in the exact weak-to-classical normal equation are
identified with the same principal functions used by the raw geometry.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

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

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}

theorem n07a_currentNormalCoefficients_sampleJetBounds
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hinterval : ∀ m, K.left m < K.right m) :
    ∃ low loss : ℕ, ∀ i : Fin 6,
      N07aSampleJetBounds T K (CanonicalGeometry.parameterGrading S)
        {z | z ∈ sectorNeighborhood S base ε ε ∧
          CanonicalGeometry.parameterGrading S low z ≤ 1}
        (canonicalOpen S K) loss
        (n07aNormalCoefficientFamily
          (fun k z m => n07aPrincipalField K (liftSectorParameter S C z) m k)
          (fun m => if K.positive m then -1 else 1) i) := by
  have h := n07a_principalFields_sampleJetBounds hD hT href hcur hinterval
  let d := h.choose
  have hb := h.choose_spec
  have hp : Monotone (CanonicalGeometry.parameterGrading S) :=
    n07aParameterGrading_monotone S
  have hIp : HasSmoothing (CanonicalGeometry.parameterGrading S) :=
    hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading
  exact n07a_normalCoefficientFamily_sampleJetBounds hD hT
    (CanonicalGeometry.parameterGrading S) hp hIp (sectorNeighborhood S base ε ε)
    (canonicalOpen S K) (fun _ => isOpen_Ioo.prod isOpen_univ) d
    (fun k z m => n07aPrincipalField K (liftSectorParameter S C z) m k) hb
    (fun k z hz m => (n07aCurrentOpenCoefficient href hcur z hz m (hinterval m) k).smooth)
    (fun m => if K.positive m then -1 else 1)
    (fun m => by split <;> norm_num)

end ContinuousFlexibility.Analysis
