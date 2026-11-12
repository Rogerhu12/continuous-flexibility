import ContinuousFlexibility.Analysis.N07aPerturbedCanonicalEquation
import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# The current distribution equation from the primitive geometry

All coefficient witnesses below are the actual principal functions and
scalar columns supplied by the raw geometric jet bounds. The equation
itself comes from the physical relation and the exact change of variables.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

def n07aCurrentCanonicalRhs
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.left m < K.right m)
    (U : CanonicalUnknown S K) (F : CanonicalSequence S K) : CanonicalL2 S K m :=
  let q := N07aCanonicalOpenCoefficient.constMul
    (if K.positive m then -1 else (1 : ℝ)) (n07aCurrentOpenCoefficient href hcur z hz m hm 4)
  let col := n07aCurrentScalarOpenCoefficient href hcur z hz m hm
  F m - q.mul (U.1 m) - U.2.1 • (col 0).toLp -
    U.2.2.1 • (col 1).toLp - U.2.2.2 • (col 2).toLp

theorem n07a_currentCanonical_distribution
    (hab : D.a ≤ D.b) (hS : IsPhysicalSpaces D T S)
    (hrefState : referenceStateConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.left m < K.right m)
    {U : CanonicalUnknown S K} {F : CanonicalSequence S K}
    (hrel : PerturbedCanonicalRelation D S C K L (liftSectorParameter S C z) U F) :
    N07aCanonicalDistributionEquation S K m (K.coefficients (liftSectorParameter S C z) m)
      (U.1 m) (n07aCurrentCanonicalRhs href hcur z hz m hm U F) := by
  exact n07a_perturbedCanonical_distribution_of_coefficients hab h04
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (hrefState.liftSectorParameter_sector z) hS.2.2.1.1 hrel
    (n07aCurrentOpenCoefficient href hcur z hz m hm 0)
    (n07aCurrentOpenCoefficient href hcur z hz m hm 1)
    (n07aCurrentOpenCoefficient href hcur z hz m hm 2)
    (N07aCanonicalOpenCoefficient.constMul (if K.positive m then -1 else (1 : ℝ))
      (n07aCurrentOpenCoefficient href hcur z hz m hm 4))
    (n07aCurrentScalarOpenCoefficient href hcur z hz m hm)
    rfl rfl rfl rfl (fun _ => rfl)

theorem n07a_currentOperator_distribution
    {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
    {P : RelativeInverseData S K V b B}
    (hab : D.a ≤ D.b) (hS : IsPhysicalSpaces D T S)
    (hrefState : referenceStateConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (h06 : N06Properties D S C K L V b B P base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.left m < K.right m) (u : B.Space) :
    N07aCanonicalDistributionEquation S K m (K.coefficients (liftSectorParameter S C z) m)
      (u.val.1.1 m) (n07aCurrentCanonicalRhs href hcur z hz m hm u.val.1
        (V.forget (3 / 4 : ℝ) 0 b (P.operator (liftSectorParameter S C z) u))) := by
  exact n07a_currentCanonical_distribution hab hS hrefState h04 href hcur z hz m hm
    ((h06.2 _ (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hrefState.liftSectorParameter_sector z)).1 u)

end ContinuousFlexibility.Analysis
