import ContinuousFlexibility.Analysis.N04PulledFieldsPhysicalDifferenceAlgebra
import ContinuousFlexibility.Analysis.N04PulledFieldsReferenceCoefficients
import ContinuousFlexibility.Analysis.N04PulledFieldsCoefficientReconstruction

/-!
# The actual coefficient difference in arbitrary genuine towers

The retained corrected coefficient is the original coefficient minus
the actual residual-substituted correction. At the reference the
correction vanishes. Both identities are transported through the
genuine mixed parameter towers on any smaller parameter neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

local instance n04PulledFieldsCoefficientDifferenceStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

set_option backward.isDefEq.respectTransparency false

/-- Subtracting the actual reference leaves the original reference
difference minus the full actual correction jet, at every order. -/
theorem n04PulledFields_startCoefficient_differenceJet
    (W : N04RealizationStart) (i : Fin 3)
    {U : Set (StateDirections W.S × ℝ)}
    (hsub : U ⊆ sectorNeighborhood W.S W.base W.ε W.ε)
    (RC : MixedJetRegularity U (annularOpen W.D)
      (fun z => canonicalCoefficientComponent i
        (W.L.coefficients (liftSectorParameter W.S W.C z))))
    (RO : MixedJetRegularity U (annularOpen W.D)
      (fun z => originalCoefficientEntry W.D W.S W.C i (liftSectorParameter W.S W.C z)))
    (RA : MixedJetRegularity U (annularOpen W.D)
      (fun z y => n04PulledFields_errorProjection i
        (returnCorrectionCoefficientError W.D W.S W.C W.R W.cutoff.cutoff
          (liftSectorParameter W.S W.C z) y
            (W.R.residual (liftSectorParameter W.S W.C z)))))
    (k a b : ℕ) (z : StateDirections W.S × ℝ) (hz : z ∈ U)
    (y : PolarPoint) (hy : y ∈ annularOpen W.D) (v : Fin k → StateDirections W.S × ℝ) :
    (RC.parameter a b y hy).D k z v -
        (if k = 0 then mixedDerivative a b
          (canonicalCoefficientComponent i (W.L.coefficients (W.C.referenceState, 0))) y else 0) =
      ((RO.parameter a b y hy).D k z v -
        (if k = 0 then mixedDerivative a b
          (originalCoefficientEntry W.D W.S W.C i (W.C.referenceState, 0)) y else 0)) -
        (RA.parameter a b y hy).D k z v := by
  have hjet := n04PulledFields_mixedSubtraction_jet
    (isOpen_Ioo.prod isOpen_univ) RC RO RA
    (fun x hx p hp => n04PulledFields_startCoefficient_sub_error W i x (hsub hx) p hp)
    k a b z hz y hy v
  have href := mixedDerivative_congr_on_open (isOpen_Ioo.prod isOpen_univ)
    (n04PulledFields_correctedCoefficient_reference_eq W i) a b hy
  rw [hjet, href]
  ring

end ContinuousFlexibility.Analysis
