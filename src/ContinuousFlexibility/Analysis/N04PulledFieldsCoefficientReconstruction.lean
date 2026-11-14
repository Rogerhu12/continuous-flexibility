module

public import ContinuousFlexibility.Analysis.N04PulledFieldsCoefficientRegularity

/-!
# Reconstruction of the actual physical coefficients

The retained coefficient is exactly the original coefficient minus
its actual residual-substituted correction error, at the same point.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

local instance n04PulledFieldsCoefficientReconstructionStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

set_option backward.isDefEq.respectTransparency false

/-- The retained physical coefficient is reconstructed from the actual
original field and the actual N02 residual-substituted error. -/
theorem n04PulledFields_startCoefficient_sub_error
    (W : N04RealizationStart) (i : Fin 3)
    (z : StateDirections W.S × ℝ) (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    (y : PolarPoint) (hy : y ∈ annularOpen W.D) :
    canonicalCoefficientComponent i (W.L.coefficients (liftSectorParameter W.S W.C z)) y =
      originalCoefficientEntry W.D W.S W.C i (liftSectorParameter W.S W.C z) y -
        n04PulledFields_errorProjection i
          (returnCorrectionCoefficientError W.D W.S W.C W.R W.cutoff.cutoff
            (liftSectorParameter W.S W.C z) y
              (W.R.residual (liftSectorParameter W.S W.C z))) := by
  have hz' := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have he := returnCorrectionCoefficientError_at_actual W.through03.1.1
    W.through03.1.2 W.hS W.cutoff.cutoff hz' hs y hy
    (fun m hm hd => (W.cutoff.active_discriminant _ hz' hs m y hm hd).le)
  rw [he]
  have hentry : originalCoefficientEntry W.D W.S W.C i
      (liftSectorParameter W.S W.C z) y =
      canonicalCoefficientComponent i
        (originalCoefficients W.D W.S W.C (liftSectorParameter W.S W.C z)) y := by
    simp only [originalCoefficientEntry, canonicalCoefficientComponent, ite_apply]
  rw [hentry]
  exact (n04PulledFields_coefficient_reconstruction i _ _
    (returnCorrectedCoefficients_a W.D W.S W.C W.cutoff.cutoff _) y).symm

end ContinuousFlexibility.Analysis
