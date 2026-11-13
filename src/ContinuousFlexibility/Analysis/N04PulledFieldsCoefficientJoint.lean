import ContinuousFlexibility.Analysis.N04PulledFieldsErrorJoint
import ContinuousFlexibility.Analysis.N04RealizationMixedJointDirections

/-!
# Joint towers of the retained physical coefficients

The original coefficients and the actual correction error are combined
as literal functions before any inverse-chart substitution. This keeps
the whole physical annulus available for every moving chart point.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04PulledFieldsCoefficientJointStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

set_option backward.isDefEq.respectTransparency false

/-- The genuine joint tower is for the retained corrected coefficient,
with the actual N02 residual already substituted. -/
def n04PulledFields_correctedCoefficientJointDirections
    (W : N04RealizationStart) (i : Fin 3) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ annularOpen W.D)
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        canonicalCoefficientComponent i
          (W.L.coefficients (liftSectorParameter W.S W.C x.1)) x.2) := by
  have hU := sectorNeighborhood_isOpen W.S W.base W.ε W.ε
  let RF := n04Realization_annularOriginalMixedRegularity W.through03.1.1 W.hS W.hT i
  let JF := n04Realization_mixedJointDirections RF hU
    (sectorNeighborhood_convex W.S W.base W.ε W.ε) isOpen_Ioo
    (convex_Ioo W.D.a W.D.b)
    (n04Realization_annularOriginalMixed_uniform W.through03.1.1 W.hS W.hT i)
  let JA := n04PulledFields_actualErrorJointDirections W.cutoff W.through03.1.1
    W.hS W.hT W.through03.1.2 (n04PulledFields_errorProjection i)
  let JN := solveSmoothDirectionsPostcomp JA (-ContinuousLinearMap.id ℝ ℝ)
  apply (smoothDirectionsAdd JF JN).congrOn
  intro x hx
  have hz' := liftSectorParameter_mem_stateNeighborhood (C := W.C) hx.1 le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector x.1
  have he := returnCorrectionCoefficientError_at_actual W.through03.1.1
    W.through03.1.2 W.hS W.cutoff.cutoff hz' hs x.2 hx.2
    (fun m hm hd => (W.cutoff.active_discriminant _ hz' hs m x.2 hm hd).le)
  change originalCoefficientEntry W.D W.S W.C i (liftSectorParameter W.S W.C x.1) x.2 +
      -n04PulledFields_errorProjection i
        (returnCorrectionCoefficientError W.D W.S W.C W.R W.cutoff.cutoff
          (liftSectorParameter W.S W.C x.1) x.2
            (W.R.residual (liftSectorParameter W.S W.C x.1))) = _
  rw [he, ← sub_eq_add_neg]
  have hentry : originalCoefficientEntry W.D W.S W.C i
      (liftSectorParameter W.S W.C x.1) x.2 =
    canonicalCoefficientComponent i
      (originalCoefficients W.D W.S W.C (liftSectorParameter W.S W.C x.1)) x.2 := by
    simp only [originalCoefficientEntry, canonicalCoefficientComponent, ite_apply]
  rw [hentry]
  exact n04PulledFields_coefficient_reconstruction i _ _
    (returnCorrectedCoefficients_a W.D W.S W.C W.cutoff.cutoff _) x.2

/-- Auxiliary replacement does not alter the actual physical coefficient
or its joint state/physical tower. -/
def n04PulledFields_gaugeCoefficientJointDirections
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space) (i : Fin 3) :
    SmoothDirections
      (sectorNeighborhood (G.S η) G.W.base G.W.ε G.W.ε ×ˢ annularOpen G.W.D)
      (fun x : CanonicalGeometry.Parameter (G.S η) × PolarPoint =>
        G.coefficientField η i (G.lift η x.1) x.2) :=
  n04PulledFields_correctedCoefficientJointDirections G.W i

end ContinuousFlexibility.Analysis
