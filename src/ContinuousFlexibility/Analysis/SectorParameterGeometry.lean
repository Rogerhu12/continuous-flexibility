import ContinuousFlexibility.Analysis.SolveStateSpaces
import ContinuousFlexibility.Analysis.SolveReturnEquations
import ContinuousFlexibility.Analysis.SmoothDirectionsAffine

/-!
# Affine sector parameters and their actual seminorms

The inclusion uses the given physical state space. Its pulled-back sum
grading is exactly the sector grading, so restricting a directional
tower preserves the original one-high-factor estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped Topology BigOperators

def sectorParameterInclusion (S : PhysicalSpacesData) :
    (StateDirections S × ℝ) →L[ℝ] (AnnularState S × ℝ) :=
  (stateSectorSubmodule S).subtypeL.prodMap (ContinuousLinearMap.id ℝ ℝ)

theorem sectorParameterInclusion_apply (S : PhysicalSpacesData)
    (z : StateDirections S × ℝ) : sectorParameterInclusion S z = (z.1.val, z.2) := rfl

theorem liftSectorParameter_eq_affine (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : StateDirections S × ℝ) :
    liftSectorParameter S C z = (C.referenceState, 0) + sectorParameterInclusion S z := by
  apply Prod.ext
  · rfl
  · exact (zero_add z.2).symm

theorem liftSectorParameter_sub_reference (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : StateDirections S × ℝ) :
    liftSectorParameter S C z - (C.referenceState, 0) = sectorParameterInclusion S z := by
  rw [liftSectorParameter_eq_affine, add_sub_cancel_left]

theorem pairGrading_sectorParameterInclusion (S : PhysicalSpacesData)
    (n : ℕ) (z : StateDirections S × ℝ) :
    pairGrading (stateGrading S) realGrading n (sectorParameterInclusion S z) =
      pairGrading (sectorGrading S) realGrading n z := rfl

theorem oneHighVariationWeight_sector_lift (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base high : ℕ) {k : ℕ}
    (z : StateDirections S × ℝ) (v : Fin k → (StateDirections S × ℝ)) :
    oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
      base high (liftSectorParameter S C z - (C.referenceState, 0))
      (fun i => sectorParameterInclusion S (v i)) =
    oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
      base high z v := by
  rw [liftSectorParameter_sub_reference]
  simp only [oneHighVariationWeight, pairGrading_sectorParameterInclusion]

theorem sectorPairGrading_continuous (S : PhysicalSpacesData) (n : ℕ) :
    Continuous (pairGrading (sectorGrading S) realGrading n) := by
  change Continuous (fun z : StateDirections S × ℝ => sectorGrading S n z.1 + ‖z.2‖)
  exact (((solve_sectorGrading_withSeminorms S).continuous_seminorm n).comp
    continuous_fst).add continuous_snd.norm

theorem sectorPairGrading_monotone (S : PhysicalSpacesData) :
    Monotone (pairGrading (sectorGrading S) realGrading) :=
  pairGrading_monotone (solve_sectorGrading_monotone S) (fun _ _ _ _ => le_rfl)

theorem sectorNeighborhood_isOpen (S : PhysicalSpacesData)
    (base : ℕ) (ε q0 : ℝ) : IsOpen (sectorNeighborhood S base ε q0) :=
  (isOpen_lt (((solve_sectorGrading_withSeminorms S).continuous_seminorm base).comp
    continuous_fst) continuous_const).inter
    (isOpen_lt continuous_snd.abs continuous_const)

theorem sectorNeighborhood_convex (S : PhysicalSpacesData)
    (base : ℕ) (ε q0 : ℝ) : Convex ℝ (sectorNeighborhood S base ε q0) := by
  let p : Seminorm ℝ (StateDirections S × ℝ) :=
    (sectorGrading S base).comp (LinearMap.fst ℝ (StateDirections S) ℝ)
  let q : Seminorm ℝ (StateDirections S × ℝ) :=
    (normSeminorm ℝ ℝ).comp (LinearMap.snd ℝ (StateDirections S) ℝ)
  have hp := p.convex_ball 0 ε
  have hq := q.convex_ball 0 q0
  simpa only [Seminorm.ball_zero_eq, p, q, Seminorm.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, coe_normSeminorm, Real.norm_eq_abs, sectorNeighborhood]
    using hp.inter hq

end ContinuousFlexibility.Statements
