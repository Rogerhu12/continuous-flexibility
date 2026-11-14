module

public import ContinuousFlexibility.Analysis.SolveStateSpaces
public import ContinuousFlexibility.Analysis.SolveReturnEquations
public import ContinuousFlexibility.Analysis.SmoothDirectionsAffine

/-!
# Affine sector parameters and their actual seminorms

The inclusion uses the given physical state space. Its pulled-back sum
grading is exactly the sector grading, so restricting a directional
tower preserves the original one-high-factor estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

local instance sectorParameterGeometryStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

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
  apply Prod.ext
  · change (C.referenceState + z.1.val) - C.referenceState = z.1.val
    exact add_sub_cancel_left _ _
  · change z.2 - 0 = z.2
    exact sub_zero _

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
  apply (congrArg
    (fun y : AnnularState S × ℝ =>
      oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
        base high y (fun i => sectorParameterInclusion S (v i)))
    (liftSectorParameter_sub_reference S C z)).trans
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

private theorem convex_pair_seminorm_sublevels
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (p : Seminorm ℝ E) (q : Seminorm ℝ F) (ε q0 : ℝ) :
    Convex ℝ {x : E × F | p x.1 < ε ∧ q x.2 < q0} := by
  intro x hx y hy a b ha hb hab
  have hpx : x.1 ∈ p.ball 0 ε := by
    simpa only [Seminorm.mem_ball_zero] using hx.1
  have hpy : y.1 ∈ p.ball 0 ε := by
    simpa only [Seminorm.mem_ball_zero] using hy.1
  have hqx : x.2 ∈ q.ball 0 q0 := by
    simpa only [Seminorm.mem_ball_zero] using hx.2
  have hqy : y.2 ∈ q.ball 0 q0 := by
    simpa only [Seminorm.mem_ball_zero] using hy.2
  constructor
  · change p (a • x.1 + b • y.1) < ε
    simpa only [Seminorm.mem_ball_zero] using p.convex_ball 0 ε hpx hpy ha hb hab
  · change q (a • x.2 + b • y.2) < q0
    simpa only [Seminorm.mem_ball_zero] using q.convex_ball 0 q0 hqx hqy ha hb hab

theorem sectorNeighborhood_convex (S : PhysicalSpacesData)
    (base : ℕ) (ε q0 : ℝ) : Convex ℝ (sectorNeighborhood S base ε q0) := by
  simpa only [sectorNeighborhood, coe_normSeminorm, Real.norm_eq_abs] using
    convex_pair_seminorm_sublevels (sectorGrading S base) (normSeminorm ℝ ℝ) ε q0

end ContinuousFlexibility.Statements
