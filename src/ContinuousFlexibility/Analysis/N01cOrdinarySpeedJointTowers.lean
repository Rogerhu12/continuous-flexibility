module

public import ContinuousFlexibility.Analysis.N01cActualCosineSpeedTower
public import ContinuousFlexibility.Analysis.N01cEndpointRadialJointTowers

/-!
# Actual physical radial speed towers

The already constructed whole-speed regularity and distributed raw
bounds yield genuine joint state-angle towers for every radial order at
every interior physical radius, on exactly the same state neighbourhood.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

/-- Joint state-angle towers of all actual physical radial speed jets. -/
abbrev OrdinarySpeedRadialTowers
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (U : Set (AnnularState S × ℝ)) :=
  ∀ m a : ℕ, ∀ r : ℝ, r ∈ Ioo (C.left m) (C.right m) →
    SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun y : (AnnularState S × ℝ) × ℝ =>
        mixedDerivative a 0 (minusCharacteristicSpeed (originalCoefficients D S C y.1))
          (r, y.2))

/-- This is the actual ordinary speed, not a substitute joint family.
The record input is the previously proved whole-speed raw control. -/
def minusCharacteristicSpeed_radialJointSmoothDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε2 : ε ≤ 1 / 2)
    (hB : N01PartB D S C base ε)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hpos : ∀ z ∈ stateNeighborhood S C base ε, ∀ m r,
      r ∈ Icc (C.left m) (C.right m) →
        0 < twoRootDivided (componentOpticalSquare D S C m z)
          (C.left m) (C.right m) r)
    (F : EndpointPowerControl (pairGrading (stateGrading S) realGrading)
      (C.referenceState, 0) base loss (stateNeighborhood S C base ε)
      (fun m => Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
      (fun m q => min (q.1 - C.left m) (C.right m - q.1))
      (fun m _ => T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ))
      (fun m _ => T.E0 (T.sample (C.cell m)))
      (fun _ z => minusCharacteristicSpeed (originalCoefficients D S C z))) :
    OrdinarySpeedRadialTowers D S C (stateNeighborhood S C base ε) := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  intro m a r hr
  have hs := materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell m)
  exact jointSmoothDirections_of_endpointRadialJet
    (X := AnnularState S × ℝ) (ι := ℕ)
    (pairGrading (stateGrading S) realGrading) (jointStateGrading_monotone S)
    (n01c_continuous_jointStateGrading S) (C.referenceState, 0) base loss
    (isOpen_stateNeighborhood S C base ε) (n01c_convex_stateNeighborhood S C base ε)
    (fun z hz => (jointStateGrading_displacement_lt_one hε2 hz).le)
    (fun i => Ioo (C.left i) (C.right i))
    (fun i u => min (u - C.left i) (C.right i - u))
    (fun i => T.H (T.sample (C.cell i)) ^ (3 / 4 : ℝ))
    (fun i => T.E0 (T.sample (C.cell i)))
    (fun _ z => minusCharacteristicSpeed (originalCoefficients D S C z))
    F.bounds m isOpen_Ioo (F.regular m) a r hr
    (lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)) (hE _ hs)
    (minusCharacteristicSpeed_radialJet_finiteAffine hS hT hA hB hpos m a r hr)

end ContinuousFlexibility.Statements
