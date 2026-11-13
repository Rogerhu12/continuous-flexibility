import ContinuousFlexibility.Analysis.N04NegativeChartInteriorTowers
import ContinuousFlexibility.Analysis.N04NegativeChartFirstIntegralRecurrence
import ContinuousFlexibility.Analysis.N01ReturnTransportRecurrences
import ContinuousFlexibility.Analysis.N07aReferenceReturn

/-! The literal full-component towers satisfy the three radial recurrences. -/

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

variable (W : N04RealizationStart)

private abbrev transportDomain : Set (Parameter W.S) :=
  sectorNeighborhood W.S W.base W.ε W.ε

private abbrev componentDomain (m : ℕ) : Set PolarPoint :=
  Ioo (W.C.left m) (W.C.right m) ×ˢ univ

private theorem transportDomain_open : IsOpen W.transportDomain :=
  sectorNeighborhood_isOpen W.S W.base W.ε W.ε

private theorem componentDomain_open (m : ℕ) : IsOpen (W.componentDomain m) :=
  isOpen_Ioo.prod isOpen_univ

private theorem transportDomain_convex (m : ℕ) :
    Convex ℝ (W.transportDomain ×ˢ W.componentDomain m) :=
  (sectorNeighborhood_convex W.S W.base W.ε W.ε).prod
    ((convex_Ioo _ _).prod (convex_univ : Convex ℝ (univ : Set ℝ)))

def negativeCutoffDerivativeJointTower (m : ℕ) :
    SmoothDirections (W.transportDomain ×ˢ W.componentDomain m)
      (fun x : Parameter W.S × PolarPoint => deriv (W.cutoff.cutoff m) x.2.1) := by
  let L : (Parameter W.S × PolarPoint) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ (Parameter W.S) PolarPoint)
  have hd : ContDiff ℝ ∞ (deriv (W.cutoff.cutoff m)) :=
    (contDiff_infty_iff_deriv.mp (W.cutoff.cutoff_smooth m)).2
  exact (smoothDirectionsOfContDiffOn isOpen_univ hd.contDiffOn).compLinear L
    (W.transportDomain_open.prod (W.componentDomain_open m)) (fun _ _ => mem_univ _)

def negativeRawReferenceJointTower (m : ℕ) :
    SmoothDirections (W.transportDomain ×ˢ W.componentDomain m)
      (fun x : Parameter W.S × PolarPoint =>
        minusCharacteristicSpeed (originalCoefficients W.D W.S W.C
          (W.C.referenceState, 0)) x.2) := by
  let P : (Parameter W.S × PolarPoint) →L[ℝ] Parameter W.S × PolarPoint :=
    (0 : (Parameter W.S × PolarPoint) →L[ℝ] Parameter W.S).prod
      (ContinuousLinearMap.snd ℝ (Parameter W.S) PolarPoint)
  have hzero : (0 : Parameter W.S) ∈ W.transportDomain :=
    ⟨(sectorGrading W.S W.base).map_zero'.trans_lt W.ε_pos,
      (abs_zero : |(0 : ℝ)| = 0).trans_lt W.ε_pos⟩
  apply ((W.negativeOriginalMinusJointTower m).compLinear P
    (W.transportDomain_open.prod (W.componentDomain_open m))
    (fun x hx => ⟨hzero, hx.2⟩)).congrOn
  intro x _
  simp only [P, ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.coe_snd', liftSectorParameter_eq_affine, map_zero, add_zero]

def negativeRawDefectJointTower (m : ℕ) :
    SmoothDirections (W.transportDomain ×ˢ W.componentDomain m)
      (fun x : Parameter W.S × PolarPoint =>
        minusCharacteristicSpeed (originalCoefficients W.D W.S W.C
          (liftSectorParameter W.S W.C x.1)) x.2 -
        minusCharacteristicSpeed (originalCoefficients W.D W.S W.C
          (W.C.referenceState, 0)) x.2) := by
  let L : PolarPoint →L[ℝ] ℝ :=
    ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ
  exact (solveSmoothDirectionsPostcomp
    (smoothDirectionsProd (W.negativeOriginalMinusJointTower m)
      (W.negativeRawReferenceJointTower m)) L).congrOn
    (fun _ _ => by simp only [L, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'])

def negativeTransportForcingJointTower (m : ℕ) :
    SmoothDirections (W.transportDomain ×ˢ W.componentDomain m)
      (fun x : Parameter W.S × PolarPoint =>
        (minusCharacteristicSpeed (originalCoefficients W.D W.S W.C
          (liftSectorParameter W.S W.C x.1)) x.2 -
        minusCharacteristicSpeed (originalCoefficients W.D W.S W.C
          (W.C.referenceState, 0)) x.2) +
        returnCorrectionVelocityLinear W.D W.S W.C W.cutoff.cutoff
          (liftSectorParameter W.S W.C x.1) m x.2
          (W.R.residual (liftSectorParameter W.S W.C x.1))) :=
  smoothDirectionsAdd (W.negativeRawDefectJointTower m)
    (W.negativeCorrectionVelocityJointTower m)

theorem negativeTransport_speed_identity (m : ℕ) {z : Parameter W.S}
    (hz : z ∈ W.transportDomain) {p : PolarPoint} (hp : p ∈ W.componentDomain m) :
    minusCharacteristicSpeed (W.L.coefficients (liftSectorParameter W.S W.C z)) p =
      minusCharacteristicSpeed (originalCoefficients W.D W.S W.C
        (liftSectorParameter W.S W.C z)) p +
        deriv (W.cutoff.cutoff m) p.1 *
          returnFlowInverseSlope W.S W.C (liftSectorParameter W.S W.C z) m p *
            returnCorrectionPulledDisplacementLinear W.S W.C W.cutoff.cutoff
              (liftSectorParameter W.S W.C z) m p
              (W.R.residual (liftSectorParameter W.S W.C z)) := by
  have he := returnCorrectionVelocityLinear_at_actual W.through03.1.1 W.through03.1.2
    W.cutoff.cutoff (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (W.through03.1.1.2.2.1.liftSectorParameter_sector z) m p
  rw [returnCorrectionVelocityLinear_eq_transportProduct,
    ← W.negativeMinus_eq_corrected m hz hp] at he
  linarith only [he]

theorem negativeTransport_speed_recurrence (m n a b : ℕ)
    (z w : Parameter W.S) (hz : z ∈ W.transportDomain)
    {p : PolarPoint} (hp : p ∈ W.componentDomain m) :
    jointMixedDiagonal (W.negativeMinusJointTower m) n a b z w p =
      jointMixedDiagonal (W.negativeOriginalMinusJointTower m) n a b z w p +
      diagonalJetProduct
        (diagonalJetProduct
          (fun k i j (_ : Unit) =>
            jointMixedDiagonal (W.negativeCutoffDerivativeJointTower m) k i j z w p)
          (fun k i j (_ : Unit) =>
            jointMixedDiagonal (W.negativeInverseSlopeJointTower m) k i j z w p))
        (fun k i j (_ : Unit) =>
          jointMixedDiagonal (W.negativePulledCorrectionJointTower m) k i j z w p)
        n a b () :=
  jointMixedDiagonal_add_triple_mul
    (W.negativeOriginalMinusJointTower m) (W.negativeCutoffDerivativeJointTower m)
    (W.negativeInverseSlopeJointTower m) (W.negativePulledCorrectionJointTower m)
    (W.negativeMinusJointTower m) W.transportDomain_open (W.componentDomain_open m)
    (W.transportDomain_convex m) (fun _ hx _ hq => W.negativeTransport_speed_identity m hx hq)
    n a b z w hz p hp

theorem negativeTransport_slope_recurrence (m n a b : ℕ)
    (z w : Parameter W.S) (hz : z ∈ W.transportDomain)
    {p : PolarPoint} (hp : p ∈ W.componentDomain m) :
    jointMixedDiagonal (W.negativeInverseSlopeJointTower m) n (a + 1) b z w p =
      diagonalJetProduct
        (fun k i j (_ : Unit) =>
          jointMixedDiagonal (W.negativeOriginalMinusJointTower m) k i (j + 1) z w p)
        (fun k i j (_ : Unit) =>
          jointMixedDiagonal (W.negativeInverseSlopeJointTower m) k i j z w p) n a b () -
      diagonalJetProduct
        (fun k i j (_ : Unit) =>
          jointMixedDiagonal (W.negativeOriginalMinusJointTower m) k i j z w p)
        (fun k i j (_ : Unit) =>
          jointMixedDiagonal (W.negativeInverseSlopeJointTower m) k i (j + 1) z w p) n a b () := by
  apply jointMixedDiagonal_variational_transport
    (W.negativeInverseSlopeJointTower m) (W.negativeOriginalMinusJointTower m)
    W.transportDomain_open (W.componentDomain_open m) (W.transportDomain_convex m)
    _ n a b z w hz hp
  intro x hx y hy
  exact W.through03.1.1.returnFlowInverseSlope_transport_of_discriminant W.hS W.hT
    (liftSectorParameter_mem_stateNeighborhood hx le_rfl)
    (W.through03.1.1.2.2.1.liftSectorParameter_sector x) m y hy.1
    (W.negativeOriginalDiscriminant_pos m hx hy.1)

theorem negativeTransport_residual_recurrence (m n a b : ℕ)
    (z w : Parameter W.S) (hz : z ∈ W.transportDomain)
    {p : PolarPoint} (hp : p ∈ W.componentDomain m) :
    jointMixedDiagonal (W.negativePulledCorrectionJointTower m) n (a + 1) b z w p =
      -diagonalJetProduct
        (fun k i j (_ : Unit) =>
          jointMixedDiagonal (W.negativeMinusJointTower m) k i j z w p)
        (fun k i j (_ : Unit) =>
          jointMixedDiagonal (W.negativePulledCorrectionJointTower m) k i (j + 1) z w p)
        n a b () := by
  apply jointMixedDiagonal_transport
    (W.negativePulledCorrectionJointTower m) (W.negativeMinusJointTower m)
    W.transportDomain_open (W.componentDomain_open m) (W.transportDomain_convex m)
    _ n a b z w hz hp
  intro x hx y hy
  have he := W.through03.1.1.returnCorrectionPulledDisplacementLinear_transport_actual
    W.hS W.hT (liftSectorParameter_mem_stateNeighborhood hx le_rfl)
    (W.through03.1.1.2.2.1.liftSectorParameter_sector x) W.through03.1.2
    W.cutoff.cutoff m (W.cutoff.cutoff_smooth m) (W.cutoff.range_on_component m)
    (W.R.residual (liftSectorParameter W.S W.C x)) y hy.1
  rw [W.negativeTransport_speed_identity m hx hy]
  exact he.trans (by ring)

theorem negativeTransport_firstIntegral_recurrence (m n a b : ℕ)
    (z w : Parameter W.S) (hz : z ∈ W.transportDomain)
    {p : PolarPoint} (hp : p ∈ W.componentDomain m) :
    jointMixedDiagonal (W.negativeFirstIntegralDefectJointTower m) n (a + 1) b z w p =
      -diagonalJetProduct
        (fun k i j (_ : Unit) =>
          jointMixedDiagonal (W.negativeMinusJointTower m) k i j z w p)
        (fun k i j (_ : Unit) =>
          jointMixedDiagonal (W.negativeFirstIntegralDefectJointTower m) k i (j + 1) z w p)
        n a b () - jointMixedDiagonal (W.negativeTransportForcingJointTower m) n a b z w p := by
  apply n04NegativeChart_jointMixedDiagonal_inhomogeneous_transport
    (W.negativeFirstIntegralDefectJointTower m) (W.negativeMinusJointTower m)
    (W.negativeTransportForcingJointTower m) W.transportDomain_open
    (W.componentDomain_open m) (W.transportDomain_convex m) _ n a b z w hz hp
  intro x hx y hy
  let v := liftSectorParameter W.S W.C x
  have hv := liftSectorParameter_mem_stateNeighborhood hx le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector x
  have hΦ := n04b_actualMinusFlow_regular W.through03 W.hS W.hT W.field hv hs m
  have hL := stateLeftChart_contDiff W.S v m (W.hS.2.1 (3 / 4 : ℝ))
  have hflow := W.through03.2.2.2.2.2.1 v hv hs m
  have hτ := n04b_referenceTravel_hasDerivAt W.radial.1.choose_spec.1
    W.through03.1.1.2.2.2.1 m hy.1
  have htransport := n04NegativeChart_minusFirstIntegral_defect_transport
    hΦ Real.pi_ne_zero hL (fun r hr θ => (hflow θ).2.2.1 r hr) hy hτ
  have href := n07a_minusCharacteristicSpeed_reference W.hS W.hT W.through03.1.1
    (W.through03.1.1.negativeComponent_subset_annularOpen m hy).1 y.2
  have hcorrection := returnCorrectionVelocityLinear_at_actual
    W.through03.1.1 W.through03.1.2 W.cutoff.cutoff hv hs m y
  rw [← W.negativeMinus_eq_corrected m hx hy] at hcorrection
  rw [← (n04b_characteristic_speed_factorization (W.L.coefficients v) y).1] at htransport
  have href' : minusCharacteristicSpeed
      (originalCoefficients W.D W.S W.C (W.C.referenceState, 0)) y =
        -opticalSpeed W.D.w y.1 := href
  have hforcing :
      (minusCharacteristicSpeed (originalCoefficients W.D W.S W.C v) y -
        minusCharacteristicSpeed (originalCoefficients W.D W.S W.C
          (W.C.referenceState, 0)) y) +
        returnCorrectionVelocityLinear W.D W.S W.C W.cutoff.cutoff v m y (W.R.residual v) =
      minusCharacteristicSpeed (W.L.coefficients v) y + opticalSpeed W.D.w y.1 := by
    rw [href', hcorrection]
    ring
  exact htransport.trans (congrArg (fun e : ℝ =>
    -(minusCharacteristicSpeed (W.L.coefficients v) y *
      angularPartial (W.negativeFirstIntegralDefect x m) y) - e) hforcing.symm)

end ContinuousFlexibility.Analysis.N04RealizationStart

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeTransport_firstIntegral_recurrence'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeTransport_firstIntegral_recurrence
