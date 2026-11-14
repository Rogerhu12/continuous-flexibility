module

public import ContinuousFlexibility.Analysis.N04NegativeGeometryCoefficientTowers

/-!
# The literal negative height and its reciprocal have joint towers

Every factor in the actual root-height formula has already been
constructed on the whole original component. Its three strictly positive
scalar arguments permit ordinary smooth composition. The component germ
then identifies this formula with the stored chosen height, and all mixed
spatial parameter towers come from that single joint tower.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable (W : N04RealizationStart)

theorem negativeRootChart_radial_pos (m : ℕ) (side : Bool)
    {z : StateDirections W.S × ℝ}
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {p : PolarPoint} (hp : p ∈ Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) :
    0 < (n04bRootPhysicalChart
      (n04bActualTravelChart W.S W.C W.L (liftSectorParameter W.S W.C z) m)
      (W.C.travel m) side p).1 :=
  n04bRootPhysicalChart_fst_pos (n04b_travelOrientation_pos_of_fullStrip side
    ((n04b_actualTravelChart_bijOn W.through03 W.hS W.hT W.field
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (W.through03.1.1.2.2.1.liftSectorParameter_sector z) m).mapsTo hp).1)

/-- The root-height formula uses the actual corrected radial coefficient,
half-gap and root-chart radial coordinate. -/
def negativeRootHeightJointTower (m : ℕ) (side : Bool) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (W.C.left m) (W.C.right m) ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        n04bRootPhysicalHeight (W.L.coefficients (liftSectorParameter W.S W.C x.1))
          (n04bCharacteristicHalfGap (W.L.coefficients (liftSectorParameter W.S W.C x.1)))
          (n04bActualTravelChart W.S W.C W.L (liftSectorParameter W.S W.C x.1) m)
          (W.C.travel m) side x.2) := by
  let V : Set (ℝ × (ℝ × PolarPoint)) := {q | 0 < q.1 ∧ 0 < q.2.1 ∧ 0 < q.2.2.1}
  have hV : IsOpen V :=
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_const continuous_snd.fst).inter
        (isOpen_lt continuous_const continuous_snd.snd.fst))
  let H : ℝ × (ℝ × PolarPoint) → ℝ := fun q =>
    (Real.sqrt (q.1 * q.2.1 / Real.sqrt q.2.2.1))⁻¹
  have hH : ContDiffOn ℝ ∞ H V := by
    intro q hq
    have hs : 0 < Real.sqrt q.2.2.1 := Real.sqrt_pos.mpr hq.2.2
    have hd : 0 < q.1 * q.2.1 / Real.sqrt q.2.2.1 :=
      div_pos (mul_pos hq.1 hq.2.1) hs
    exact ((((contDiffAt_fst.mul contDiffAt_snd.fst).div
      (contDiffAt_snd.snd.fst.sqrt hq.2.2.ne') hs.ne').sqrt hd.ne').inv
        (Real.sqrt_pos.mpr hd).ne').contDiffWithinAt
  have hmap : MapsTo
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        ((W.L.coefficients (liftSectorParameter W.S W.C x.1)).a x.2,
          n04bCharacteristicHalfGap
            (W.L.coefficients (liftSectorParameter W.S W.C x.1)) x.2,
          n04bRootPhysicalChart
            (n04bActualTravelChart W.S W.C W.L (liftSectorParameter W.S W.C x.1) m)
            (W.C.travel m) side x.2))
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (W.C.left m) (W.C.right m) ×ˢ univ)) V := by
    intro x hx
    have hz := liftSectorParameter_mem_stateNeighborhood (C := W.C) hx.1 le_rfl
    have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector x.1
    exact ⟨W.field.positive_a _ hz hs x.2
        (W.through03.1.1.negativeComponent_subset_annularOpen m hx.2),
      n04b_actualCharacteristic_halfGap_pos W.through03 W.field hz hs m hx.2,
      W.negativeRootChart_radial_pos m side hx.1 hx.2⟩
  exact (smoothDirectionsProd (W.negativeRadialJointTower m)
    (smoothDirectionsProd (W.negativeHalfGapJointTower m)
      (W.negativeRootChartJointTower m side))).comp_contDiff hV hH hmap

/-- The actual chosen height is its explicit root formula at every
physical point of the original component. -/
def negativeHeightJointTower (m : ℕ) (side : Bool) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (W.C.left m) (W.C.right m) ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        n04bActualNegativeHeight W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C x.1) m side x.2) := by
  apply (W.negativeRootHeightJointTower m side).congrOn
  intro x hx
  exact ((n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field
    (liftSectorParameter_mem_stateNeighborhood hx.1 le_rfl)
    (W.through03.1.1.2.2.1.liftSectorParameter_sector x.1) m side).component_height_germ
      hx.2).self_of_nhds.symm

theorem negativeHeight_pos (m : ℕ) (side : Bool)
    {z : StateDirections W.S × ℝ}
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {p : PolarPoint} (hp : p ∈ Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) :
    0 < n04bActualNegativeHeight W.hT W.hS W.through03 W.field
      (liftSectorParameter W.S W.C z) m side p := by
  have hz' := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
  rw [((n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field
    hz' hs m side).component_height_germ hp).self_of_nhds]
  exact (n04b_actualRootPhysical_regular_at W.through03 W.hS W.hT W.field
    hz' hs m side hp).2.2.2

def negativeHeightInverseJointTower (m : ℕ) (side : Bool) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (W.C.left m) (W.C.right m) ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        (n04bActualNegativeHeight W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C x.1) m side x.2)⁻¹) :=
  (W.negativeHeightJointTower m side).comp_contDiff isOpen_Ioi
    (contDiffOn_id.inv (fun q (hq : q ∈ Ioi (0 : ℝ)) => hq.ne'))
    (fun x hx => W.negativeHeight_pos m side hx.1 hx.2)

/-- All mixed physical derivatives of the same actual height have their
parameter towers without a further neighborhood choice. -/
def negativeHeightMixedRegularity (m : ℕ) (side : Bool) :
    MixedJetRegularity (sectorNeighborhood W.S W.base W.ε W.ε)
      (Ioo (W.C.left m) (W.C.right m) ×ˢ univ)
      (fun z p => n04bActualNegativeHeight W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m side p) :=
  n04Realization_jointMixedRegularity (W.negativeHeightJointTower m side)
    (sectorNeighborhood_isOpen W.S W.base W.ε W.ε)
    (isOpen_Ioo.prod isOpen_univ)
    ((sectorNeighborhood_convex W.S W.base W.ε W.ε).prod
      ((convex_Ioo _ _).prod convex_univ))

end ContinuousFlexibility.Analysis.N04RealizationStart

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeHeightJointTower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeHeightJointTower
