import ContinuousFlexibility.Analysis.N04NegativeGeometryChartTowers
import ContinuousFlexibility.Analysis.N01CoefficientJointTower
import ContinuousFlexibility.Analysis.N01ReturnVelocitySpatialTower
import ContinuousFlexibility.Analysis.ReturnCorrectionResidualLinear

/-!
# Actual corrected radial coefficient and half-gap towers

The original coefficient towers and the retained residual velocity give
the literal corrected minus characteristic speed. Reflection recovers
the actual positive half-gap. Thus the physical height below uses the
stored corrected field, including the inactive part of each component.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis.N04RealizationStart

open Set ContinuousFlexibility.Statements
open scoped ContDiff

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

private theorem original_add_correction {a c v : ℝ} (h : v = c - a) : a + v = c := by
  rw [h]
  ring

private theorem halfGap_of_reflection (A : SymmetricCoefficients) (p : PolarPoint)
    (hdrift : n04bCharacteristicDrift A (p.1, -p.2) = -n04bCharacteristicDrift A p)
    (hgap : n04bCharacteristicHalfGap A (p.1, -p.2) = n04bCharacteristicHalfGap A p) :
    (-1 / 2 : ℝ) * (minusCharacteristicSpeed A (p.1, -p.2) +
      minusCharacteristicSpeed A p) = n04bCharacteristicHalfGap A p := by
  rw [(n04b_characteristic_speed_factorization A (p.1, -p.2)).1,
    (n04b_characteristic_speed_factorization A p).1, hdrift, hgap]
  ring

variable (W : N04RealizationStart)

theorem negativeOriginalDiscriminant_pos (m : ℕ)
    {z : StateDirections W.S × ℝ}
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {p : PolarPoint} (hp : p.1 ∈ Ioo (W.C.left m) (W.C.right m)) :
    0 < (originalCoefficients W.D W.S W.C (liftSectorParameter W.S W.C z)).b p ^ 2 -
      (originalCoefficients W.D W.S W.C (liftSectorParameter W.S W.C z)).a p *
        (originalCoefficients W.D W.S W.C (liftSectorParameter W.S W.C z)).c p :=
  W.through03.1.1.n04NegativeGeometry_originalDiscriminant_of_preservedCorrection
    W.field W.cutoff.cutoff W.coefficients_eq W.cutoff.discriminant_on_support
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (W.through03.1.1.2.2.1.liftSectorParameter_sector z) m hp

theorem negativeOriginalRadial_pos (m : ℕ)
    {z : StateDirections W.S × ℝ}
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {p : PolarPoint} (hp : p ∈ Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) :
    0 < (originalCoefficients W.D W.S W.C (liftSectorParameter W.S W.C z)).a p :=
  W.through03.1.1.originalRadialCoefficient_pos
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (W.through03.1.1.2.2.1.liftSectorParameter_sector z)
    (W.through03.1.1.negativeComponent_subset_annularOpen m hp)

/-- The original radial coefficient is unchanged by the actual patch. -/
def negativeRadialJointTower (m : ℕ) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (W.C.left m) (W.C.right m) ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        (W.L.coefficients (liftSectorParameter W.S W.C x.1)).a x.2) := by
  let J := W.through03.1.1.originalCoefficient_parameterSpatialTower
    W.hS W.hT m (W.C.cell m) (W.host m) 0
  apply J.congrOn
  intro x hx
  simp only [originalCoefficientEntry, ↓reduceIte, W.coefficients_eq,
    returnCorrectedCoefficients_a]

/-- Smooth scalar operations on the three original coefficients give
the original minus speed on the entire open component. -/
def negativeOriginalMinusJointTower (m : ℕ) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (W.C.left m) (W.C.right m) ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        minusCharacteristicSpeed
          (originalCoefficients W.D W.S W.C (liftSectorParameter W.S W.C x.1)) x.2) := by
  let J := fun i : Fin 3 => W.through03.1.1.originalCoefficient_parameterSpatialTower
    W.hS W.hT m (W.C.cell m) (W.host m) i
  let V : Set (ℝ × (ℝ × ℝ)) := {q | 0 < q.1 ∧ 0 < q.2.1 ^ 2 - q.1 * q.2.2}
  have hV : IsOpen V :=
    (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_const
        ((continuous_snd.fst.pow 2).sub (continuous_fst.mul continuous_snd.snd)))
  have hkernel : ContDiffOn ℝ ∞
      (fun q : ℝ × (ℝ × ℝ) =>
        q.2.1 / q.1 - Real.sqrt (q.2.1 ^ 2 - q.1 * q.2.2) / q.1) V := by
    intro q hq
    exact ((contDiffAt_snd.fst.div contDiffAt_fst hq.1.ne').sub
      ((((contDiffAt_snd.fst.pow 2).sub
        (contDiffAt_fst.mul contDiffAt_snd.snd)).sqrt hq.2.ne').div
          contDiffAt_fst hq.1.ne')).contDiffWithinAt
  have hmap : MapsTo
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        (originalCoefficientEntry W.D W.S W.C 0 (liftSectorParameter W.S W.C x.1) x.2,
          originalCoefficientEntry W.D W.S W.C 1 (liftSectorParameter W.S W.C x.1) x.2,
          originalCoefficientEntry W.D W.S W.C 2 (liftSectorParameter W.S W.C x.1) x.2))
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (W.C.left m) (W.C.right m) ×ˢ univ)) V := by
    intro x hx
    change 0 < (originalCoefficients W.D W.S W.C
        (liftSectorParameter W.S W.C x.1)).a x.2 ∧
      0 < (originalCoefficients W.D W.S W.C
        (liftSectorParameter W.S W.C x.1)).b x.2 ^ 2 -
          (originalCoefficients W.D W.S W.C (liftSectorParameter W.S W.C x.1)).a x.2 *
            (originalCoefficients W.D W.S W.C (liftSectorParameter W.S W.C x.1)).c x.2
    exact
      And.intro (W.negativeOriginalRadial_pos m hx.1 hx.2)
        (W.negativeOriginalDiscriminant_pos m hx.1 hx.2.1)
  apply ((smoothDirectionsProd (J 0) (smoothDirectionsProd (J 1) (J 2))).comp_contDiff
    hV hkernel hmap).congrOn
  intro x hx
  rfl

/-- The actual residual velocity has the same full-component domain as
the chart; its construction uses no chart estimate. -/
def negativeCorrectionVelocityJointTower (m : ℕ) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (W.C.left m) (W.C.right m) ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        returnCorrectionVelocityLinear W.D W.S W.C W.cutoff.cutoff
          (liftSectorParameter W.S W.C x.1) m x.2
          (W.R.residual (liftSectorParameter W.S W.C x.1))) := by
  apply n04NegativeGeometry_glueComponentTowers
    (sectorNeighborhood_isOpen W.S W.base W.ε W.ε)
  intro l h hl hh
  exact W.through03.1.1.returnCorrectionVelocity_actual_parameterSpatialTower
    W.hS W.hT W.cutoff.cutoff W.cutoff.range_on_component W.cutoff.cutoff_smooth
    m l h hl hh
    (fun z hz p hp => W.negativeOriginalDiscriminant_pos m hz
      ⟨hl.trans hp.1, hp.2.trans hh⟩) W.through03.1.2

theorem negativeMinus_eq_corrected (m : ℕ)
    {z : StateDirections W.S × ℝ}
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {p : PolarPoint} (hp : p ∈ Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) :
    minusCharacteristicSpeed (W.L.coefficients (liftSectorParameter W.S W.C z)) p =
      returnCorrectedMinusSpeed W.D W.S W.C W.cutoff.cutoff
        (liftSectorParameter W.S W.C z) m p := by
  rw [W.coefficients_eq]
  exact returnCorrectedCoefficients_minusCharacteristicSpeed
    W.through03.1.1.2.2.2.1.2.2.1 W.cutoff.cutoff
    (liftSectorParameter W.S W.C z) m p hp.1
    (W.negativeOriginalRadial_pos m hz hp)
    (W.cutoff.corrected_speeds (liftSectorParameter W.S W.C z)
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (W.through03.1.1.2.2.1.liftSectorParameter_sector z) m p.1 hp.1 p.2).2

/-- The literal corrected characteristic speed has a joint tower. -/
def negativeMinusJointTower (m : ℕ) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (W.C.left m) (W.C.right m) ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        minusCharacteristicSpeed (W.L.coefficients (liftSectorParameter W.S W.C x.1)) x.2) := by
  apply (smoothDirectionsAdd (W.negativeOriginalMinusJointTower m)
    (W.negativeCorrectionVelocityJointTower m)).congrOn
  intro x hx
  exact (original_add_correction
    (returnCorrectionVelocityLinear_at_actual W.through03.1.1 W.through03.1.2
      W.cutoff.cutoff (liftSectorParameter_mem_stateNeighborhood hx.1 le_rfl)
      (W.through03.1.1.2.2.1.liftSectorParameter_sector x.1) m x.2)).trans
    (W.negativeMinus_eq_corrected m hx.1 hx.2).symm

/-- Reflection of the actual minus speed recovers the actual positive
half-gap, as a function on the same complete physical component. -/
def negativeHalfGapJointTower (m : ℕ) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (W.C.left m) (W.C.right m) ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        n04bCharacteristicHalfGap (W.L.coefficients (liftSectorParameter W.S W.C x.1)) x.2) := by
  let J := W.negativeMinusJointTower m
  let R : PolarPoint →L[ℝ] PolarPoint :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (-ContinuousLinearMap.snd ℝ ℝ ℝ)
  let P : ((StateDirections W.S × ℝ) × PolarPoint) →L[ℝ]
      (StateDirections W.S × ℝ) × PolarPoint :=
    (ContinuousLinearMap.fst ℝ (StateDirections W.S × ℝ) PolarPoint).prod
      (R.comp (ContinuousLinearMap.snd ℝ (StateDirections W.S × ℝ) PolarPoint))
  let K := J.compLinear P J.open_domain (fun x hx => by
    exact ⟨hx.1, hx.2.1, mem_univ _⟩)
  let A : (ℝ × ℝ) →L[ℝ] ℝ :=
    (-1 / 2 : ℝ) • (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ)
  apply (solveSmoothDirectionsPostcomp (smoothDirectionsProd K J) A).congrOn
  intro x hx
  have href := n04b_actualCharacteristic_reflection W.through03
    (liftSectorParameter_mem_stateNeighborhood hx.1 le_rfl)
    (W.through03.1.1.2.2.1.liftSectorParameter_sector x.1) x.2
  change (-1 / 2 : ℝ) *
    (minusCharacteristicSpeed (W.L.coefficients (liftSectorParameter W.S W.C x.1))
      (x.2.1, -x.2.2) +
      minusCharacteristicSpeed (W.L.coefficients (liftSectorParameter W.S W.C x.1)) x.2) = _
  exact halfGap_of_reflection _ _ href.1 href.2

end ContinuousFlexibility.Analysis.N04RealizationStart

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeHalfGapJointTower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeHalfGapJointTower
