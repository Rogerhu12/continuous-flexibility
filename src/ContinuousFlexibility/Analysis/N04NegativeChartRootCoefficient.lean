module

public import ContinuousFlexibility.Analysis.N04NegativeChartRootIdentification
public import ContinuousFlexibility.Analysis.N04NegativeGeometryChartTowers
public import ContinuousFlexibility.Analysis.N04NegativeGeometryRootCollarTowers

/-!
# The actual divided root travel coefficient

The positive coefficient is defined on the original parameter sector,
using the stored travel chart. Its joint tower exists on the whole
positive root band. A supplied inverse-flow representative identifies it
with the odd projection; subtracting the initial angle leaves this odd
projection unchanged. No positivity of an arbitrary extension is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04NegativeChart_rootOddCoefficient_sub_angle
    (G : ℝ × ℝ × ℝ → ℝ) {p : PolarPoint} (hp : p.1 ≠ 0) :
    rootOddCoefficient (fun q => G q - q.2.2) p = rootOddCoefficient G p := by
  simp only [rootOddCoefficient, rootOdd, if_neg hp]
  congr 1
  ring

theorem n04NegativeChart_rootEven_sub_angle
    (G : ℝ × ℝ × ℝ → ℝ) (p : PolarPoint) :
    rootEven (fun q => G q - q.2.2) p = rootEven G p - p.2 := by
  simp only [rootEven]
  ring

namespace N04RealizationStart

variable (W : N04RealizationStart)

/-- The normalized positive point stays in the full physical component. -/
theorem negativeScaledPoint_mem_component (m : ℕ) (side : Bool)
    {δ R : ℝ} (hδ : 0 < δ) (hband : δ * R ≤ W.C.right m - W.C.left m)
    {p : PolarPoint} (hp : p.1 ∈ Ioo (0 : ℝ) R) :
    W.negativeInwardPoint m side (δ * p.1, p.2) ∈
      Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ) := by
  have hx : 0 < δ * p.1 := mul_pos hδ hp.1
  have hw : δ * p.1 < W.C.right m - W.C.left m :=
    (mul_lt_mul_of_pos_left hp.2 hδ).trans_le hband
  refine ⟨?_, mem_univ _⟩
  cases side <;> simp only [negativeInwardPoint, inwardComponentPoint,
    Bool.false_eq_true, ↓reduceIte] <;> constructor <;> linarith only [hx, hw]

/-- The coefficient uses the actual oriented travel, including the
right endpoint's travel complement. -/
def negativeRootTravelCoefficient (m : ℕ) (side : Bool) (δ : ℝ)
    (z : StateDirections W.S × ℝ) (p : PolarPoint) : ℝ :=
  n04bTravelOrientation (W.C.travel m) side
    (n04bActualTravelChart W.S W.C W.L (liftSectorParameter W.S W.C z) m
      (W.negativeInwardPoint m side (δ * p.1, p.2))).1 / p.1 ^ (3 / 2 : ℝ)

def negativeRootAngleDefect (m : ℕ) (side : Bool) (δ : ℝ)
    (z : StateDirections W.S × ℝ) (p : PolarPoint) : ℝ :=
  (n04bActualTravelChart W.S W.C W.L (liftSectorParameter W.S W.C z) m
    (W.negativeInwardPoint m side (δ * p.1, p.2))).2 - p.2

def negativeScaledTravelJointTower (m : ℕ) (side : Bool)
    {δ R : ℝ} (hδ : 0 < δ) (hband : δ * R ≤ W.C.right m - W.C.left m) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ (Ioo (0 : ℝ) R ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        n04bActualTravelChart W.S W.C W.L (liftSectorParameter W.S W.C x.1) m
          (W.negativeInwardPoint m side (δ * x.2.1, x.2.2))) := by
  have he (p : PolarPoint) :
      rootProfileShift (n01ComponentRoot W.C m side)
        (n01ComponentRootOrientation side * δ) p =
        W.negativeInwardPoint m side (δ * p.1, p.2) := by
    rw [W.negativeInwardPoint_root_add]
    simp only [rootProfileShift, mul_assoc]
  have hm : MapsTo
      (rootProfileShift (n01ComponentRoot W.C m side)
        (n01ComponentRootOrientation side * δ))
      (Ioo (0 : ℝ) R ×ˢ (univ : Set ℝ))
      (Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) := by
    intro p hp
    rw [he p]
    exact W.negativeScaledPoint_mem_component m side hδ hband hp.1
  let J := NegativeRootCollar.jointRootShift
    (isOpen_sectorNeighborhood W.S W.base W.ε W.ε)
    (isOpen_Ioo.prod isOpen_univ) (n01ComponentRoot W.C m side)
    (n01ComponentRootOrientation side * δ) hm (W.negativeTravelJointTower m)
  exact J.congrOn (fun x _ => congrArg
    (n04bActualTravelChart W.S W.C W.L (liftSectorParameter W.S W.C x.1) m) (he x.2))

/-- Subtracting the fixed physical angle keeps the actual travel tower. -/
def negativeRootAngleDefectJointTower (m : ℕ) (side : Bool)
    {δ R : ℝ} (hδ : 0 < δ) (hband : δ * R ≤ W.C.right m - W.C.left m) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ (Ioo (0 : ℝ) R ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        W.negativeRootAngleDefect m side δ x.1 x.2) := by
  let π : ((StateDirections W.S × ℝ) × PolarPoint) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ (StateDirections W.S × ℝ) PolarPoint)
  let Jθ := smoothDirectionsLinearOn π
    ((isOpen_sectorNeighborhood W.S W.base W.ε W.ε).prod
      ((isOpen_Ioo : IsOpen (Ioo (0 : ℝ) R)).prod isOpen_univ))
  exact (smoothDirectionsProd (W.negativeScaledTravelJointTower m side hδ hband) Jθ).comp_contDiff
    isOpen_univ
    ((contDiff_fst.snd.sub contDiff_snd) :
      ContDiff ℝ ∞ (fun p : PolarPoint × ℝ => p.1.2 - p.2)).contDiffOn
    (fun _ _ => mem_univ _)

/-- Joint smoothness belongs to the actual sector function before any
finite-dimensional representative or derivative order is chosen. -/
def negativeRootTravelCoefficientJointTower (m : ℕ) (side : Bool)
    {δ R : ℝ} (hδ : 0 < δ) (hband : δ * R ≤ W.C.right m - W.C.left m) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ (Ioo (0 : ℝ) R ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        W.negativeRootTravelCoefficient m side δ x.1 x.2) := by
  let π : ((StateDirections W.S × ℝ) × PolarPoint) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ (StateDirections W.S × ℝ) PolarPoint)
  let Jx := smoothDirectionsLinearOn π
    ((isOpen_sectorNeighborhood W.S W.base W.ε W.ε).prod
      ((isOpen_Ioo : IsOpen (Ioo (0 : ℝ) R)).prod isOpen_univ))
  let J := W.negativeScaledTravelJointTower m side hδ hband
  let g : PolarPoint × ℝ → ℝ := fun p =>
    n04bTravelOrientation (W.C.travel m) side p.1.1 / p.2 ^ (3 / 2 : ℝ)
  have ht : ContDiff ℝ ∞ (fun p : PolarPoint × ℝ =>
      n04bTravelOrientation (W.C.travel m) side p.1.1) := by
    cases side
    · exact contDiff_fst.fst
    · exact contDiff_const.sub contDiff_fst.fst
  have hg : ContDiffOn ℝ ∞ g ((univ : Set PolarPoint) ×ˢ Ioi (0 : ℝ)) := by
    intro p hp
    have hpow : ContDiffAt ℝ ∞ (fun q : PolarPoint × ℝ => q.2 ^ (3 / 2 : ℝ)) p :=
      (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hp.2)).comp p contDiffAt_snd
    exact (ht.contDiffAt.div hpow (Real.rpow_pos_of_pos hp.2 (3 / 2 : ℝ)).ne').contDiffWithinAt
  exact (smoothDirectionsProd J Jx).comp_contDiff (isOpen_univ.prod isOpen_Ioi) hg
    (fun x hx => ⟨mem_univ _, hx.2.1.1⟩)

def negativeRootTravelCoefficientMixedRegularity (m : ℕ) (side : Bool)
    {δ R : ℝ} (hδ : 0 < δ) (hband : δ * R ≤ W.C.right m - W.C.left m) :
    MixedJetRegularity (sectorNeighborhood W.S W.base W.ε W.ε)
      (Ioo (0 : ℝ) R ×ˢ univ) (W.negativeRootTravelCoefficient m side δ) :=
  n04Realization_jointMixedRegularity
    (W.negativeRootTravelCoefficientJointTower m side hδ hband)
    (isOpen_sectorNeighborhood W.S W.base W.ε W.ε) (isOpen_Ioo.prod isOpen_univ)
    ((sectorNeighborhood_convex W.S W.base W.ε W.ε).prod
      ((convex_Ioo _ _).prod convex_univ))

theorem negativeRootTravelCoefficient_pos (m : ℕ) (side : Bool)
    {δ R : ℝ} (hδ : 0 < δ) (hband : δ * R ≤ W.C.right m - W.C.left m)
    {z : StateDirections W.S × ℝ} (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {p : PolarPoint} (hp : p.1 ∈ Ioo (0 : ℝ) R) :
    0 < W.negativeRootTravelCoefficient m side δ z p := by
  have hpoint := W.negativeScaledPoint_mem_component m side hδ hband hp
  have ht := (n04b_actualTravelChart_bijOn W.through03 W.hS W.hT W.field
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (W.through03.1.1.2.2.1.liftSectorParameter_sector z) m).mapsTo hpoint
  exact div_pos (n04b_travelOrientation_pos_of_fullStrip side ht.1)
    (Real.rpow_pos_of_pos hp.1 _)

namespace NegativeOpticalFactors

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}
  (F : NegativeOpticalFactors W e)
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {d c : P × PolarPoint → ℝ} {δ : ℝ}

/-- The stored positive coefficient is the divided odd part of the same
supplied inverse coordinate, with its initial angle subtracted. -/
theorem fullHalfFields_root_coefficient
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdp : ∀ y r, Function.Periodic (fun θ => d (y, (r, θ))) Real.pi)
    (hcp : ∀ y r, Function.Periodic (fun θ => c (y, (r, θ))) Real.pi)
    (A : NegativeChartRootFlowData d c δ) (y : P)
    {z : StateDirections W.S × ℝ}
    (hz : liftSectorParameter W.S W.C z ∈ stateNeighborhood W.S W.C W.base (W.ε / 2))
    (hs : stateSector W.S (liftSectorParameter W.S W.C z).1) (m : ℕ) (side : Bool)
    {R : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hδc : δ * R ≤ W.negativeMaterialCollar m)
    (hrep : ∀ p : PolarPoint, p.1 ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) →
      d (y, p) = F.fullHalfDrift (liftSectorParameter W.S W.C z) m side p ∧
      c (y, p) = F.fullHalfSpeed (liftSectorParameter W.S W.C z) m side p)
    {p : PolarPoint} (hp : p.1 ∈ Ioc (0 : ℝ) R) :
    W.negativeRootTravelCoefficient m side δ z p = rootOddCoefficient
      (fun q => W.negativeRootInverseCoordinate A (liftSectorParameter W.S W.C z) m side y q -
        q.2.2) p := by
  let G := W.negativeRootInverseCoordinate A (liftSectorParameter W.S W.C z) m side y
  have ht := F.fullHalfFields_root_travel hd hc hdp hcp A y hz hs m side hR hδ hδc hrep hp p.2
  have hv := congrArg Prod.fst
    (characteristicTravelChart_rootCharacteristicCoordinate G (p := p) hp.1)
  rw [ht] at hv
  dsimp only at hv
  rw [n04NegativeChart_rootOddCoefficient_sub_angle _ hp.1.ne']
  change _ / p.1 ^ (3 / 2 : ℝ) = rootOddCoefficient G p
  apply (div_eq_iff (Real.rpow_pos_of_pos hp.1 (3 / 2 : ℝ)).ne').2
  exact hv.trans (mul_comm _ _)

/-- The other actual coordinate uses the even projection of exactly
the same displacement, with no estimate for the unbounded angle itself. -/
theorem fullHalfFields_root_angle_defect
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdp : ∀ y r, Function.Periodic (fun θ => d (y, (r, θ))) Real.pi)
    (hcp : ∀ y r, Function.Periodic (fun θ => c (y, (r, θ))) Real.pi)
    (A : NegativeChartRootFlowData d c δ) (y : P)
    {z : StateDirections W.S × ℝ}
    (hz : liftSectorParameter W.S W.C z ∈ stateNeighborhood W.S W.C W.base (W.ε / 2))
    (hs : stateSector W.S (liftSectorParameter W.S W.C z).1) (m : ℕ) (side : Bool)
    {R : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hδc : δ * R ≤ W.negativeMaterialCollar m)
    (hrep : ∀ p : PolarPoint, p.1 ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) →
      d (y, p) = F.fullHalfDrift (liftSectorParameter W.S W.C z) m side p ∧
      c (y, p) = F.fullHalfSpeed (liftSectorParameter W.S W.C z) m side p)
    {p : PolarPoint} (hp : p.1 ∈ Ioc (0 : ℝ) R) :
    W.negativeRootAngleDefect m side δ z p = rootEven
      (fun q => W.negativeRootInverseCoordinate A (liftSectorParameter W.S W.C z) m side y q -
        q.2.2) p := by
  let G := W.negativeRootInverseCoordinate A (liftSectorParameter W.S W.C z) m side y
  have ht := F.fullHalfFields_root_travel hd hc hdp hcp A y hz hs m side hR hδ hδc hrep hp p.2
  have hv := congrArg Prod.snd
    (characteristicTravelChart_rootCharacteristicCoordinate G (p := p) hp.1)
  rw [ht] at hv
  dsimp only at hv
  rw [n04NegativeChart_rootEven_sub_angle]
  exact congrArg (fun t : ℝ => t - p.2) hv

end NegativeOpticalFactors
end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeRootTravelCoefficientJointTower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeRootTravelCoefficientJointTower
