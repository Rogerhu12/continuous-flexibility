import ContinuousFlexibility.Analysis.N04NegativeChartReturnCircleBounds
import ContinuousFlexibility.Analysis.N01RootLabels

/-! The two actual root labels, in one circle family with one low base. -/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)

def N01Properties.n04RootLabelCircle (side : Bool) (z : StateDirections S × ℝ) :
    CircleSpace S :=
  if side then circleOddLinear (hS.2.1 (3 / 4 : ℝ))
    (hN.sectorReturnTransportCircle hS hT z) else z.1.val.2.2.2

theorem N01Properties.n04RootLabelCircle_lift (side : Bool)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) (m : ℕ) :
    circleAffineLift (fun _ => 0)
      ((S.circle (3 / 4 : ℝ)).decode (hN.n04RootLabelCircle hS hT side z)) 1 m =
      n01RootLabel S C (liftSectorParameter S C z) m side := by
  cases side with
  | false =>
      funext θ
      simpa only [n04RootLabelCircle, n01RootLabel, circleAffineLift,
        Bool.false_eq_true, ↓reduceIte, add_zero, one_mul] using
        (hN.2.2.1.sector_leftChart z m θ).symm
  | true => exact hN.sectorReturnTransportCircle_odd_lift hS hT z hz m

theorem N01Properties.n04FixedBase_rootLabelCircle
    (hflow : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m r,
      r ∈ Icc (C.left m) (C.right m) → ∀ θ,
        1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ∧
        deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ≤ 3 / 2) :
    N04FixedBaseSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (hN.n04RootLabelCircle hS hT) := by
  let H : CircleModelData := S.circle (3 / 4 : ℝ)
  have hH := hS.2.1 (3 / 4 : ℝ)
  have hl := n04FixedBase_sectorChart (I := Bool) S base ε
  have hu := hN.n04FixedBase_sectorReturnTransportCircle (I := Bool) hS hT hflow
  have hr := hu.postTameContinuousLinear (circleOddContinuousLinear hH) (circleOddLinear_tame hH)
  let L : Bool → (H.Space × H.Space) →L[ℝ] H.Space := fun side =>
    if side then ContinuousLinearMap.snd ℝ H.Space H.Space
    else ContinuousLinearMap.fst ℝ H.Space H.Space
  have hproj := (hl.prodMk (sectorPairGrading_monotone S) hr).postContinuousLinear
    (r := H.grading) L 0
    (fun s => ⟨1, zero_le_one, fun side y => by
      cases side
      · simpa only [L, Bool.false_eq_true, ↓reduceIte, ContinuousLinearMap.coe_fst',
          Nat.add_zero, one_mul, pairGrading_apply] using
          le_add_of_nonneg_right (apply_nonneg (H.grading s) y.2)
      · simpa only [L, ↓reduceIte, ContinuousLinearMap.coe_snd',
          Nat.add_zero, one_mul, pairGrading_apply] using
          le_add_of_nonneg_left (apply_nonneg (H.grading s) y.1)⟩)
  apply hproj.congr
  intro side z _
  cases side <;> simp only [L, n04RootLabelCircle, Bool.false_eq_true, ↓reduceIte,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', circleOddContinuousLinear_apply]

end ContinuousFlexibility.Statements

/-- info: 'ContinuousFlexibility.Statements.N01Properties.n04FixedBase_rootLabelCircle'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Statements.N01Properties.n04FixedBase_rootLabelCircle
