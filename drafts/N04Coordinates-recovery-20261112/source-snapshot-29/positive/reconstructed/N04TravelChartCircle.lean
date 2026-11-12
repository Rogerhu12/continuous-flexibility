import ContinuousFlexibility.Analysis.N04MinusFirstIntegralCircle
import ContinuousFlexibility.Analysis.N04bActualTravelChart
import ContinuousFlexibility.Analysis.SpacesCircleParity
import ContinuousFlexibility.Analysis.CircleJointEvaluation
import ContinuousFlexibility.Analysis.TameProductDirections
import ContinuousFlexibility.Scalar.WeightedSmoothTameLinear

/-!
# The actual travel chart from one first-integral circle

The radial and angular displacements are the even and odd projections of
the same normalized first integral. The genuine joint tower below projects
one circle-valued tower before either derivative order is chosen. The
stored-chart adapter requires the literal corrected-flow identity; it does
not infer that identity from an arbitrary cumulative witness.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

local instance n04TravelChartCircleStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- `false` is the radial displacement, and `true` the angular displacement. -/
def N01Properties.n04TravelChartCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (side : Bool) (z : StateDirections S × ℝ) : CircleSpace S :=
  (if side then circleModelOddProjection (hS.2.1 (3 / 4 : ℝ))
    else circleModelEvenProjection (hS.2.1 (3 / 4 : ℝ)))
      (hN.n04MinusFirstIntegralCircle hS hT χ hχrange rsel hrsel z)

theorem N01Properties.n04TravelChartCircle_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (θ : ℝ) :
    n04bCharacteristicTravelChart
        (fun p => returnCorrectedMinusFlow S C χ (liftSectorParameter S C z) m p.1 p.2)
        (stateLeftChart S (liftSectorParameter S C z).1 m) (rsel m, θ) =
      (opticalTravel D.w (C.left m) (rsel m) +
        (S.circle (3 / 4 : ℝ)).decode
          (hN.n04TravelChartCircle hS hT χ hχrange rsel hrsel false z) m θ,
       θ + (S.circle (3 / 4 : ℝ)).decode
          (hN.n04TravelChartCircle hS hT χ hχrange rsel hrsel true z) m θ) := by
  let e := hN.n04MinusFirstIntegralCircle hS hT χ hχrange rsel hrsel z
  let t := opticalTravel D.w (C.left m) (rsel m)
  let V := n04bMinusFirstIntegral
    (fun p => returnCorrectedMinusFlow S C χ (liftSectorParameter S C z) m p.1 p.2)
    (stateLeftChart S (liftSectorParameter S C z).1 m)
  have hd (a : ℝ) : (S.circle (3 / 4 : ℝ)).decode e m a =
      V (rsel m, a) - (a + t) :=
    hN.n04MinusFirstIntegralCircle_decode hS hT χ hχrange rsel hrsel z hz m a
  change ((1 / 2 : ℝ) * (V (rsel m, θ) - -V (rsel m, -θ)),
      (1 / 2 : ℝ) * (-V (rsel m, -θ) + V (rsel m, θ))) =
    (t + (S.circle (3 / 4 : ℝ)).decode
      (circleModelEvenProjection (hS.2.1 (3 / 4 : ℝ)) e) m θ,
     θ + (S.circle (3 / 4 : ℝ)).decode
      (circleModelOddProjection (hS.2.1 (3 / 4 : ℝ)) e) m θ)
  rw [circleModelEvenProjection_decode, circleModelOddProjection_decode, hd θ, hd (-θ)]
  congr 1 <;> ring

theorem N01Properties.smoothTameOn_n04TravelChartCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (side : Bool) :
    SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (hN.n04TravelChartCircle hS hT χ hχrange rsel hrsel side) := by
  have he := hN.smoothTameOn_n04MinusFirstIntegralCircle hS hT χ hχrange rsel hrsel
  cases side with
  | false =>
      exact smoothTameOn_postcompose_generic (sectorPairGrading_monotone S)
        (sectorPairGrading_withSeminorms S) (withSeminorms_graded _ _) he
        (circleModelEvenProjection (hS.2.1 (3 / 4 : ℝ)))
        (circleModelEvenProjection_isTame (hS.2.1 (3 / 4 : ℝ)))
  | true =>
      exact smoothTameOn_postcompose_generic (sectorPairGrading_monotone S)
        (sectorPairGrading_withSeminorms S) (withSeminorms_graded _ _) he
        (circleModelOddProjection (hS.2.1 (3 / 4 : ℝ)))
        (circleModelOddProjection_isTame (hS.2.1 (3 / 4 : ℝ)))

/-- One genuine joint state-angle tower for the actual corrected travel map. -/
def N01Properties.n04TravelChartSelector_jointTower
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) (m : ℕ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun p : (StateDirections S × ℝ) × ℝ => n04bCharacteristicTravelChart
        (fun q => returnCorrectedMinusFlow S C χ (liftSectorParameter S C p.1) m q.1 q.2)
        (stateLeftChart S (liftSectorParameter S C p.1).1 m) (rsel m, p.2)) := by
  let J : SmoothDirections (sectorNeighborhood S base ε ε)
      (hN.n04MinusFirstIntegralCircle hS hT χ hχrange rsel hrsel) :=
    (hN.smoothTameOn_n04MinusFirstIntegralCircle hS hT χ hχrange rsel hrsel).choose
  let Je := solveSmoothDirectionsPostcomp J
    (circleModelEvenProjection (hS.2.1 (3 / 4 : ℝ)))
  let Jo := solveSmoothDirectionsPostcomp J
    (circleModelOddProjection (hS.2.1 (3 / 4 : ℝ)))
  have hH (j : ℕ) : 0 < T.H (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 j)).2.1
  let t : ℝ := opticalTravel D.w (C.left m) (rsel m)
  let R := (smoothDirectionsLinear (ContinuousLinearMap.id ℝ ℝ)).compAffine
    (0 : ((StateDirections S × ℝ) × ℝ) →L[ℝ] ℝ) t
    (J.open_domain.prod isOpen_univ) (fun _ _ => mem_univ _)
  let Kr := smoothDirectionsAdd R
    (circleDecodedJointDirections (hS.2.1 (3 / 4 : ℝ)) hH Je m)
  let Ka := circleAffineLiftJointDirections (hS.2.1 (3 / 4 : ℝ)) hH Jo
    (fun _ => 0) m
  apply (smoothDirectionsProd Kr Ka).congrOn
  intro p hp
  change ((t + (0 : ℝ)) + (S.circle (3 / 4 : ℝ)).decode
      (circleModelEvenProjection (hS.2.1 (3 / 4 : ℝ))
        (hN.n04MinusFirstIntegralCircle hS hT χ hχrange rsel hrsel p.1)) m p.2,
    p.2 + (0 : ℝ) + (S.circle (3 / 4 : ℝ)).decode
      (circleModelOddProjection (hS.2.1 (3 / 4 : ℝ))
        (hN.n04MinusFirstIntegralCircle hS hT χ hχrange rsel hrsel p.1)) m p.2) = _
  simpa only [n04TravelChartCircle, Bool.false_eq_true, ↓reduceIte, add_zero, t] using
    (hN.n04TravelChartCircle_decode hS hT χ hχrange rsel hrsel p.1 hp.1 m p.2).symm

/-- Retain the same chart stored by the literal N03 correction constructor. -/
def N01Properties.n04ActualTravelChartSelector_jointTower
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (L : ReturnCorrectionData S) (hL : L.minusFlow = returnCorrectedMinusFlow S C χ)
    (m : ℕ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun p : (StateDirections S × ℝ) × ℝ =>
        n04bActualTravelChart S C L (liftSectorParameter S C p.1) m (rsel m, p.2)) := by
  let J := hN.n04TravelChartSelector_jointTower hS hT χ hχrange rsel hrsel m
  apply J.congrOn
  intro p hp
  simp only [n04bActualTravelChart, hL]

end ContinuousFlexibility.Statements
