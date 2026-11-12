import ContinuousFlexibility.Analysis.N04CorrectedFlowInverseCircle
import ContinuousFlexibility.Analysis.N04bCharacteristicFirstIntegrals

/-!
# The actual normalized first integral in the circle model

The given left chart is composed with the actual inverse of the same
corrected flow. Its circle displacement retains the optical translation.
The circle composition theorem supplies genuine derivatives in the state
and angle, with the radial selector fixed throughout.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

local instance n04MinusFirstIntegralCircleStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def N01Properties.n04MinusFirstIntegralCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) : CircleSpace S :=
  hN.n04CorrectedFlowInverseCircle hS hT χ hχrange rsel hrsel z +
    circleShiftedChartComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
      (fun m => opticalTravel D.w (C.left m) (rsel m))
      (hN.n04CorrectedFlowInverseCircle hS hT χ hχrange rsel hrsel z) z.1.val.2.2.2

theorem N01Properties.n04MinusFirstIntegralCircle_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
      (hN.n04MinusFirstIntegralCircle hS hT χ hχrange rsel hrsel z) m θ =
      n04bMinusFirstIntegral
        (fun p => returnCorrectedMinusFlow S C χ (liftSectorParameter S C z) m p.1 p.2)
        (stateLeftChart S (liftSectorParameter S C z).1 m) (rsel m, θ) -
          (θ + opticalTravel D.w (C.left m) (rsel m)) := by
  let e := hN.n04CorrectedFlowInverseCircle hS hT χ hχrange rsel hrsel z
  let c : CircleSpace S := z.1.val.2.2.2
  let travel : ℕ → ℝ := fun j => opticalTravel D.w (C.left j) (rsel j)
  let q := circleShiftedChartComposeLinear
    (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num) travel e c
  let a : ℝ := θ + travel m
  let η : ℝ := Function.invFun
    (returnCorrectedMinusFlow S C χ (liftSectorParameter S C z) m (rsel m)) θ
  have he : (S.circle (3 / 4 : ℝ)).decode e m θ = η - a :=
    congrArg (fun u : ℕ → ℝ → ℝ => u m θ)
      (hN.n04CorrectedFlowInverseCircle_decode hS hT χ hχrange rsel hrsel z hz)
  have harg : a + (S.circle (3 / 4 : ℝ)).decode e m θ = η := by
    rw [he]
    ring
  have hq : (S.circle (3 / 4 : ℝ)).decode q m θ =
      (S.circle (3 / 4 : ℝ)).decode c m η :=
    (circleShiftedChartComposeLinear_decode
      (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num) travel e c m θ).trans
        (congrArg (fun x : ℝ => (S.circle (3 / 4 : ℝ)).decode c m x) harg)
  have hleft : stateLeftChart S (liftSectorParameter S C z).1 m η =
      η + (S.circle (3 / 4 : ℝ)).decode c m η :=
    hN.2.2.1.sector_leftChart z m η
  change (S.circle (3 / 4 : ℝ)).decode (e + q) m θ =
    stateLeftChart S (liftSectorParameter S C z).1 m η - a
  calc
    _ = (S.circle (3 / 4 : ℝ)).decode e m θ +
        (S.circle (3 / 4 : ℝ)).decode q m θ :=
      congrArg (fun u : ℕ → ℝ → ℝ => u m θ) ((S.circle (3 / 4 : ℝ)).decode.map_add e q)
    _ = (η - a) + (S.circle (3 / 4 : ℝ)).decode c m η :=
      congrArg₂ (fun x y : ℝ => x + y) he hq
    _ = _ := by rw [hleft]; ring

theorem N01Properties.smoothTameOn_n04MinusFirstIntegralCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) :
    SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (hN.n04MinusFirstIntegralCircle hS hT χ hχrange rsel hrsel) := by
  have he := hN.smoothTameOn_n04CorrectedFlowInverseCircle hS hT χ hχrange rsel hrsel
  have hc : SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun z : StateDirections S × ℝ => z.1.val.2.2.2) :=
    smoothTameOn_restrict_open (smoothTameOn_sectorChart S)
      (sectorNeighborhood_isOpen S base ε ε) (subset_univ _)
  have hcomp := smoothTameOn_circleShiftedChartCompose_maps
    (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
    (fun m => opticalTravel D.w (C.left m) (rsel m))
    (sectorPairGrading_monotone S) (sectorPairGrading_withSeminorms S)
    (sectorNeighborhood_isOpen S base ε ε) he hc
  simpa only [n04MinusFirstIntegralCircle] using
    smoothTameOn_add (sectorPairGrading_monotone S) he hcomp

def N01Properties.n04MinusFirstIntegralSelector_jointTower
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) (m : ℕ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun p : (StateDirections S × ℝ) × ℝ => n04bMinusFirstIntegral
        (fun q => returnCorrectedMinusFlow S C χ (liftSectorParameter S C p.1) m q.1 q.2)
        (stateLeftChart S (liftSectorParameter S C p.1).1 m) (rsel m, p.2)) := by
  let J : SmoothDirections (sectorNeighborhood S base ε ε)
      (hN.n04MinusFirstIntegralCircle hS hT χ hχrange rsel hrsel) :=
    (hN.smoothTameOn_n04MinusFirstIntegralCircle hS hT χ hχrange rsel hrsel).choose
  have hH (j : ℕ) : 0 < T.H (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 j)).2.1
  let travel : ℕ → ℝ := fun j => opticalTravel D.w (C.left j) (rsel j)
  let K := circleAffineLiftJointDirections (hS.2.1 (3 / 4 : ℝ)) hH J travel m
  apply K.congrOn
  intro p hp
  let a : ℝ := p.2 + travel m
  let b : ℝ := n04bMinusFirstIntegral
    (fun q => returnCorrectedMinusFlow S C χ (liftSectorParameter S C p.1) m q.1 q.2)
    (stateLeftChart S (liftSectorParameter S C p.1).1 m) (rsel m, p.2)
  have hd : (S.circle (3 / 4 : ℝ)).decode
      (hN.n04MinusFirstIntegralCircle hS hT χ hχrange rsel hrsel p.1) m p.2 = b - a :=
    hN.n04MinusFirstIntegralCircle_decode hS hT χ hχrange rsel hrsel p.1 hp.1 m p.2
  exact (congrArg (fun y : ℝ => a + y) hd).trans
    ((add_comm a (b - a)).trans (sub_add_cancel b a))

end ContinuousFlexibility.Statements
