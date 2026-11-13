import ContinuousFlexibility.Analysis.N04NegativeChartReturnCircleBounds
import ContinuousFlexibility.Analysis.N04NegativeGeometryCorrectedFlowInverseCircle
import ContinuousFlexibility.Analysis.N04bCharacteristicFirstIntegrals

/-!
# Fixed-base bounds for the actual interior first integral

The actual corrected flow is the ordinary flow composed with its supplied
cutoff interpolation. Their existing lower angular bounds give the common
lower bound `1 / 24`. Its actual inverse, followed by the actual left chart,
has a circle displacement relative to the reference optical translation.
The estimates are uniform in every closed-radius selector.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

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

variable {I : Type*} {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (χ : ℕ → ℝ → ℝ)
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
  (hflow : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m r,
    r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ∧
      deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ≤ 3 / 2)

include hflow in
theorem N01Properties.n04NegativeChart_correctedFlowCircle_uniform_lower
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) (m : ℕ) (θ : ℝ) :
    1 / 24 ≤ 1 + deriv ((S.circle (3 / 4 : ℝ)).decode
      (hN.n04NegativeGeometryCorrectedFlowCircle hS hT χ hχrange rsel hrsel z) m) θ := by
  rw [← circleAffineLift_deriv (hS.2.1 (3 / 4 : ℝ))
    (fun j => -opticalTravel D.w (C.left j) (rsel j)),
    hN.n04NegativeGeometryCorrectedFlowCircle_affineLift hS hT χ hχrange rsel hrsel z hz]
  let initial : ℝ → ℝ := returnInterpolation (χ m (rsel m))
    (returnCorrectionInitialMap S C (liftSectorParameter S C z) m)
  let flow : ℝ → ℝ := C.minusFlow (liftSectorParameter S C z) m (rsel m)
  have hi : 1 / 12 ≤ deriv initial θ := by
    have h := hN.interpolationSelectorCircle_uniform_lower hS hT hflow χ hχrange
      rsel hrsel z hz m θ
    rw [← circleAffineLift_deriv (hS.2.1 (3 / 4 : ℝ)) (fun _ => 0),
      hN.interpolationSelectorCircle_lift hS hT χ hχrange rsel hrsel z hz m] at h
    exact h
  have hf : 1 / 2 ≤ deriv flow (initial θ) :=
    (hflow z hz m (rsel m) (hrsel m) (initial θ)).1
  have hip : 0 < deriv initial θ := (by norm_num : (0 : ℝ) < 1 / 12).trans_le hi
  have hfp : 0 < deriv flow (initial θ) := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hf
  have hc : HasDerivAt (fun t => flow (initial t))
      (deriv flow (initial θ) * deriv initial θ) θ :=
    (differentiableAt_of_deriv_ne_zero hfp.ne').hasDerivAt.comp θ
      (differentiableAt_of_deriv_ne_zero hip.ne').hasDerivAt
  change 1 / 24 ≤ deriv (fun t => flow (initial t)) θ
  rw [hc.deriv]
  exact (by norm_num : (1 / 24 : ℝ) = (1 / 2) * (1 / 12)).trans_le
    (mul_le_mul hf hi (by norm_num) hfp.le)

include hflow in
theorem N01Properties.n04FixedBase_correctedFlowCircle
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    N04FixedBaseSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun i => hN.n04NegativeGeometryCorrectedFlowCircle hS hT χ hχrange (rsel i) (hrsel i)) := by
  have he := hN.n04FixedBase_interpolationSelectorCircle hS hT hflow χ hχrange rsel hrsel
  have hf := hN.n04FixedBase_endpointFlowCircle hS hT rsel hrsel
  have hc := n04FixedBaseSmoothFamilyOn_circleCompose_maps (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1
    (by norm_num) (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ : I => fun _ => 0)
    (sectorPairGrading_monotone S) (n04FixedBase_sectorParameter_hasInterpolation hS)
    (sectorNeighborhood_isOpen S base ε ε) he hf
  exact he.add (sectorPairGrading_monotone S) hc

include hflow in
theorem N01Properties.n04FixedBase_correctedFlowInverseCircle
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    N04FixedBaseSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun i => hN.n04NegativeGeometryCorrectedFlowInverseCircle
        hS hT χ hχrange (rsel i) (hrsel i)) := by
  have hf := hN.n04FixedBase_correctedFlowCircle hS hT χ hχrange hflow rsel hrsel
  have hi := n04FixedBaseSmoothFamilyOn_circleInverse_maps (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1
    (by norm_num) (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
    (fun i m => -opticalTravel D.w (C.left m) (rsel i m)) (1 / 24) (by norm_num)
    (sectorPairGrading_monotone S) (n04FixedBase_sectorParameter_hasInterpolation hS)
    (sectorNeighborhood_isOpen S base ε ε)
    (fun i z hz m θ => hN.n04NegativeChart_correctedFlowCircle_uniform_lower
      hS hT χ hχrange hflow (rsel i) (hrsel i) z hz m θ) hf hf
  exact hi.neg

/-- The all-component displacement of the actual minus first integral,
centered by its reference optical translation. -/
def N01Properties.n04NegativeChartMinusFirstIntegralSelectorCircle
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) : CircleSpace S :=
  hN.n04NegativeGeometryCorrectedFlowInverseCircle hS hT χ hχrange rsel hrsel z +
    circlePositiveInverseComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
      (fun m => -opticalTravel D.w (C.left m) (rsel m))
      (hN.n04NegativeGeometryCorrectedFlowCircle hS hT χ hχrange rsel hrsel z) z.1.val.2.2.2

theorem N01Properties.n04NegativeChartMinusFirstIntegralSelectorCircle_decode
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
      (hN.n04NegativeChartMinusFirstIntegralSelectorCircle hS hT χ hχrange rsel hrsel z) m θ =
      n04bMinusFirstIntegral
        (fun p => returnCorrectedMinusFlow S C χ (liftSectorParameter S C z) m p.1 p.2)
        (stateLeftChart S (liftSectorParameter S C z).1 m) (rsel m, θ) -
          (θ + opticalTravel D.w (C.left m) (rsel m)) := by
  let H := S.circle (3 / 4 : ℝ)
  let u : ℝ := Function.invFun
    (returnCorrectedMinusFlow S C χ (liftSectorParameter S C z) m (rsel m)) θ
  let travel : ℕ → ℝ := fun j => -opticalTravel D.w (C.left j) (rsel j)
  let e : CircleSpace S := hN.n04NegativeGeometryCorrectedFlowCircle hS hT χ hχrange rsel hrsel z
  let q : CircleSpace S := circlePositiveInverseComposeLinear (hS.2.1 (3 / 4 : ℝ))
    hT hN.1.1 (by norm_num) travel e z.1.val.2.2.2
  have hpos : e ∈ circlePositiveLiftDomain H :=
    hN.n04NegativeGeometryCorrectedFlowCircle_mem_positiveLiftDomain
      hS hT χ hχrange rsel hrsel z hz
  have hi : H.decode (hN.n04NegativeGeometryCorrectedFlowInverseCircle
      hS hT χ hχrange rsel hrsel z) m θ =
      u - (θ + opticalTravel D.w (C.left m) (rsel m)) :=
    congrArg (fun w : ℕ → ℝ → ℝ => w m θ)
      (hN.n04NegativeGeometryCorrectedFlowInverseCircle_decode hS hT χ hχrange rsel hrsel z hz)
  have hinv : circleAffineInverse travel e m θ = u :=
    congrArg (fun w : ℕ → ℝ → ℝ => w m θ)
      (hN.n04NegativeGeometryCorrectedFlowCircle_affineInverse hS hT χ hχrange rsel hrsel z hz)
  have hq : H.decode q m θ = H.decode z.1.val.2.2.2 m u :=
    (congrArg (fun w : ℕ → ℝ → ℝ => w m θ)
      (circlePositiveInverseComposeLinear_decode (hS.2.1 (3 / 4 : ℝ))
        hT hN.1.1 (by norm_num) travel e z.1.val.2.2.2 hpos)).trans
      (congrArg (H.decode z.1.val.2.2.2 m) hinv)
  have hs : H.decode
      (hN.n04NegativeChartMinusFirstIntegralSelectorCircle hS hT χ hχrange rsel hrsel z) m θ =
      (u - (θ + opticalTravel D.w (C.left m) (rsel m))) + H.decode z.1.val.2.2.2 m u :=
    (congrArg (fun w : ℕ → ℝ → ℝ => w m θ)
      (H.decode.map_add (hN.n04NegativeGeometryCorrectedFlowInverseCircle
        hS hT χ hχrange rsel hrsel z) q)).trans
      (congrArg₂ (fun a b : ℝ => a + b) hi hq)
  have hl : stateLeftChart S (liftSectorParameter S C z).1 m u =
      u + H.decode z.1.val.2.2.2 m u := hN.2.2.1.sector_leftChart z m u
  calc
    _ = (u - (θ + opticalTravel D.w (C.left m) (rsel m))) + H.decode z.1.val.2.2.2 m u := hs
    _ = (u + H.decode z.1.val.2.2.2 m u) -
        (θ + opticalTravel D.w (C.left m) (rsel m)) := by ring
    _ = stateLeftChart S (liftSectorParameter S C z).1 m u -
        (θ + opticalTravel D.w (C.left m) (rsel m)) :=
      congrArg (fun a : ℝ => a - (θ + opticalTravel D.w (C.left m) (rsel m))) hl.symm
    _ = _ := rfl

include hflow in
theorem N01Properties.n04FixedBase_minusFirstIntegralSelectorCircle
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    N04FixedBaseSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun i => hN.n04NegativeChartMinusFirstIntegralSelectorCircle
        hS hT χ hχrange (rsel i) (hrsel i)) := by
  have hf := hN.n04FixedBase_correctedFlowCircle hS hT χ hχrange hflow rsel hrsel
  have hi := hN.n04FixedBase_correctedFlowInverseCircle hS hT χ hχrange hflow rsel hrsel
  have hl := n04FixedBase_sectorChart (I := I) S base ε
  have hc := n04FixedBaseSmoothFamilyOn_circleInverse_maps (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1
    (by norm_num) (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
    (fun i m => -opticalTravel D.w (C.left m) (rsel i m)) (1 / 24) (by norm_num)
    (sectorPairGrading_monotone S) (n04FixedBase_sectorParameter_hasInterpolation hS)
    (sectorNeighborhood_isOpen S base ε ε)
    (fun i z hz m θ => hN.n04NegativeChart_correctedFlowCircle_uniform_lower
      hS hT χ hχrange hflow (rsel i) (hrsel i) z hz m θ) hf hl
  exact hi.add (sectorPairGrading_monotone S) hc

end ContinuousFlexibility.Statements
