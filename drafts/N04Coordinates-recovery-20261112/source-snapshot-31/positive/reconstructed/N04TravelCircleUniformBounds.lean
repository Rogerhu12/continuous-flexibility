import ContinuousFlexibility.Analysis.N04TravelChartCircle
import ContinuousFlexibility.Analysis.N01ReturnVelocityUniformBounds

/-!
# Uniform estimates for the same actual first-integral circle

The original flow's common angular bound gives a uniform positive slope
for its actual corrected composition. The existing inverse and circle
operations then estimate the already defined first-integral displacement,
uniformly in every closed-radius selector. No inverse, cutoff or circle
representative is selected again.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

local instance n04TravelCircleUniformStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {I : Type*} {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hflow : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m r,
    r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ∧
      deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ≤ 3 / 2)

include hflow in
theorem N01Properties.n04CorrectedFlowCircle_uniform_lower
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (θ : ℝ) :
    1 / 24 ≤ 1 + deriv ((S.circle (3 / 4 : ℝ)).decode
      (hN.n04CorrectedFlowCircle hS hT χ hχrange rsel hrsel z) m) θ := by
  let initial : ℝ → ℝ := returnInterpolation (χ m (rsel m))
    (returnCorrectionInitialMap S C (liftSectorParameter S C z) m)
  let flow : ℝ → ℝ := C.minusFlow (liftSectorParameter S C z) m (rsel m)
  have hi : 1 / 12 ≤ deriv initial θ := by
    have h := hN.interpolationSelectorCircle_uniform_lower hS hT hflow
      χ hχrange rsel hrsel z hz m θ
    rw [← circleAffineLift_deriv (hS.2.1 (3 / 4 : ℝ)) (fun _ => 0),
      hN.interpolationSelectorCircle_lift hS hT χ hχrange rsel hrsel z hz m] at h
    exact h
  have hf : 1 / 2 ≤ deriv flow (initial θ) :=
    (hflow z hz m (rsel m) (hrsel m) (initial θ)).1
  have hiPos : 0 < deriv initial θ := (by norm_num : (0 : ℝ) < 1 / 12).trans_le hi
  have hfPos : 0 < deriv flow (initial θ) := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hf
  have hc := (differentiableAt_of_deriv_ne_zero hfPos.ne').hasDerivAt.comp θ
    (differentiableAt_of_deriv_ne_zero hiPos.ne').hasDerivAt
  have heq : returnCorrectedMinusFlow S C χ (liftSectorParameter S C z)
      m (rsel m) = flow ∘ initial := rfl
  have hd : deriv (returnCorrectedMinusFlow S C χ (liftSectorParameter S C z)
      m (rsel m)) θ = deriv flow (initial θ) * deriv initial θ := by
    rw [heq]
    exact hc.deriv
  rw [← circleAffineLift_deriv (hS.2.1 (3 / 4 : ℝ))
    (fun j => -opticalTravel D.w (C.left j) (rsel j)),
    hN.n04CorrectedFlowCircle_affineLift hS hT χ hχrange rsel hrsel z hz, hd]
  have hm := mul_le_mul hf hi (by norm_num : (0 : ℝ) ≤ 1 / 12) hfPos.le
  norm_num at hm
  exact hm

include hflow in
theorem N01Properties.uniformSmoothFamilyOn_n04CorrectedFlowCircle
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    UniformSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun i => hN.n04CorrectedFlowCircle hS hT χ hχrange (rsel i) (hrsel i)) := by
  have hi := hN.uniformSmoothFamilyOn_interpolationSelectorCircle
    hS hT hflow χ hχrange rsel hrsel
  have hf := hN.uniformSmoothFamilyOn_endpointFlowCircle hS hT rsel hrsel
  have hc := uniformSmoothFamilyOn_circleCompose_maps
    (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ : I => fun _ => 0)
    (sectorPairGrading_monotone S) (sectorNeighborhood_isOpen S base ε ε) hi hf
  exact hi.add (sectorPairGrading_monotone S) hc

include hflow in
theorem N01Properties.uniformSmoothFamilyOn_n04CorrectedFlowInverseCircle
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    UniformSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun i => hN.n04CorrectedFlowInverseCircle hS hT χ hχrange (rsel i) (hrsel i)) := by
  let H := S.circle (3 / 4 : ℝ)
  letI : ContinuousNeg H.Space :=
    (withSeminorms_graded (fun n => H.level n) H.bond).isTopologicalAddGroup.toContinuousNeg
  have hf := hN.uniformSmoothFamilyOn_n04CorrectedFlowCircle
    hS hT hflow χ hχrange rsel hrsel
  have hi := uniformSmoothFamilyOn_circleInverse_maps
    (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
    (fun i m => -opticalTravel D.w (C.left m) (rsel i m))
    (1 / 24) (by norm_num) (sectorPairGrading_monotone S)
    (sectorNeighborhood_isOpen S base ε ε)
    (fun i z hz m θ => hN.n04CorrectedFlowCircle_uniform_lower hS hT hflow
      χ hχrange (rsel i) (hrsel i) z hz m θ) hf hf
  exact hi.neg (sectorPairGrading_monotone S)

include hflow in
theorem N01Properties.uniformSmoothFamilyOn_n04MinusFirstIntegralCircle
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    UniformSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun i => hN.n04MinusFirstIntegralCircle hS hT χ hχrange (rsel i) (hrsel i)) := by
  have he := hN.uniformSmoothFamilyOn_n04CorrectedFlowInverseCircle
    hS hT hflow χ hχrange rsel hrsel
  have hl := uniformSmoothFamilyOn_sectorChart (I := I) S base ε
  have hc := uniformSmoothFamilyOn_circleCompose_maps
    (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
    (fun i m => opticalTravel D.w (C.left m) (rsel i m))
    (sectorPairGrading_monotone S) (sectorNeighborhood_isOpen S base ε ε) he hl
  exact he.add (sectorPairGrading_monotone S) hc

include hflow in
theorem N01Properties.uniformSmoothFamilyOn_n04TravelChartCircle
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m))
    (side : Bool) :
    UniformSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun i => hN.n04TravelChartCircle hS hT χ hχrange (rsel i) (hrsel i) side) := by
  have he := hN.uniformSmoothFamilyOn_n04MinusFirstIntegralCircle
    hS hT hflow χ hχrange rsel hrsel
  cases side with
  | false => exact he.postTameContinuousLinear (sectorPairGrading_monotone S)
      (circleModelEvenProjection (hS.2.1 (3 / 4 : ℝ)))
      (circleModelEvenProjection_isTame (hS.2.1 (3 / 4 : ℝ)))
  | true => exact he.postTameContinuousLinear (sectorPairGrading_monotone S)
      (circleModelOddProjection (hS.2.1 (3 / 4 : ℝ)))
      (circleModelOddProjection_isTame (hS.2.1 (3 / 4 : ℝ)))

include hflow in
/-- The chosen genuine family precedes all derivative orders. The low
box index and derivative loss may depend on the parameter order, and
both are fixed before the spatial grading and every radius selector. -/
theorem N01Properties.n04TravelChartCircle_uniform_oneHigh
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m))
    (side : Bool)
    (J : ∀ i, SmoothDirections (sectorNeighborhood S base ε ε)
      (hN.n04TravelChartCircle hS hT χ hχrange (rsel i) (hrsel i) side)) :
    ∀ n : ℕ, ∃ B δ : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ i z, z ∈ sectorNeighborhood S base ε ε →
        pairGrading (sectorGrading S) realGrading B z ≤ R →
      ∀ v : Fin n → StateDirections S × ℝ,
        (S.circle (3 / 4 : ℝ)).grading s ((J i).D n z v) ≤ K *
          tameJetSize (pairGrading (sectorGrading S) realGrading) n s δ B z v :=
  ((hN.uniformSmoothFamilyOn_n04TravelChartCircle
    hS hT hflow χ hχrange rsel hrsel side).jets J).oneHigh

end ContinuousFlexibility.Statements
