import ContinuousFlexibility.Analysis.N04NegativeChartCircleFixedBaseCalculus
import ContinuousFlexibility.Analysis.N01ReturnVelocityUniformBounds
import ContinuousFlexibility.Analysis.N04EndpointCircleFixedBaseBounds

/-!
# A common base for the actual return and interpolation maps

Every map below is the existing N01 circle-valued map. The endpoint-flow
estimate, the left-chart projection, and the finite fixed-base circle
calculus give one low order before all state orders and radius selectors.
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

theorem N01Properties.n04FixedBase_endpointFlowCircle
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    N04FixedBaseSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun i => hN.endpointFlowCircle hS hT (rsel i) (hrsel i)) := by
  let J := fun i => (hN.exists_endpointFlowCircle_smoothDirections hS hT (rsel i) (hrsel i)).choose
  let data := hN.endpointFlowCircle_fixedBase_oneHigh hS hT
  refine ⟨J, data.choose, fun n => ?_⟩
  let orderData := data.choose_spec.2 n
  refine ⟨orderData.choose, fun R hR s => ?_⟩
  let estimate := orderData.choose_spec R hR s
  exact ⟨estimate.choose, estimate.choose_spec.1, fun i x hx hlow v =>
    estimate.choose_spec.2 (rsel i) (hrsel i) (J i) x hx hlow v⟩

theorem n04FixedBase_sectorChart (S : PhysicalSpacesData) (base : ℕ) (ε : ℝ) :
    N04FixedBaseSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun (_ : I) (z : StateDirections S × ℝ) => z.1.val.2.2.2) :=
  n04FixedBaseSmoothFamilyOn_linear (sectorNeighborhood_isOpen S base ε ε)
    (fun _ : I => sectorChartContinuousLinear S) 0
    (fun s => ⟨1, zero_le_one, fun _ z => by
      simpa only [Nat.add_zero, one_mul, sectorChartContinuousLinear_apply] using
        sectorParameter_chart_grading_le S s z⟩)

theorem N01Properties.n04FixedBase_returnFlowCircle :
    N04FixedBaseSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun _ : I => hN.returnFlowCircle hS hT) :=
  hN.n04FixedBase_endpointFlowCircle hS hT (fun _ : I => C.right)
    (fun _ => hN.right_radius_mem)

variable
  (hflow : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m r,
    r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ∧
      deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ≤ 3 / 2)

include hflow in
theorem N01Properties.n04FixedBase_sectorReturnTransportCircle :
    N04FixedBaseSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun _ : I => hN.sectorReturnTransportCircle hS hT) := by
  have hf := hN.n04FixedBase_returnFlowCircle (I := I) hS hT
  have hl := n04FixedBase_sectorChart (I := I) S base ε
  exact n04FixedBaseSmoothFamilyOn_circleInverse_maps (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1
    (by norm_num) (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ m => -C.travel m)
    (1 / 2) (by norm_num) (sectorPairGrading_monotone S)
    (n04FixedBase_sectorParameter_hasInterpolation hS)
    (sectorNeighborhood_isOpen S base ε ε)
    (fun _ z hz m θ => hN.endpointFlowCircle_uniform_lower hS hT hflow
      C.right hN.right_radius_mem z hz m θ) hf (hl.sub (sectorPairGrading_monotone S) hf)

include hflow in
theorem N01Properties.n04FixedBase_sectorReturnResidualCircle :
    N04FixedBaseSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun _ : I => hN.sectorReturnResidualCircle hS hT) := by
  let hH := hS.2.1 (3 / 4 : ℝ)
  have hu := hN.n04FixedBase_sectorReturnTransportCircle (I := I) hS hT hflow
  have ho := hu.postTameContinuousLinear (circleOddContinuousLinear hH) (circleOddLinear_tame hH)
  have he := hu.postTameContinuousLinear (circleEvenContinuousLinear hH) (circleEvenLinear_tame hH)
  exact n04FixedBaseSmoothFamilyOn_circleInverse_maps hH hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ _ => 0) (1 / 3) (by norm_num)
    (sectorPairGrading_monotone S) (n04FixedBase_sectorParameter_hasInterpolation hS)
    (sectorNeighborhood_isOpen S base ε ε)
    (fun _ z hz m θ => hN.transportedOddCircle_uniform_lower hS hT hflow z hz m θ) ho he

include hflow in
theorem N01Properties.n04FixedBase_rightChartInverseCircle :
    N04FixedBaseSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun _ : I => hN.rightChartInverseCircle hS hT) := by
  let hH := hS.2.1 (3 / 4 : ℝ)
  have hu := hN.n04FixedBase_sectorReturnTransportCircle (I := I) hS hT hflow
  have ho := hu.postTameContinuousLinear (circleOddContinuousLinear hH) (circleOddLinear_tame hH)
  have hi := n04FixedBaseSmoothFamilyOn_circleInverse_maps hH hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ : I => fun _ => 0) (1 / 3) (by norm_num)
    (sectorPairGrading_monotone S) (n04FixedBase_sectorParameter_hasInterpolation hS)
    (sectorNeighborhood_isOpen S base ε ε)
    (fun _ z hz m θ => hN.transportedOddCircle_uniform_lower hS hT hflow z hz m θ) ho ho
  exact hi.neg

include hflow in
theorem N01Properties.n04FixedBase_selectorInverseCircle
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    N04FixedBaseSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun i => hN.selectorInverseCircle hS hT (rsel i) (hrsel i)) := by
  have hf := hN.n04FixedBase_endpointFlowCircle hS hT rsel hrsel
  have hi := n04FixedBaseSmoothFamilyOn_circleInverse_maps (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1
    (by norm_num) (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
    (fun i m => -opticalTravel D.w (C.left m) (rsel i m))
    (1 / 2) (by norm_num) (sectorPairGrading_monotone S)
    (n04FixedBase_sectorParameter_hasInterpolation hS)
    (sectorNeighborhood_isOpen S base ε ε)
    (fun i z hz m θ => hN.endpointFlowCircle_uniform_lower hS hT hflow
      (rsel i) (hrsel i) z hz m θ) hf hf
  exact hi.neg

include hflow in
theorem N01Properties.n04FixedBase_returnTransportInverseCircle :
    N04FixedBaseSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun _ : I => hN.returnTransportInverseCircle hS hT) := by
  have hr := hN.n04FixedBase_rightChartInverseCircle (I := I) hS hT hflow
  have hf := hN.n04FixedBase_selectorInverseCircle hS hT hflow
    (fun _ : I => C.right) (fun _ => hN.right_radius_mem)
  have hc := n04FixedBaseSmoothFamilyOn_circleCompose_maps (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1
    (by norm_num) (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ : I => fun _ => 0)
    (sectorPairGrading_monotone S) (n04FixedBase_sectorParameter_hasInterpolation hS)
    (sectorNeighborhood_isOpen S base ε ε) hr hf
  exact hr.add (sectorPairGrading_monotone S) hc

include hflow in
theorem N01Properties.n04FixedBase_returnCorrectionInitialCircle :
    N04FixedBaseSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun _ : I => hN.returnCorrectionInitialCircle hS hT) := by
  have hl := n04FixedBase_sectorChart (I := I) S base ε
  have hg := hN.n04FixedBase_returnTransportInverseCircle (I := I) hS hT hflow
  have hc := n04FixedBaseSmoothFamilyOn_circleCompose_maps (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1
    (by norm_num) (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ : I => fun m => -C.travel m)
    (sectorPairGrading_monotone S) (n04FixedBase_sectorParameter_hasInterpolation hS)
    (sectorNeighborhood_isOpen S base ε ε) hl hg
  exact hl.add (sectorPairGrading_monotone S) hc

include hflow in
theorem N01Properties.n04FixedBase_rightReturnChartCircle :
    N04FixedBaseSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun _ : I => hN.rightReturnChartCircle hS hT) := by
  let hH := hS.2.1 (3 / 4 : ℝ)
  have hf := hN.n04FixedBase_returnFlowCircle (I := I) hS hT
  have hu := hN.n04FixedBase_sectorReturnTransportCircle (I := I) hS hT hflow
  have ho := hu.postTameContinuousLinear (circleOddContinuousLinear hH) (circleOddLinear_tame hH)
  have hc := n04FixedBaseSmoothFamilyOn_circleCompose_maps hH hT hN.1.1
    (by norm_num) (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ : I => fun m => -C.travel m)
    (sectorPairGrading_monotone S) (n04FixedBase_sectorParameter_hasInterpolation hS)
    (sectorNeighborhood_isOpen S base ε ε) hf ho
  exact hf.add (sectorPairGrading_monotone S) hc

include hflow in
theorem N01Properties.n04FixedBase_interpolationSelectorCircle
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    N04FixedBaseSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun i => hN.interpolationSelectorCircle hS hT χ hχrange (rsel i) (hrsel i)) := by
  let H := S.circle (3 / 4 : ℝ)
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  have hc (i : I) : ∀ m, |χ m (rsel i m)| ≤ 1 :=
    cutoffSelector_abs_le_one χ (rsel i) hχrange (hrsel i)
  let L : I → H.Space →L[ℝ] H.Space := fun i =>
    circleComponentContractionContinuousLinear hH (fun m => χ m (rsel i m)) (hc i)
  have hK := hN.n04FixedBase_returnCorrectionInitialCircle (I := I) hS hT hflow
  have hpost := hK.postContinuousLinear L 0
    (fun s => ⟨1, zero_le_one, fun i u => by
      have happ : L i u = circleComponentContractionLinear hH
          (fun m => χ m (rsel i m)) (hc i) u :=
        circleComponentContractionContinuousLinear_apply hH (fun m => χ m (rsel i m)) (hc i) u
      have hnorm : H.grading s (L i u) ≤ H.grading s u :=
        (congrArg (H.grading s) happ).trans_le
          (circleComponentContractionLinear_grading_le hH (fun m => χ m (rsel i m)) (hc i) s u)
      simpa only [Nat.add_zero, one_mul] using hnorm⟩)
  exact hpost.congr (fun i z _ => circleComponentContractionContinuousLinear_apply hH
    (fun m => χ m (rsel i m)) (hc i) (hN.returnCorrectionInitialCircle hS hT z))

end ContinuousFlexibility.Statements
