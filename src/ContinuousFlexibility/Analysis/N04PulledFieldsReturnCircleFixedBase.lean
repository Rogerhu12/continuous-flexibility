import ContinuousFlexibility.Analysis.N04PulledFieldsCircleFixedBaseOperations
import ContinuousFlexibility.Analysis.N04PulledFieldsSelectorFixedBase

/-!
# One common low base for the actual return-circle formulas

The endpoint flow, transported odd/even chart, actual residual, inverse
return coordinate, and averaged divided difference are their existing
N01 objects. Every step uses a strong seed or a fixed-base closure lemma.
The common first-angular-derivative bound is the same hypothesis already
provided by the retained uniform inverse neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

local instance n04PulledFieldsReturnCircleFixedBaseStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {I : Type*} {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)

theorem N01Properties.n04PulledFields_fixedBase_endpointFlowCircle
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    N04PulledFieldsFixedBaseFamily (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun i => hN.endpointFlowCircle hS hT (rsel i) (hrsel i)) := by
  let J := fun i => (hN.exists_endpointFlowCircle_smoothDirections hS hT (rsel i) (hrsel i)).choose
  let data := hN.endpointFlowCircle_fixedBase_oneHigh hS hT
  refine ⟨J, data.choose, fun n => (data.choose_spec.2 n).choose, fun n R hR s => ?_⟩
  let estimate := (data.choose_spec.2 n).choose_spec R hR s
  exact ⟨estimate.choose, estimate.choose_spec.1,
    fun i => estimate.choose_spec.2 (rsel i) (hrsel i) (J i)⟩

theorem n04PulledFields_fixedBase_sectorChart (S : PhysicalSpacesData) (base : ℕ) (ε : ℝ) :
    N04PulledFieldsFixedBaseFamily (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun (_ : I) (z : StateDirections S × ℝ) => z.1.val.2.2.2) :=
  n04PulledFields_fixedBaseFamily_linear (sectorNeighborhood_isOpen S base ε ε)
    (fun _ : I => sectorChartContinuousLinear S) 0
    (fun s => ⟨1, zero_le_one, fun _ z => by
      simpa only [Nat.add_zero, one_mul, sectorChartContinuousLinear_apply] using
        sectorParameter_chart_grading_le S s z⟩)

variable
  (hflow : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m r,
    r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ∧
      deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ≤ 3 / 2)

include hflow

theorem N01Properties.n04PulledFields_fixedBase_sectorReturnTransportCircle :
    N04PulledFieldsFixedBaseFamily (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun _ : I => hN.sectorReturnTransportCircle hS hT) := by
  have hf := hN.n04PulledFields_fixedBase_endpointFlowCircle hS hT
    (fun _ : I => C.right) (fun _ => hN.right_radius_mem)
  have hl := n04PulledFields_fixedBase_sectorChart (I := I) S base ε
  exact n04PulledFields_fixedBase_circleInverse_maps hN.1.1 hT (by norm_num)
    (hS.2.1 (3 / 4 : ℝ)) (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
    (fun _ m => -C.travel m) (1 / 2) (by norm_num) (sectorPairGrading_monotone S)
    (n04PulledFields_selectorParameterInterpolation hS)
    (sectorNeighborhood_isOpen S base ε ε)
    (fun _ z hz m θ => hN.endpointFlowCircle_uniform_lower hS hT hflow
      C.right hN.right_radius_mem z hz m θ) hf (hl.sub (sectorPairGrading_monotone S) hf)

theorem N01Properties.n04PulledFields_fixedBase_sectorReturnResidualCircle :
    N04PulledFieldsFixedBaseFamily (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun _ : I => hN.sectorReturnResidualCircle hS hT) := by
  let hH := hS.2.1 (3 / 4 : ℝ)
  have hu := hN.n04PulledFields_fixedBase_sectorReturnTransportCircle (I := I) hS hT hflow
  have ho := hu.postTameContinuousLinear (circleOddContinuousLinear hH) (circleOddLinear_tame hH)
  have he := hu.postTameContinuousLinear (circleEvenContinuousLinear hH) (circleEvenLinear_tame hH)
  exact n04PulledFields_fixedBase_circleInverse_maps hN.1.1 hT (by norm_num) hH
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ _ => 0) (1 / 3) (by norm_num)
    (sectorPairGrading_monotone S) (n04PulledFields_selectorParameterInterpolation hS)
    (sectorNeighborhood_isOpen S base ε ε)
    (fun _ z hz m θ => hN.transportedOddCircle_uniform_lower hS hT hflow z hz m θ) ho he

theorem N01Properties.n04PulledFields_fixedBase_rightChartInverseCircle :
    N04PulledFieldsFixedBaseFamily (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun _ : I => hN.rightChartInverseCircle hS hT) := by
  let H := S.circle (3 / 4 : ℝ)
  let hH := hS.2.1 (3 / 4 : ℝ)
  letI : ContinuousNeg H.Space :=
    (withSeminorms_graded (fun n => H.level n) H.bond).isTopologicalAddGroup.toContinuousNeg
  have hu := hN.n04PulledFields_fixedBase_sectorReturnTransportCircle (I := I) hS hT hflow
  have ho := hu.postTameContinuousLinear (circleOddContinuousLinear hH) (circleOddLinear_tame hH)
  have hi := n04PulledFields_fixedBase_circleInverse_maps hN.1.1 hT (by norm_num) hH
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ : I => fun _ => 0) (1 / 3) (by norm_num)
    (sectorPairGrading_monotone S) (n04PulledFields_selectorParameterInterpolation hS)
    (sectorNeighborhood_isOpen S base ε ε)
    (fun _ z hz m θ => hN.transportedOddCircle_uniform_lower hS hT hflow z hz m θ) ho ho
  exact hi.neg

theorem N01Properties.n04PulledFields_fixedBase_selectorInverseCircle
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    N04PulledFieldsFixedBaseFamily (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun i => hN.selectorInverseCircle hS hT (rsel i) (hrsel i)) := by
  let J := (hN.uniformSmoothFamilyOn_selectorInverseCircle hS hT hflow rsel hrsel).choose
  let data := hN.n04PulledFields_selectorInverseCircle_fixedBase_oneHigh hS hT hflow
  refine ⟨J, data.choose, fun n => (data.choose_spec.2 n).choose, fun n R hR s => ?_⟩
  let estimate := (data.choose_spec.2 n).choose_spec R hR s
  exact ⟨estimate.choose, estimate.choose_spec.1,
    fun i => estimate.choose_spec.2 (rsel i) (hrsel i) (J i)⟩

theorem N01Properties.n04PulledFields_fixedBase_returnTransportInverseCircle :
    N04PulledFieldsFixedBaseFamily (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun _ : I => hN.returnTransportInverseCircle hS hT) := by
  have hr := hN.n04PulledFields_fixedBase_rightChartInverseCircle (I := I) hS hT hflow
  have hf := hN.n04PulledFields_fixedBase_selectorInverseCircle hS hT hflow
    (fun _ : I => C.right) (fun _ => hN.right_radius_mem)
  have hc := n04PulledFields_fixedBase_circleCompose_maps hN.1.1 hT (by norm_num)
    (hS.2.1 (3 / 4 : ℝ)) (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ : I => fun _ => 0)
    (sectorPairGrading_monotone S) (n04PulledFields_selectorParameterInterpolation hS)
    (sectorNeighborhood_isOpen S base ε ε) hr hf
  exact hr.add (sectorPairGrading_monotone S) hc

theorem N01Properties.n04PulledFields_fixedBase_returnCorrectionInitialCircle :
    N04PulledFieldsFixedBaseFamily (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun _ : I => hN.returnCorrectionInitialCircle hS hT) := by
  have hl := n04PulledFields_fixedBase_sectorChart (I := I) S base ε
  have hg := hN.n04PulledFields_fixedBase_returnTransportInverseCircle (I := I) hS hT hflow
  have hc := n04PulledFields_fixedBase_circleCompose_maps hN.1.1 hT (by norm_num)
    (hS.2.1 (3 / 4 : ℝ)) (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ : I => fun m => -C.travel m)
    (sectorPairGrading_monotone S) (n04PulledFields_selectorParameterInterpolation hS)
    (sectorNeighborhood_isOpen S base ε ε) hl hg
  exact hl.add (sectorPairGrading_monotone S) hc

theorem N01Properties.n04PulledFields_fixedBase_rightReturnChartCircle :
    N04PulledFieldsFixedBaseFamily (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun _ : I => hN.rightReturnChartCircle hS hT) := by
  let hH := hS.2.1 (3 / 4 : ℝ)
  have hf := hN.n04PulledFields_fixedBase_endpointFlowCircle hS hT
    (fun _ : I => C.right) (fun _ => hN.right_radius_mem)
  have hu := hN.n04PulledFields_fixedBase_sectorReturnTransportCircle (I := I) hS hT hflow
  have ho := hu.postTameContinuousLinear (circleOddContinuousLinear hH) (circleOddLinear_tame hH)
  have hc := n04PulledFields_fixedBase_circleCompose_maps hN.1.1 hT (by norm_num) hH
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ : I => fun m => -C.travel m)
    (sectorPairGrading_monotone S) (n04PulledFields_selectorParameterInterpolation hS)
    (sectorNeighborhood_isOpen S base ε ε) hf ho
  exact hf.add (sectorPairGrading_monotone S) hc

theorem N01Properties.n04PulledFields_fixedBase_returnCorrectionDslopeCircle :
    N04PulledFieldsFixedBaseFamily (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun _ : I => hN.returnCorrectionDslopeCircle hS hT) := by
  let hH := hS.2.1 (3 / 4 : ℝ)
  have he := hN.n04PulledFields_fixedBase_sectorReturnResidualCircle (I := I) hS hT hflow
  have hg := hN.n04PulledFields_fixedBase_returnTransportInverseCircle (I := I) hS hT hflow
  have hd := (hg.postTameContinuousLinear (circleDerivativeContinuousLinear hH)
    (circleDerivativeLinear_isTame hH)).congr
      (fun _ z _ => circleDerivativeContinuousLinear_apply hH
        (hN.returnTransportInverseCircle hS hT z))
  exact n04PulledFields_fixedBase_circleAverage_maps hN.1.1 hT (by norm_num) hH
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ _ => 0)
    (sectorPairGrading_monotone S) (n04PulledFields_selectorParameterInterpolation hS)
    (sectorNeighborhood_isOpen S base ε ε) he hd

end ContinuousFlexibility.Statements
