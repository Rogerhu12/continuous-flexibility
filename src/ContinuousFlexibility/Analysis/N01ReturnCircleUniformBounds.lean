import ContinuousFlexibility.Analysis.N01FlowCircleUniformBounds
import ContinuousFlexibility.Analysis.CircleUniformFamilyOperations
import ContinuousFlexibility.Analysis.N01ReturnVelocitySmoothTame
import ContinuousFlexibility.Analysis.ReturnChartUniformBounds

/-!
# Uniform bounds for the actual return coordinates and divided difference

One common first-derivative bound for the original flow supplies the
positive constants used by every inverse. The estimates follow the
existing circle-valued definitions, through the actual transported
chart, residual, inverse coordinate and divided-difference average.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

private theorem returnCircle_uniform_neg
    {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (H : CircleModelData) {p : ℕ → Seminorm ℝ E} {U : Set E} {f : I → E → H.Space}
    (hf : UniformSmoothFamilyOn p H.grading U f) (hp : Monotone p) :
    UniformSmoothFamilyOn p H.grading U (fun i x => -f i x) := by
  exact hf.neg hp

local instance n01ReturnCircleUniformBoundsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {I : Type*} {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)

theorem N01Properties.uniformSmoothFamilyOn_endpointFlowCircle
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    UniformSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun i => hN.endpointFlowCircle hS hT (rsel i) (hrsel i)) := by
  let J := fun i => (hN.exists_endpointFlowCircle_smoothDirections hS hT (rsel i) (hrsel i)).choose
  exact ⟨J, hN.endpointFlowCircle_uniformFamilyJetBounds hS hT rsel hrsel J⟩

theorem N01Properties.uniformSmoothFamilyOn_returnFlowCircle :
    UniformSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun _ : I => hN.returnFlowCircle hS hT) :=
  hN.uniformSmoothFamilyOn_endpointFlowCircle hS hT (fun _ : I => C.right)
    (fun _ => hN.right_radius_mem)

theorem uniformSmoothFamilyOn_sectorChart (S : PhysicalSpacesData) (base : ℕ) (ε : ℝ) :
    UniformSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun (_ : I) (z : StateDirections S × ℝ) => z.1.val.2.2.2) :=
  uniformSmoothFamilyOn_linear (sectorNeighborhood_isOpen S base ε ε)
    (sectorPairGrading_monotone S) (fun _ : I => sectorChartContinuousLinear S) 0
    (fun s => ⟨1, zero_le_one, fun _ z => by
      simpa only [Nat.add_zero, one_mul, sectorChartContinuousLinear_apply] using
        sectorParameter_chart_grading_le S s z⟩)

variable
  (hflow : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m r,
    r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ∧
      deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ≤ 3 / 2)

include hflow in
theorem N01Properties.endpointFlowCircle_uniform_lower
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) (m : ℕ) (θ : ℝ) :
    1 / 2 ≤ 1 + deriv
      ((S.circle (3 / 4 : ℝ)).decode (hN.endpointFlowCircle hS hT rsel hrsel z) m) θ := by
  rw [← circleAffineLift_deriv (hS.2.1 (3 / 4 : ℝ))
    (fun j => -opticalTravel D.w (C.left j) (rsel j))]
  rw [hN.endpointFlowCircle_affineLift hS hT rsel hrsel z hz]
  exact (hflow z hz m (rsel m) (hrsel m) θ).1

include hflow in
theorem N01Properties.transportedOddCircle_uniform_lower
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) (m : ℕ) (θ : ℝ) :
    1 / 3 ≤ 1 + deriv ((S.circle (3 / 4 : ℝ)).decode
      (circleOddLinear (hS.2.1 (3 / 4 : ℝ)) (hN.sectorReturnTransportCircle hS hT z)) m) θ := by
  rw [← circleAffineLift_deriv (hS.2.1 (3 / 4 : ℝ)) (fun _ => 0),
    hN.sectorReturnTransportCircle_odd_lift hS hT z hz m]
  exact (hN.rightChartCandidate_deriv_bounds
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (hN.2.2.1.liftSectorParameter_sector z)
    (fun j t => hflow z hz j (C.right j) (hN.right_radius_mem j) t) m θ).1

include hflow in
theorem N01Properties.uniformSmoothFamilyOn_sectorReturnTransportCircle :
    UniformSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun _ : I => hN.sectorReturnTransportCircle hS hT) := by
  have hf := hN.uniformSmoothFamilyOn_returnFlowCircle (I := I) hS hT
  have hl := uniformSmoothFamilyOn_sectorChart (I := I) S base ε
  exact uniformSmoothFamilyOn_circleInverse_maps (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1
    (by norm_num) (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ m => -C.travel m)
    (1 / 2) (by norm_num) (sectorPairGrading_monotone S)
    (sectorNeighborhood_isOpen S base ε ε)
    (fun _ z hz m θ => hN.endpointFlowCircle_uniform_lower hS hT hflow
      C.right hN.right_radius_mem z hz m θ) hf (hl.sub (sectorPairGrading_monotone S) hf)

include hflow in
theorem N01Properties.uniformSmoothFamilyOn_sectorReturnResidualCircle :
    UniformSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun _ : I => hN.sectorReturnResidualCircle hS hT) := by
  let hH := hS.2.1 (3 / 4 : ℝ)
  have hu := hN.uniformSmoothFamilyOn_sectorReturnTransportCircle (I := I) hS hT hflow
  have ho := hu.postTameContinuousLinear (sectorPairGrading_monotone S)
    (circleOddContinuousLinear hH) (circleOddLinear_tame hH)
  have he := hu.postTameContinuousLinear (sectorPairGrading_monotone S)
    (circleEvenContinuousLinear hH) (circleEvenLinear_tame hH)
  exact uniformSmoothFamilyOn_circleInverse_maps hH hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ _ => 0) (1 / 3) (by norm_num)
    (sectorPairGrading_monotone S) (sectorNeighborhood_isOpen S base ε ε)
    (fun _ z hz m θ => hN.transportedOddCircle_uniform_lower hS hT hflow z hz m θ) ho he

include hflow in
theorem N01Properties.uniformSmoothFamilyOn_rightChartInverseCircle :
    UniformSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun _ : I => hN.rightChartInverseCircle hS hT) := by
  let hH := hS.2.1 (3 / 4 : ℝ)
  have hu := hN.uniformSmoothFamilyOn_sectorReturnTransportCircle (I := I) hS hT hflow
  have ho := hu.postTameContinuousLinear (sectorPairGrading_monotone S)
    (circleOddContinuousLinear hH) (circleOddLinear_tame hH)
  have hi := uniformSmoothFamilyOn_circleInverse_maps hH hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ : I => fun _ => 0) (1 / 3) (by norm_num)
    (sectorPairGrading_monotone S) (sectorNeighborhood_isOpen S base ε ε)
    (fun _ z hz m θ => hN.transportedOddCircle_uniform_lower hS hT hflow z hz m θ) ho ho
  exact returnCircle_uniform_neg (S.circle (3 / 4 : ℝ)) hi (sectorPairGrading_monotone S)

include hflow in
theorem N01Properties.uniformSmoothFamilyOn_selectorInverseCircle
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    UniformSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun i => hN.selectorInverseCircle hS hT (rsel i) (hrsel i)) := by
  have hf := hN.uniformSmoothFamilyOn_endpointFlowCircle hS hT rsel hrsel
  have hi := uniformSmoothFamilyOn_circleInverse_maps (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1
    (by norm_num) (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
    (fun i m => -opticalTravel D.w (C.left m) (rsel i m))
    (1 / 2) (by norm_num) (sectorPairGrading_monotone S)
    (sectorNeighborhood_isOpen S base ε ε)
    (fun i z hz m θ => hN.endpointFlowCircle_uniform_lower hS hT hflow
      (rsel i) (hrsel i) z hz m θ) hf hf
  exact returnCircle_uniform_neg (S.circle (3 / 4 : ℝ)) hi (sectorPairGrading_monotone S)

include hflow in
theorem N01Properties.uniformSmoothFamilyOn_returnTransportInverseCircle :
    UniformSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun _ : I => hN.returnTransportInverseCircle hS hT) := by
  have hr := hN.uniformSmoothFamilyOn_rightChartInverseCircle (I := I) hS hT hflow
  have hf := hN.uniformSmoothFamilyOn_selectorInverseCircle hS hT hflow
    (fun _ : I => C.right) (fun _ => hN.right_radius_mem)
  have hc := uniformSmoothFamilyOn_circleCompose_maps (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1
    (by norm_num) (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ : I => fun _ => 0)
    (sectorPairGrading_monotone S) (sectorNeighborhood_isOpen S base ε ε) hr hf
  exact hr.add (sectorPairGrading_monotone S) hc

include hflow in
theorem N01Properties.uniformSmoothFamilyOn_returnCorrectionInitialCircle :
    UniformSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun _ : I => hN.returnCorrectionInitialCircle hS hT) := by
  have hl := uniformSmoothFamilyOn_sectorChart (I := I) S base ε
  have hg := hN.uniformSmoothFamilyOn_returnTransportInverseCircle (I := I) hS hT hflow
  have hc := uniformSmoothFamilyOn_circleCompose_maps (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1
    (by norm_num) (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ : I => fun m => -C.travel m)
    (sectorPairGrading_monotone S) (sectorNeighborhood_isOpen S base ε ε) hl hg
  exact hl.add (sectorPairGrading_monotone S) hc

include hflow in
theorem N01Properties.uniformSmoothFamilyOn_rightReturnChartCircle :
    UniformSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun _ : I => hN.rightReturnChartCircle hS hT) := by
  let hH := hS.2.1 (3 / 4 : ℝ)
  have hf := hN.uniformSmoothFamilyOn_returnFlowCircle (I := I) hS hT
  have hu := hN.uniformSmoothFamilyOn_sectorReturnTransportCircle (I := I) hS hT hflow
  have ho := hu.postTameContinuousLinear (sectorPairGrading_monotone S)
    (circleOddContinuousLinear hH) (circleOddLinear_tame hH)
  have hc := uniformSmoothFamilyOn_circleCompose_maps hH hT hN.1.1
    (by norm_num) (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ : I => fun m => -C.travel m)
    (sectorPairGrading_monotone S) (sectorNeighborhood_isOpen S base ε ε) hf ho
  exact hf.add (sectorPairGrading_monotone S) hc

include hflow in
theorem N01Properties.uniformSmoothFamilyOn_returnCorrectionDslopeCircle :
    UniformSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun _ : I => hN.returnCorrectionDslopeCircle hS hT) := by
  let hH := hS.2.1 (3 / 4 : ℝ)
  have he := hN.uniformSmoothFamilyOn_sectorReturnResidualCircle (I := I) hS hT hflow
  have hg := hN.uniformSmoothFamilyOn_returnTransportInverseCircle (I := I) hS hT hflow
  have hd := (hg.postTameContinuousLinear (sectorPairGrading_monotone S)
    (circleDerivativeContinuousLinear hH) (circleDerivativeLinear_isTame hH)).congr
      (fun _ z _ => circleDerivativeContinuousLinear_apply hH
        (hN.returnTransportInverseCircle hS hT z))
  exact uniformSmoothFamilyOn_circleAverage_maps hH hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ => 0)
    (sectorPairGrading_monotone S) (sectorNeighborhood_isOpen S base ε ε) he hd

end ContinuousFlexibility.Statements
