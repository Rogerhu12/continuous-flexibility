module

public import ContinuousFlexibility.Analysis.N04PulledFieldsReturnCircleFixedBase
public import ContinuousFlexibility.Analysis.N04PulledFieldsCircleProductFixedBase
public import ContinuousFlexibility.Analysis.N01TransportAngularInterpolation

/-!
# Fixed-base bounds for the actual correction displacement

The residual remains an independent input. The original divided difference,
right return chart, cutoff interpolation and two positive inverses produce
the same displacement as the existing correction construction. The common
base survives each of these finite operations.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

local instance n04PulledFieldsCorrectionCircleFixedBaseStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

theorem n04PulledFields_correctionParameterInterpolation
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) :
    HasInterpolation (pairGrading realGrading
      (pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading)) :=
  coordinate_hasInterpolation_pair (fun _ _ _ _ => le_rfl)
    (correctionParameterGrading_monotone S) coordinate_hasInterpolation_realGrading
    (correctionParameterGrading_hasInterpolation hS)

variable {I : Type*} {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hflow : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m r,
    r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ∧
      deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ≤ 3 / 2)

include hflow

theorem N01Properties.n04PulledFields_fixedBase_returnCorrectionDisplacementCircleLinear :
    N04PulledFieldsFixedBaseFamily
      (pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun (_ : I) (x : (StateDirections S × ℝ) × CircleSpace S) =>
        hN.returnCorrectionDisplacementCircleLinear hS hT x.1 x.2) := by
  let H := S.circle (3 / 4 : ℝ)
  let p := pairGrading (pairGrading (sectorGrading S) realGrading) H.grading
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  have hp : Monotone p := correctionParameterGrading_monotone S
  have hPI := n04PulledFields_correctionParameterInterpolation hS
  have hU := (sectorNeighborhood_isOpen S base ε ε).prod (isOpen_univ : IsOpen (univ : Set H.Space))
  have hd := (hN.n04PulledFields_fixedBase_returnCorrectionDslopeCircle (I := I) hS hT hflow).fst
    (r := H.grading) (sectorNeighborhood_isOpen S base ε ε)
  have hy := (hN.n04PulledFields_fixedBase_rightReturnChartCircle (I := I) hS hT hflow).fst
    (r := H.grading) (sectorNeighborhood_isOpen S base ε ε)
  have hρ : N04PulledFieldsFixedBaseFamily p H.grading (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun (_ : I) (x : (StateDirections S × ℝ) × H.Space) => x.2) :=
    n04PulledFields_fixedBaseFamily_linear hU
      (fun _ : I => ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) H.Space) 0
      (fun s => ⟨1, zero_le_one, fun _ x => by
        simp only [ContinuousLinearMap.coe_snd', Nat.add_zero, one_mul, pairGrading_apply]
        exact le_add_of_nonneg_left (apply_nonneg _ _)⟩)
  have hproduct := n04PulledFields_fixedBase_circleProduct_maps hN.1.1 hT (by norm_num) hH
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 hp hPI hU hd hρ
  have hsum := hρ.add hp hproduct
  have hcomp := n04PulledFields_fixedBase_circleCompose_maps hN.1.1 hT (by norm_num) hH
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ : I => fun m => -C.travel m) hp hPI hU hy hsum
  exact hcomp.congr (fun _ _ _ => rfl)

theorem N01Properties.n04PulledFields_fixedBase_interpolationSelectorCircle
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    N04PulledFieldsFixedBaseFamily (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun i => hN.interpolationSelectorCircle hS hT χ hχrange (rsel i) (hrsel i)) := by
  let H := S.circle (3 / 4 : ℝ)
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  have hc (i : I) : ∀ m, |χ m (rsel i m)| ≤ 1 :=
    cutoffSelector_abs_le_one χ (rsel i) hχrange (hrsel i)
  let L : I → H.Space →L[ℝ] H.Space := fun i =>
    circleComponentContractionContinuousLinear hH (fun m => χ m (rsel i m)) (hc i)
  have hK := hN.n04PulledFields_fixedBase_returnCorrectionInitialCircle (I := I) hS hT hflow
  have hpost : N04PulledFieldsFixedBaseFamily (pairGrading (sectorGrading S) realGrading)
      H.grading (sectorNeighborhood S base ε ε)
      (fun i z => L i (hN.returnCorrectionInitialCircle hS hT z)) :=
    hK.postContinuousLinear L 0
      (fun s => ⟨1, zero_le_one, fun i u => by
        have happ : L i u =
            circleComponentContractionLinear hH (fun m => χ m (rsel i m)) (hc i) u :=
          circleComponentContractionContinuousLinear_apply hH (fun m => χ m (rsel i m)) (hc i) u
        have hnorm : H.grading s (L i u) ≤ H.grading s u :=
          (congrArg (H.grading s) happ).trans_le
            (circleComponentContractionLinear_grading_le hH (fun m => χ m (rsel i m)) (hc i) s u)
        simpa only [Nat.add_zero, one_mul] using hnorm⟩)
  exact hpost.congr (fun i z _ => circleComponentContractionContinuousLinear_apply hH
    (fun m => χ m (rsel i m)) (hc i) (hN.returnCorrectionInitialCircle hS hT z))

theorem N01Properties.n04PulledFields_fixedBase_selectorInverseSlopeCircle
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    N04PulledFieldsFixedBaseFamily (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun i => hN.selectorInverseSlopeCircle hS hT (rsel i) (hrsel i)) := by
  let hH := hS.2.1 (3 / 4 : ℝ)
  have hf := hN.n04PulledFields_fixedBase_endpointFlowCircle hS hT rsel hrsel
  have hd := (hf.postTameContinuousLinear (circleDerivativeContinuousLinear hH)
    (circleDerivativeLinear_isTame hH)).congr
      (fun i z _ => circleDerivativeContinuousLinear_apply hH
        (hN.endpointFlowCircle hS hT (rsel i) (hrsel i) z))
  exact n04PulledFields_fixedBase_circleInverse_maps hN.1.1 hT (by norm_num) hH
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
    (fun i m => -opticalTravel D.w (C.left m) (rsel i m)) (1 / 2) (by norm_num)
    (sectorPairGrading_monotone S) (n04PulledFields_selectorParameterInterpolation hS)
    (sectorNeighborhood_isOpen S base ε ε)
    (fun i z hz m θ => hN.endpointFlowCircle_uniform_lower hS hT hflow
      (rsel i) (hrsel i) z hz m θ) hf hd

theorem N01Properties.n04PulledFields_fixedBase_returnCorrectionPulledDisplacementCircleLinear
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    N04PulledFieldsFixedBaseFamily
      (pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun i (x : (StateDirections S × ℝ) × CircleSpace S) =>
        hN.returnCorrectionPulledDisplacementCircleLinear hS hT χ hχrange (rsel i) (hrsel i) x.1 x.2) := by
  let H := S.circle (3 / 4 : ℝ)
  let p := pairGrading (pairGrading (sectorGrading S) realGrading) H.grading
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  have hp : Monotone p := correctionParameterGrading_monotone S
  have hPI := n04PulledFields_correctionParameterInterpolation hS
  have hU := (sectorNeighborhood_isOpen S base ε ε).prod (isOpen_univ : IsOpen (univ : Set H.Space))
  have hi := (hN.n04PulledFields_fixedBase_interpolationSelectorCircle
    hS hT hflow χ hχrange rsel hrsel).fst (r := H.grading) (sectorNeighborhood_isOpen S base ε ε)
  have hD := hN.n04PulledFields_fixedBase_returnCorrectionDisplacementCircleLinear (I := I) hS hT hflow
  have hfirst := n04PulledFields_fixedBase_circleInverse_maps hN.1.1 hT (by norm_num) hH
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ : I => fun _ => 0)
    (1 / 12) (by norm_num) hp hPI hU
    (fun i x hx m θ => hN.interpolationSelectorCircle_uniform_lower hS hT hflow
      χ hχrange (rsel i) (hrsel i) x.1 hx.1 m θ) hi hD
  have hf := (hN.n04PulledFields_fixedBase_endpointFlowCircle hS hT rsel hrsel).fst
    (r := H.grading) (sectorNeighborhood_isOpen S base ε ε)
  have hsecond := n04PulledFields_fixedBase_circleInverse_maps hN.1.1 hT (by norm_num) hH
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
    (fun i m => -opticalTravel D.w (C.left m) (rsel i m)) (1 / 2) (by norm_num) hp hPI hU
    (fun i x hx m θ => hN.endpointFlowCircle_uniform_lower hS hT hflow
      (rsel i) (hrsel i) x.1 hx.1 m θ) hf hfirst
  exact hsecond.congr (fun _ _ _ => rfl)

end ContinuousFlexibility.Statements
