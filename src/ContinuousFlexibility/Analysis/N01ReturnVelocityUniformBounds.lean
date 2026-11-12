import ContinuousFlexibility.Analysis.N01ReturnCircleUniformBounds
import ContinuousFlexibility.Analysis.ReturnInterpolationJetBounds

/-!
# Selector-uniform one-high estimates for the actual cutoff velocity

The proof follows the existing independent-residual displacement, both
actual inverse compositions, the inverse-flow angular slope and the same
cutoff derivative. The low order and loss are chosen before the radius of
the low box and the output order; every numerical constant is chosen
before the closed-radius selector. Ordinary radial differentiation is a
separate ODE estimate and is not asserted here.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

local instance n01ReturnVelocityUniformBoundsStateSMul (S : PhysicalSpacesData) :
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
theorem N01Properties.uniformSmoothFamilyOn_returnCorrectionDisplacementCircleLinear :
    UniformSmoothFamilyOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun (_ : I) (x : (StateDirections S × ℝ) × CircleSpace S) =>
        hN.returnCorrectionDisplacementCircleLinear hS hT x.1 x.2) := by
  let H := S.circle (3 / 4 : ℝ)
  let p := pairGrading (pairGrading (sectorGrading S) realGrading) H.grading
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  have hm := gradedSeminorm_monotone (fun n => H.level n) H.bond
  have hp : Monotone p := tamePairGrading_monotone (sectorPairGrading_monotone S) hm
  have hU := (sectorNeighborhood_isOpen S base ε ε).prod (isOpen_univ : IsOpen (univ : Set H.Space))
  have hd := (hN.uniformSmoothFamilyOn_returnCorrectionDslopeCircle (I := I) hS hT hflow).fst
    (sectorPairGrading_monotone S) hm (sectorNeighborhood_isOpen S base ε ε)
  have hy := (hN.uniformSmoothFamilyOn_rightReturnChartCircle (I := I) hS hT hflow).fst
    (sectorPairGrading_monotone S) hm (sectorNeighborhood_isOpen S base ε ε)
  have hρ : UniformSmoothFamilyOn p H.grading (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun (_ : I) (x : (StateDirections S × ℝ) × H.Space) => x.2) :=
    uniformSmoothFamilyOn_linear hU hp
      (fun _ : I => ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) H.Space) 0
      (fun s => ⟨1, zero_le_one, fun i x => by
        simp only [ContinuousLinearMap.coe_snd', Nat.add_zero, one_mul, pairGrading_apply]
        exact le_add_of_nonneg_left (apply_nonneg _ _)⟩)
  have hproduct := uniformSmoothFamilyOn_circleProduct_maps hH hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 hp hU hd hρ
  have hsum := hρ.add hp hproduct
  have hcomp := uniformSmoothFamilyOn_circleCompose_maps hH hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ : I => fun m => -C.travel m) hp hU hy hsum
  exact hcomp.congr (fun _ _ _ => rfl)

include hflow in
theorem N01Properties.uniformSmoothFamilyOn_interpolationSelectorCircle
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    UniformSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun i => hN.interpolationSelectorCircle hS hT χ hχrange (rsel i) (hrsel i)) := by
  let H := S.circle (3 / 4 : ℝ)
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  have hc (i : I) : ∀ m, |χ m (rsel i m)| ≤ 1 :=
    cutoffSelector_abs_le_one χ (rsel i) hχrange (hrsel i)
  let L : I → H.Space →L[ℝ] H.Space := fun i =>
    circleComponentContractionContinuousLinear hH (fun m => χ m (rsel i m)) (hc i)
  have hK : UniformSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      H.grading (sectorNeighborhood S base ε ε)
      (fun (_ : I) z => hN.returnCorrectionInitialCircle hS hT z) :=
    hN.uniformSmoothFamilyOn_returnCorrectionInitialCircle (I := I) hS hT hflow
  have hpost : UniformSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      H.grading (sectorNeighborhood S base ε ε)
      (fun i z => L i (hN.returnCorrectionInitialCircle hS hT z)) :=
    hK.postContinuousLinear (sectorPairGrading_monotone S) L 0
      (fun s => ⟨1, zero_le_one, fun i u => by
        have happ : L i u =
            circleComponentContractionLinear hH (fun m => χ m (rsel i m)) (hc i) u :=
          circleComponentContractionContinuousLinear_apply hH (fun m => χ m (rsel i m))
            (hc i) u
        have hnorm : H.grading s (L i u) ≤ H.grading s u :=
          (congrArg (H.grading s) happ).trans_le
            (circleComponentContractionLinear_grading_le hH (fun m => χ m (rsel i m))
              (hc i) s u)
        simpa only [Nat.add_zero, one_mul] using hnorm⟩)
  exact hpost.congr (fun i z _ => circleComponentContractionContinuousLinear_apply hH
    (fun m => χ m (rsel i m)) (hc i) (hN.returnCorrectionInitialCircle hS hT z))

include hflow in
theorem N01Properties.interpolationSelectorCircle_uniform_lower
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) (m : ℕ) (θ : ℝ) :
    1 / 12 ≤ 1 + deriv ((S.circle (3 / 4 : ℝ)).decode
      (hN.interpolationSelectorCircle hS hT χ hχrange rsel hrsel z) m) θ := by
  rw [← circleAffineLift_deriv (hS.2.1 (3 / 4 : ℝ)) (fun _ => 0),
    hN.interpolationSelectorCircle_lift hS hT χ hχrange rsel hrsel z hz m]
  have hb := hN.returnCorrectionInitialMap_deriv_bounds
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (hN.2.2.1.liftSectorParameter_sector z)
    (fun j t => hflow z hz j (C.right j) (hN.right_radius_mem j) t) m θ
  have hpos : 0 < deriv (returnCorrectionInitialMap S C (liftSectorParameter S C z) m) θ :=
    (by norm_num : (0 : ℝ) < 1 / 12).trans_le hb.1
  rw [(returnInterpolation_hasDerivAt (χ := χ m (rsel m))
    (differentiableAt_of_deriv_ne_zero hpos.ne').hasDerivAt).deriv]
  have hc := hχrange m (rsel m) (hrsel m)
  have hm := mul_nonneg hc.1 (sub_nonneg.mpr hb.1)
  nlinarith only [hm, hc.2]

include hflow in
theorem N01Properties.uniformSmoothFamilyOn_selectorInverseSlopeCircle
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    UniformSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun i => hN.selectorInverseSlopeCircle hS hT (rsel i) (hrsel i)) := by
  let hH := hS.2.1 (3 / 4 : ℝ)
  have hf := hN.uniformSmoothFamilyOn_endpointFlowCircle hS hT rsel hrsel
  have hd := (hf.postTameContinuousLinear (sectorPairGrading_monotone S)
    (circleDerivativeContinuousLinear hH) (circleDerivativeLinear_isTame hH)).congr
      (fun i z _ => circleDerivativeContinuousLinear_apply hH
        (hN.endpointFlowCircle hS hT (rsel i) (hrsel i) z))
  exact uniformSmoothFamilyOn_circleInverse_maps hH hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
    (fun i m => -opticalTravel D.w (C.left m) (rsel i m)) (1 / 2) (by norm_num)
    (sectorPairGrading_monotone S) (sectorNeighborhood_isOpen S base ε ε)
    (fun i z hz m θ => hN.endpointFlowCircle_uniform_lower hS hT hflow
      (rsel i) (hrsel i) z hz m θ) hf hd

include hflow in
theorem N01Properties.uniformSmoothFamilyOn_returnCorrectionPulledDisplacementCircleLinear
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    UniformSmoothFamilyOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun i (x : (StateDirections S × ℝ) × CircleSpace S) =>
        hN.returnCorrectionPulledDisplacementCircleLinear hS hT χ hχrange (rsel i) (hrsel i) x.1 x.2) := by
  let H := S.circle (3 / 4 : ℝ)
  let p := pairGrading (pairGrading (sectorGrading S) realGrading) H.grading
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  have hm := gradedSeminorm_monotone (fun n => H.level n) H.bond
  have hp : Monotone p := tamePairGrading_monotone (sectorPairGrading_monotone S) hm
  have hU := (sectorNeighborhood_isOpen S base ε ε).prod (isOpen_univ : IsOpen (univ : Set H.Space))
  have hi := (hN.uniformSmoothFamilyOn_interpolationSelectorCircle hS hT hflow χ hχrange rsel hrsel).fst
    (sectorPairGrading_monotone S) hm (sectorNeighborhood_isOpen S base ε ε)
  have hD := hN.uniformSmoothFamilyOn_returnCorrectionDisplacementCircleLinear (I := I) hS hT hflow
  have hfirst := uniformSmoothFamilyOn_circleInverse_maps hH hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ : I => fun _ => 0)
    (1 / 12) (by norm_num) hp hU
    (fun i x hx m θ => hN.interpolationSelectorCircle_uniform_lower hS hT hflow
      χ hχrange (rsel i) (hrsel i) x.1 hx.1 m θ) hi hD
  have hf := (hN.uniformSmoothFamilyOn_endpointFlowCircle hS hT rsel hrsel).fst
    (sectorPairGrading_monotone S) hm (sectorNeighborhood_isOpen S base ε ε)
  have hsecond := uniformSmoothFamilyOn_circleInverse_maps hH hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
    (fun i m => -opticalTravel D.w (C.left m) (rsel i m)) (1 / 2) (by norm_num) hp hU
    (fun i x hx m θ => hN.endpointFlowCircle_uniform_lower hS hT hflow
      (rsel i) (hrsel i) x.1 hx.1 m θ) hf hfirst
  exact hsecond.congr (fun _ _ _ => rfl)

include hflow in
theorem N01Properties.uniformSmoothFamilyOn_returnCorrectionPulledResidualCircle
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    UniformSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun i z => hN.returnCorrectionPulledDisplacementCircleLinear hS hT χ hχrange
        (rsel i) (hrsel i) z (hN.sectorReturnResidualCircle hS hT z)) := by
  let H := S.circle (3 / 4 : ℝ)
  let p := pairGrading (sectorGrading S) realGrading
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  letI : ∀ n, CompleteSpace (H.level n) :=
    fun n => (hH.2.1 n).isComplete.completeSpace_coe
  letI : LocallyConvexSpace ℝ ((StateDirections S × ℝ) × H.Space) :=
    (withSeminorms_pairGrading (sectorPairGrading_withSeminorms S)
      (withSeminorms_graded (fun n => H.level n) H.bond)).toLocallyConvexSpace
  have hp : Monotone p := sectorPairGrading_monotone S
  have hU := sectorNeighborhood_isOpen S base ε ε
  have hid : UniformSmoothFamilyOn p p (sectorNeighborhood S base ε ε)
      (fun (_ : I) (z : StateDirections S × ℝ) => z) :=
    uniformSmoothFamilyOn_linear hU hp
      (fun _ : I => ContinuousLinearMap.id ℝ (StateDirections S × ℝ)) 0
      (fun s => ⟨1, zero_le_one, fun _ _ => by
        simp only [ContinuousLinearMap.id_apply, Nat.add_zero, one_mul, le_refl]⟩)
  have he := hN.uniformSmoothFamilyOn_sectorReturnResidualCircle (I := I) hS hT hflow
  have hD := hN.uniformSmoothFamilyOn_returnCorrectionPulledDisplacementCircleLinear
    hS hT hflow χ hχrange rsel hrsel
  exact UniformSmoothFamilyOn.comp
    (Y := fun n => H.level n) (bond := H.bond)
    (p := p) (q := pairGrading p H.grading) (r := H.grading)
    (U := sectorNeighborhood S base ε ε)
    (V := sectorNeighborhood S base ε ε ×ˢ (univ : Set H.Space))
    (f := fun (_ : I) z => (z, hN.sectorReturnResidualCircle hS hT z))
    (g := fun i (x : (StateDirections S × ℝ) × H.Space) =>
      hN.returnCorrectionPulledDisplacementCircleLinear hS hT χ hχrange
        (rsel i) (hrsel i) x.1 x.2)
    hD hp (hid.prodMk hp he) hU (hU.prod isOpen_univ)
    (fun _ _ hz => ⟨hz, mem_univ _⟩)

include hflow in
/-- Any genuine tower of the inverse angular slope has the same
selector-uniform estimates. Apply `.oneHigh n` to obtain homogeneous
estimates with all constants chosen before the selector. -/
theorem N01Properties.selectorInverseSlopeCircle_uniformFamilyJetBounds
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m))
    (J : ∀ i, SmoothDirections (sectorNeighborhood S base ε ε)
      (hN.selectorInverseSlopeCircle hS hT (rsel i) (hrsel i))) :
    UniformFamilyJetBounds (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading J :=
  (hN.uniformSmoothFamilyOn_selectorInverseSlopeCircle hS hT hflow rsel hrsel).jets J

include hflow in
theorem N01Properties.returnCorrectionPulledDisplacementCircleLinear_uniformFamilyJetBounds
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m))
    (J : ∀ i, SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun x : (StateDirections S × ℝ) × CircleSpace S =>
        hN.returnCorrectionPulledDisplacementCircleLinear hS hT χ hχrange
          (rsel i) (hrsel i) x.1 x.2)) :
    UniformFamilyJetBounds
      (pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading)
      (S.circle (3 / 4 : ℝ)).grading J :=
  (hN.uniformSmoothFamilyOn_returnCorrectionPulledDisplacementCircleLinear
    hS hT hflow χ hχrange rsel hrsel).jets J

include hflow in
theorem N01Properties.returnCorrectionPulledResidualCircle_uniformFamilyJetBounds
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m))
    (J : ∀ i, SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => hN.returnCorrectionPulledDisplacementCircleLinear hS hT χ hχrange
        (rsel i) (hrsel i) z (hN.sectorReturnResidualCircle hS hT z))) :
    UniformFamilyJetBounds (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading J :=
  (hN.uniformSmoothFamilyOn_returnCorrectionPulledResidualCircle
    hS hT hflow χ hχrange rsel hrsel).jets J

include hflow in
theorem N01Properties.uniformSmoothFamilyOn_returnCorrectionVelocityCircleLinear
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (hcutoff : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
      |iteratedDeriv k (χ m) r| ≤ A * radialE (D.cellIndex (j m)) ^ P)
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    UniformSmoothFamilyOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun i (x : (StateDirections S × ℝ) × CircleSpace S) =>
        hN.returnCorrectionVelocityCircleLinear hS hT j hcell χ hχrange hcutoff
          (rsel i) (hrsel i) x.1 x.2) := by
  let H := S.circle (3 / 4 : ℝ)
  let p := pairGrading (pairGrading (sectorGrading S) realGrading) H.grading
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  have hm := gradedSeminorm_monotone (fun n => H.level n) H.bond
  have hp : Monotone p := tamePairGrading_monotone (sectorPairGrading_monotone S) hm
  have hU := (sectorNeighborhood_isOpen S base ε ε).prod (isOpen_univ : IsOpen (univ : Set H.Space))
  have hd := hN.uniformSmoothFamilyOn_returnCorrectionPulledDisplacementCircleLinear
    hS hT hflow χ hχrange rsel hrsel
  have hs := (hN.uniformSmoothFamilyOn_selectorInverseSlopeCircle hS hT hflow rsel hrsel).fst
    (sectorPairGrading_monotone S) hm (sectorNeighborhood_isOpen S base ε ε)
  have hprod := uniformSmoothFamilyOn_circleProduct_maps hH hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 hp hU hs hd
  have hsum := hd.add hp hprod
  let hb : ∃ K : ℝ, 0 ≤ K ∧ ∀ (r : ℕ → ℝ) (s : ℕ) (u : H.Space),
      H.grading s (hN.opticalCutoffJetCircleLinear hS hT j hcell χ hcutoff 1 r u) ≤
        K * H.grading (s + 1) u :=
    hN.opticalCutoffJetCircleLinear_uniform_bound hS hT j hcell χ hcutoff 1
  let K : ℝ := hb.choose
  have hK : 0 ≤ K := hb.choose_spec.1
  let M : I → H.Space →ₗ[ℝ] H.Space := fun i =>
    hN.opticalCutoffJetCircleLinear hS hT j hcell χ hcutoff 1 (rsel i)
  have htame (i : I) : IsTameLinear H.grading H.grading (M i) 1 0 :=
    fun s _ => ⟨⟨K, hK⟩, fun u => hb.choose_spec.2 (rsel i) s u⟩
  let L : I → H.Space →L[ℝ] H.Space := fun i => (htame i).toContinuousLinearMap
    (withSeminorms_graded (fun n => H.level n) H.bond)
    (withSeminorms_graded (fun n => H.level n) H.bond) hm
  have heq (i : I) (u : H.Space) : L i u = M i u :=
    IsTameLinear.toContinuousLinearMap_apply (htame i)
      (withSeminorms_graded (fun n => H.level n) H.bond)
      (withSeminorms_graded (fun n => H.level n) H.bond) hm u
  have hpost := hsum.postContinuousLinear
    (p := p) (q := H.grading) (r := H.grading) hp L 1
    (fun s => ⟨K, hK, fun i u =>
      (congrArg (H.grading s) (heq i u)).trans_le (hb.choose_spec.2 (rsel i) s u)⟩)
  apply hpost.congr
  intro i x hx
  simp only [N01Properties.returnCorrectionVelocityCircleLinear, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  exact heq i _

include hflow in
/-- The constant is chosen before the radius selector and before the
choice of any genuine tower for the same actual velocity map. -/
theorem N01Properties.returnCorrectionVelocity_uniform_oneHigh
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (hcutoff : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
      |iteratedDeriv k (χ m) r| ≤ A * radialE (D.cellIndex (j m)) ^ P) :
    ∀ n, ∃ B L : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
      (J : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
        (fun x : (StateDirections S × ℝ) × CircleSpace S =>
          hN.returnCorrectionVelocityCircleLinear hS hT j hcell χ hχrange hcutoff rsel hrsel x.1 x.2)),
      ∀ x ∈ sectorNeighborhood S base ε ε ×ˢ univ,
        pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading B x ≤ R →
      ∀ v : Fin n → (StateDirections S × ℝ) × CircleSpace S,
        (S.circle (3 / 4 : ℝ)).grading s (J.D n x v) ≤ K *
          tameJetSize (pairGrading (pairGrading (sectorGrading S) realGrading)
            (S.circle (3 / 4 : ℝ)).grading) n s L B x v := by
  let H := S.circle (3 / 4 : ℝ)
  let p := pairGrading (pairGrading (sectorGrading S) realGrading) H.grading
  let U := sectorNeighborhood S base ε ε ×ˢ (univ : Set H.Space)
  let A := {rsel : ℕ → ℝ // ∀ m, rsel m ∈ Icc (C.left m) (C.right m)}
  let f : A → ((StateDirections S × ℝ) × H.Space) → H.Space := fun r x =>
    hN.returnCorrectionVelocityCircleLinear hS hT j hcell χ hχrange hcutoff
      r.val r.property x.1 x.2
  let h : UniformSmoothFamilyOn p H.grading U f :=
    hN.uniformSmoothFamilyOn_returnCorrectionVelocityCircleLinear hS hT hflow
      j hcell χ hχrange hcutoff (fun r : A => r.val) (fun r => r.property)
  let J₀ : ∀ r : A, SmoothDirections U (f r) := h.choose
  have hJ₀ : UniformFamilyJetBounds p H.grading J₀ := h.choose_spec
  intro n
  let hb : ∃ B L : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ r : A, ∀ x, x ∈ U → p B x ≤ R →
      ∀ v : Fin n → (StateDirections S × ℝ) × H.Space,
        H.grading s ((J₀ r).D n x v) ≤ K * tameJetSize p n s L B x v :=
    hJ₀.oneHigh n
  let B : ℕ := hb.choose
  let L : ℕ := hb.choose_spec.choose
  refine ⟨B, L, fun R hR s => ?_⟩
  let hc : ∃ K : ℝ, 0 ≤ K ∧
      ∀ r : A, ∀ x, x ∈ U → p B x ≤ R →
      ∀ v : Fin n → (StateDirections S × ℝ) × H.Space,
        H.grading s ((J₀ r).D n x v) ≤ K * tameJetSize p n s L B x v :=
    hb.choose_spec.choose_spec R hR s
  refine ⟨hc.choose, hc.choose_spec.1, fun rsel hrsel J x hx hlow v => ?_⟩
  have heq : J.D n x = (J₀ (⟨rsel, hrsel⟩ : A)).D n x :=
    J.unique (J₀ (⟨rsel, hrsel⟩ : A)) n x hx
  have hnorm : H.grading s (J.D n x v) =
      H.grading s ((J₀ (⟨rsel, hrsel⟩ : A)).D n x v) :=
    congrArg (fun L : ContinuousMultilinearMap ℝ
      (fun _ : Fin n => (StateDirections S × ℝ) × H.Space) H.Space => H.grading s (L v)) heq
  exact hnorm.trans_le (hc.choose_spec.2 (⟨rsel, hrsel⟩ : A) x hx hlow v)

end ContinuousFlexibility.Statements
