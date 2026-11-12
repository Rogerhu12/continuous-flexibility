import ContinuousFlexibility.Analysis.N01ReturnVelocityCircle

/-!
# Full parameter tameness of the actual cutoff velocity

Both inverse compositions are the canonical operators whose decoders
are the actual old flow and interpolation inverses. Their genuine tame
towers, the exact divided-difference displacement, and the same cutoff
multiplier give the original velocity jointly in the state and the
independent residual. The resulting scalar tower also varies the angle.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

theorem smoothTameOn_circlePositiveInverseCompose_maps
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {H : CircleModelData}
    (hH : IsCircleModel T γ H) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hi : HasInterpolation H.grading) (travel : ℕ → ℝ)
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (ht : WithSeminorms p)
    {U : Set E} (hU : IsOpen U) {f g : E → H.Space}
    (hpos : MapsTo f U (circlePositiveLiftDomain H))
    (hf : SmoothTameOn p H.grading U f) (hg : SmoothTameOn p H.grading U g) :
    SmoothTameOn p H.grading U
      (fun x => circlePositiveInverseComposeLinear hH hT hD hγ travel (f x) (g x)) := by
  letI : ∀ n, CompleteSpace (H.level n) :=
    fun n => (hH.2.1 n).isComplete.completeSpace_coe
  have htop : WithSeminorms H.grading :=
    withSeminorms_graded (fun n => H.level n) H.bond
  exact smoothTameOn_comp_topological
    (X := E) (Y := H.Space × H.Space)
    (G := fun n => H.level n) (g := H.bond)
    (p := p) (q := pairGrading H.grading H.grading) (r := H.grading)
    (U := U) (V := circlePositiveLiftDomain H ×ˢ (univ : Set H.Space))
    (u := fun x => (f x, g x))
    (v := fun x : H.Space × H.Space =>
      circlePositiveInverseComposeLinear hH hT hD hγ travel x.1 x.2)
    hp ht (withSeminorms_pairGrading htop htop)
    hU ((circlePositiveLiftDomain_isOpen hH hT hD hγ).prod isOpen_univ)
    (fun x hx => ⟨hpos hx, mem_univ _⟩) (smoothTameOn_prodMk hp ht hf hg)
    (smoothTameOn_circlePositiveInverseComposeLinear hH hT hD hγ hi travel)

local instance n01ReturnVelocitySmoothTameStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.smoothTameOn_selectorInverseSlopeCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) :
    SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (hN.selectorInverseSlopeCircle hS hT rsel hrsel) := by
  let H := S.circle (3 / 4 : ℝ)
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  letI : ∀ n, CompleteSpace (H.level n) :=
    fun n => (hH.2.1 n).isComplete.completeSpace_coe
  have hp := sectorPairGrading_monotone S
  have ht := sectorPairGrading_withSeminorms S
  have htop : WithSeminorms H.grading :=
    withSeminorms_graded (fun n => H.level n) H.bond
  have hU := sectorNeighborhood_isOpen S base ε ε
  have hflow := hN.smoothTameOn_endpointFlowCircle hS hT rsel hrsel
  have hder : SmoothTameOn (pairGrading (sectorGrading S) realGrading) H.grading
      (sectorNeighborhood S base ε ε)
      (fun z => circleDerivativeLinear hH (hN.endpointFlowCircle hS hT rsel hrsel z)) :=
    smoothTameOn_comp_topological hp ht htop hU isOpen_univ (fun _ _ => mem_univ _)
      hflow (smoothTameOn_circleDerivativeLinear hH)
  exact smoothTameOn_circlePositiveInverseCompose_maps hH hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
    (fun m => -opticalTravel D.w (C.left m) (rsel m)) hp ht hU
    (fun z hz => hN.endpointFlowCircle_mem_positiveLiftDomain hS hT rsel hrsel z hz) hflow hder

theorem N01Properties.smoothTameOn_returnCorrectionPulledDisplacementCircleLinear
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun x : (StateDirections S × ℝ) × CircleSpace S =>
        hN.returnCorrectionPulledDisplacementCircleLinear hS hT χ hχrange rsel hrsel x.1 x.2) := by
  let H := S.circle (3 / 4 : ℝ)
  let p := pairGrading (pairGrading (sectorGrading S) realGrading) H.grading
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  have hp : Monotone p := tamePairGrading_monotone (sectorPairGrading_monotone S)
    (gradedSeminorm_monotone (fun n => H.level n) H.bond)
  have ht : WithSeminorms p := withSeminorms_pairGrading (sectorPairGrading_withSeminorms S)
    (withSeminorms_graded (fun n => H.level n) H.bond)
  have hU := (sectorNeighborhood_isOpen S base ε ε).prod (isOpen_univ : IsOpen (univ : Set H.Space))
  have hi : HasInterpolation H.grading := (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
  have hJ := solve_smoothTameOn_fst H.grading
    (hN.smoothTameOn_interpolationSelectorCircle hS hT χ hχrange rsel hrsel)
  have hD := hN.smoothTameOn_returnCorrectionDisplacementCircleLinear hS hT
  have hfirst := smoothTameOn_circlePositiveInverseCompose_maps hH hT hN.1.1 (by norm_num)
    hi (fun _ => 0) hp ht hU
    (fun x hx => hN.interpolationSelectorCircle_positive hS hT χ hχrange rsel hrsel x.1 hx.1)
    hJ hD
  have hflow := solve_smoothTameOn_fst H.grading
    (hN.smoothTameOn_endpointFlowCircle hS hT rsel hrsel)
  have hsecond := smoothTameOn_circlePositiveInverseCompose_maps hH hT hN.1.1 (by norm_num)
    hi (fun m => -opticalTravel D.w (C.left m) (rsel m)) hp ht hU
    (fun x hx => hN.endpointFlowCircle_mem_positiveLiftDomain hS hT rsel hrsel x.1 hx.1)
    hflow hfirst
  apply smoothTameOn_congr hsecond
  intro x hx
  rfl

theorem N01Properties.smoothTameOn_returnCorrectionVelocityCircleLinear
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (hcutoff : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
      |iteratedDeriv k (χ m) r| ≤ A * radialE (D.cellIndex (j m)) ^ P)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) :
    SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun x : (StateDirections S × ℝ) × CircleSpace S =>
        hN.returnCorrectionVelocityCircleLinear hS hT j hcell χ hχrange hcutoff rsel hrsel x.1 x.2) := by
  let H := S.circle (3 / 4 : ℝ)
  let p := pairGrading (pairGrading (sectorGrading S) realGrading) H.grading
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  letI : ∀ n, CompleteSpace (H.level n) :=
    fun n => (hH.2.1 n).isComplete.completeSpace_coe
  have hp : Monotone p := tamePairGrading_monotone (sectorPairGrading_monotone S)
    (gradedSeminorm_monotone (fun n => H.level n) H.bond)
  have ht : WithSeminorms p := withSeminorms_pairGrading (sectorPairGrading_withSeminorms S)
    (withSeminorms_graded (fun n => H.level n) H.bond)
  have hU := (sectorNeighborhood_isOpen S base ε ε).prod (isOpen_univ : IsOpen (univ : Set H.Space))
  have hD := hN.smoothTameOn_returnCorrectionPulledDisplacementCircleLinear hS hT χ hχrange rsel hrsel
  have hw := solve_smoothTameOn_fst H.grading
    (hN.smoothTameOn_selectorInverseSlopeCircle hS hT rsel hrsel)
  have hprod := smoothTameOn_circleProduct_maps hH hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 hp ht hU hw hD
  have hsum := smoothTameOn_add hp hD hprod
  have hscaled := smoothTameOn_comp_topological hp ht
    (withSeminorms_graded (fun n => H.level n) H.bond) hU isOpen_univ (fun _ _ => mem_univ _)
    hsum (hN.smoothTameOn_opticalCutoffJetCircleLinear hS hT j hcell χ hcutoff 1 rsel)
  apply smoothTameOn_congr hscaled
  intro x hx
  rfl

def N01Properties.returnCorrectionVelocity_jointTower
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (hcutoff : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
      |iteratedDeriv k (χ m) r| ≤ A * radialE (D.cellIndex (j m)) ^ P)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) (m : ℕ) :
    SmoothDirections ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ univ)
      (fun p : ((StateDirections S × ℝ) × CircleSpace S) × ℝ =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C p.1.1) m
          (rsel m, p.2) p.1.2) := by
  let J := (hN.smoothTameOn_returnCorrectionVelocityCircleLinear
    hS hT j hcell χ hχrange hcutoff rsel hrsel).choose
  have hH (i : ℕ) : 0 < T.H (T.sample i) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 i)).2.1
  apply (circleDecodedJointDirections (hS.2.1 (3 / 4 : ℝ)) hH J m).congrOn
  intro p hp
  exact hN.returnCorrectionVelocityCircleLinear_decode hS hT j hcell χ hχrange hcutoff
    rsel hrsel p.1.1 hp.1.1 p.1.2 m p.2

end ContinuousFlexibility.Statements
