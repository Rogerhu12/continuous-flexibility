module

public import ContinuousFlexibility.Analysis.N04PulledFieldsCorrectionCircleFixedBase

/-!
# Fixed-base estimates for the actual correction velocity

The genuine independent-residual velocity is the original pulled
displacement times the original inverse angular slope, followed by the
same cutoff derivative. The N02 decoder identity then substitutes the
retained actual residual. Neither step changes the low base with the
parameter order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

local instance n04PulledFieldsVelocityFixedBaseStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {I : Type*} {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hflow : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m r,
    r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ∧
      deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ≤ 3 / 2)
  (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
  (χ : ℕ → ℝ → ℝ)
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
  (hcutoff : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
    |iteratedDeriv k (χ m) r| ≤ A * radialE (D.cellIndex (j m)) ^ P)

include hflow

theorem N01Properties.n04PulledFields_fixedBase_returnCorrectionVelocityCircleLinear
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    N04PulledFieldsFixedBaseFamily
      (pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun i (x : (StateDirections S × ℝ) × CircleSpace S) =>
        hN.returnCorrectionVelocityCircleLinear hS hT j hcell χ hχrange hcutoff
          (rsel i) (hrsel i) x.1 x.2) := by
  let H := S.circle (3 / 4 : ℝ)
  let p := pairGrading (pairGrading (sectorGrading S) realGrading) H.grading
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  have hm := gradedSeminorm_monotone (fun n => H.level n) H.bond
  have hp : Monotone p := correctionParameterGrading_monotone S
  have hU := (sectorNeighborhood_isOpen S base ε ε).prod (isOpen_univ : IsOpen (univ : Set H.Space))
  have hd := hN.n04PulledFields_fixedBase_returnCorrectionPulledDisplacementCircleLinear
    hS hT hflow χ hχrange rsel hrsel
  have hs := (hN.n04PulledFields_fixedBase_selectorInverseSlopeCircle hS hT hflow rsel hrsel).fst
    (r := H.grading) (sectorNeighborhood_isOpen S base ε ε)
  have hprod := n04PulledFields_fixedBase_circleProduct_maps hN.1.1 hT (by norm_num) hH
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 hp
    (n04PulledFields_correctionParameterInterpolation hS) hU hs hd
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
  have hpost := hsum.postContinuousLinear L 1
    (fun s => ⟨K, hK, fun i u =>
      (congrArg (H.grading s) (heq i u)).trans_le (hb.choose_spec.2 (rsel i) s u)⟩)
  apply hpost.congr
  intro i x hx
  simp only [N01Properties.returnCorrectionVelocityCircleLinear, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  exact heq i _

theorem N01Properties.n04PulledFields_fixedBase_actualReturnCorrectionVelocity
    (hR : N02Properties D T S C R base ε)
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    N04PulledFieldsFixedBaseFamily (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun i z => hN.returnCorrectionVelocityCircleLinear hS hT j hcell χ hχrange hcutoff
        (rsel i) (hrsel i) z (R.residual (liftSectorParameter S C z))) := by
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
  have hid : N04PulledFieldsFixedBaseFamily p p (sectorNeighborhood S base ε ε)
      (fun (_ : I) (z : StateDirections S × ℝ) => z) :=
    n04PulledFields_fixedBaseFamily_linear hU
      (fun _ : I => ContinuousLinearMap.id ℝ (StateDirections S × ℝ)) 0
      (fun s => ⟨1, zero_le_one, fun _ _ => by
        simp only [ContinuousLinearMap.id_apply, Nat.add_zero, one_mul, le_refl]⟩)
  have he := (hN.n04PulledFields_fixedBase_sectorReturnResidualCircle (I := I) hS hT hflow).congr
    (fun _ z hz => hN.sectorReturnResidualCircle_eq_of_N02 hS hT hR z hz)
  have hv := hN.n04PulledFields_fixedBase_returnCorrectionVelocityCircleLinear
    hS hT hflow j hcell χ hχrange hcutoff rsel hrsel
  exact N04PulledFieldsFixedBaseFamily.comp
    (Y := fun n => H.level n) (bond := H.bond)
    (p := p) (q := pairGrading p H.grading) (r := H.grading)
    (U := sectorNeighborhood S base ε ε)
    (V := sectorNeighborhood S base ε ε ×ˢ (univ : Set H.Space))
    (f := fun (_ : I) z => (z, R.residual (liftSectorParameter S C z)))
    (g := fun i (x : (StateDirections S × ℝ) × H.Space) =>
      hN.returnCorrectionVelocityCircleLinear hS hT j hcell χ hχrange hcutoff
        (rsel i) (hrsel i) x.1 x.2)
    hv hp (n04PulledFields_selectorParameterInterpolation hS)
    (hid.prodMk hp he) hU (hU.prod isOpen_univ) (fun _ _ hz => ⟨hz, mem_univ _⟩)

/-- The actual N02-substituted velocity has one low base before every
parameter order. The constants are also chosen before the radius selector
and the supplied genuine tower. -/
theorem N01Properties.n04PulledFields_actualVelocity_fixedBase_oneHigh
    (hR : N02Properties D T S C R base ε) :
    ∃ B : ℕ, ∃ d : ℕ → ℕ, ∀ n A, 0 ≤ A → ∀ s, ∃ K : ℝ, 0 ≤ K ∧
      ∀ (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
        (J : SmoothDirections (sectorNeighborhood S base ε ε)
          (fun z => hN.returnCorrectionVelocityCircleLinear hS hT j hcell χ hχrange hcutoff
            rsel hrsel z (R.residual (liftSectorParameter S C z)))),
      ∀ z ∈ sectorNeighborhood S base ε ε, pairGrading (sectorGrading S) realGrading B z ≤ A →
      ∀ v : Fin n → (StateDirections S × ℝ),
        (S.circle (3 / 4 : ℝ)).grading s (J.D n z v) ≤
          K * tameJetSize (pairGrading (sectorGrading S) realGrading) n s (d n) B z v := by
  let I := {rsel : ℕ → ℝ // ∀ m, rsel m ∈ Icc (C.left m) (C.right m)}
  let family := hN.n04PulledFields_fixedBase_actualReturnCorrectionVelocity hS hT hflow
    j hcell χ hχrange hcutoff hR (fun i : I => i.val) (fun i => i.property)
  let data := family.oneHigh
  refine ⟨data.choose, data.choose_spec.choose, fun n A hA s => ?_⟩
  let estimate := data.choose_spec.choose_spec n A hA s
  exact ⟨estimate.choose, estimate.choose_spec.1,
    fun rsel hrsel => estimate.choose_spec.2 (⟨rsel, hrsel⟩ : I)⟩

end ContinuousFlexibility.Statements
