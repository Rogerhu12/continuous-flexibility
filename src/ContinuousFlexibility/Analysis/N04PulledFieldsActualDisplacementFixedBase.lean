import ContinuousFlexibility.Analysis.N04PulledFieldsCorrectionCircleFixedBase

/-!
# The actual residual-substituted displacement at one fixed low base

The independent-residual circle displacement is evaluated on the graph
of the retained N02 residual. The graph and its genuine tower use the
same sector parameter and the original residual decoder identity.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

local instance n04PulledFieldsActualDisplacementStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

/-- Substitution of the actual residual retains one low order for all
parameter orders and all admissible radius selectors. -/
theorem N01Properties.n04PulledFields_fixedBase_actualReturnCorrectionPulledDisplacement
    {I : Type*} {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hflow : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m r,
      r ∈ Icc (C.left m) (C.right m) → ∀ θ,
        1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ∧
        deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ≤ 3 / 2)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (hR : N02Properties D T S C R base ε)
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    N04PulledFieldsFixedBaseFamily (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun i z => hN.returnCorrectionPulledDisplacementCircleLinear hS hT χ hχrange
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
  have hd := hN.n04PulledFields_fixedBase_returnCorrectionPulledDisplacementCircleLinear
    hS hT hflow χ hχrange rsel hrsel
  exact N04PulledFieldsFixedBaseFamily.comp
    (Y := fun n => H.level n) (bond := H.bond)
    (p := p) (q := pairGrading p H.grading) (r := H.grading)
    (U := sectorNeighborhood S base ε ε)
    (V := sectorNeighborhood S base ε ε ×ˢ (univ : Set H.Space))
    (f := fun (_ : I) z => (z, R.residual (liftSectorParameter S C z)))
    (g := fun i (x : (StateDirections S × ℝ) × H.Space) =>
      hN.returnCorrectionPulledDisplacementCircleLinear hS hT χ hχrange
        (rsel i) (hrsel i) x.1 x.2)
    hd hp (n04PulledFields_selectorParameterInterpolation hS)
    (hid.prodMk hp he) hU (hU.prod isOpen_univ) (fun _ _ hz => ⟨hz, mem_univ _⟩)

end ContinuousFlexibility.Statements
