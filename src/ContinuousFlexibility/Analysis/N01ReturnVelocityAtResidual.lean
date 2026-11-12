import ContinuousFlexibility.Analysis.N01ReturnVelocitySmoothTame

/-!
# The actual velocity with the actual residual substituted

The independently linear velocity has already been realized in the
original circle model. Composing its genuine tower with the actual N02
residual gives its state dependence after substitution. Fixed angular
evaluations of both versions are retained for coefficient reconstruction.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance n01ReturnVelocityAtResidualStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
  (χ : ℕ → ℝ → ℝ)
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
  (hcutoff : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
    |iteratedDeriv k (χ m) r| ≤ A * radialE (D.cellIndex (j m)) ^ P)
  (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))

theorem N01Properties.smoothTameOn_returnCorrectionVelocity_at_residual
    (hR : N02Properties D T S C R base ε) :
    SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun z : StateDirections S × ℝ =>
        hN.returnCorrectionVelocityCircleLinear hS hT j hcell χ hχrange hcutoff rsel hrsel
          z (R.residual (liftSectorParameter S C z))) := by
  let H := S.circle (3 / 4 : ℝ)
  let p := pairGrading (sectorGrading S) realGrading
  let U := sectorNeighborhood S base ε ε
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  letI : ∀ n, CompleteSpace (H.level n) :=
    fun n => (hH.2.1 n).isComplete.completeSpace_coe
  have hp : Monotone p := sectorPairGrading_monotone S
  have ht : WithSeminorms p := sectorPairGrading_withSeminorms S
  have htop : WithSeminorms H.grading :=
    withSeminorms_graded (fun n => H.level n) H.bond
  have hU : IsOpen U := sectorNeighborhood_isOpen S base ε ε
  have hid : SmoothTameOn p p U (fun z : StateDirections S × ℝ => z) :=
    smoothTameOn_restrict_open
      (smoothTameOn_continuousLinear (ContinuousLinearMap.id ℝ (StateDirections S × ℝ))
        (IsTameLinear.id p)) hU (subset_univ _)
  have hres : SmoothTameOn p H.grading U
      (fun z => R.residual (liftSectorParameter S C z)) := by
    rcases hR with ⟨_, _, _, _, _, _, _, _, _, _, h⟩
    exact h
  have hv := hN.smoothTameOn_returnCorrectionVelocityCircleLinear
    hS hT j hcell χ hχrange hcutoff rsel hrsel
  exact smoothTameOn_comp_topological
    (G := fun n => H.level n) (g := H.bond)
    (p := p) (q := pairGrading p H.grading) (r := H.grading)
    (U := U) (V := U ×ˢ (univ : Set H.Space))
    (u := fun z : StateDirections S × ℝ => (z, R.residual (liftSectorParameter S C z)))
    (v := fun x : (StateDirections S × ℝ) × H.Space =>
      hN.returnCorrectionVelocityCircleLinear hS hT j hcell χ hχrange hcutoff rsel hrsel
        x.1 x.2)
    hp ht (withSeminorms_pairGrading ht htop)
    hU (hU.prod isOpen_univ) (fun z hz => ⟨hz, mem_univ _⟩)
    (smoothTameOn_prodMk hp ht hid hres) hv

def N01Properties.returnCorrectionVelocity_pointTower (m : ℕ) (θ : ℝ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun x : (StateDirections S × ℝ) × CircleSpace S =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1)
          m (rsel m, θ) x.2) := by
  let J := (hN.smoothTameOn_returnCorrectionVelocityCircleLinear
    hS hT j hcell χ hχrange hcutoff rsel hrsel).choose
  apply (circleDecodedAngularDirections (hS.2.1 (3 / 4 : ℝ)) J 0 m θ).congrOn
  intro x hx
  simp only [iteratedDeriv_zero]
  exact hN.returnCorrectionVelocityCircleLinear_decode hS hT j hcell χ hχrange hcutoff
    rsel hrsel x.1 hx.1 x.2 m θ

def N01Properties.returnCorrectionVelocity_actual_pointTower
    (hR : N02Properties D T S C R base ε) (m : ℕ) (θ : ℝ) :
    SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z : StateDirections S × ℝ =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C z)
          m (rsel m, θ) (R.residual (liftSectorParameter S C z))) := by
  let J := (hN.smoothTameOn_returnCorrectionVelocity_at_residual
    hS hT j hcell χ hχrange hcutoff rsel hrsel hR).choose
  apply (circleDecodedAngularDirections (hS.2.1 (3 / 4 : ℝ)) J 0 m θ).congrOn
  intro z hz
  simp only [iteratedDeriv_zero]
  exact hN.returnCorrectionVelocityCircleLinear_decode hS hT j hcell χ hχrange hcutoff
    rsel hrsel z hz (R.residual (liftSectorParameter S C z)) m θ

end ContinuousFlexibility.Statements
