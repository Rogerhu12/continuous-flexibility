import ContinuousFlexibility.Analysis.N01ReturnVelocityUniformBounds

/-!
# Uniform estimates for the residual of any actual N02 construction

The decoder clause in N02 identifies its residual with the already
constructed circle residual on the common sector neighborhood. Thus the
numerical bounds for the actual construction apply to the same supplied
return operator, including its use in the pulled displacement. No
uniform constant is extracted from an abstract smooth-tame assertion.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

local instance n01ResidualUniformBoundsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {I : Type*} {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hR : N02Properties D T S C R base ε)

include hR in
theorem N01Properties.sectorReturnResidualCircle_eq_of_N02
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) :
    hN.sectorReturnResidualCircle hS hT z = R.residual (liftSectorParameter S C z) := by
  apply (hS.2.1 (3 / 4 : ℝ)).2.2.2.2.2.1
  funext m θ
  exact (hN.sectorReturnResidualCircle_decode hS hT z hz m θ).trans
    ((hR.2.1 (liftSectorParameter S C z)
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hN.2.2.1.liftSectorParameter_sector z) m θ).symm)

variable
  (hflow : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m r,
    r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ∧
      deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ≤ 3 / 2)

include hN hS hT hR hflow in
theorem N01Properties.uniformSmoothFamilyOn_returnResidual_of_N02 :
    UniformSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun (_ : I) z => R.residual (liftSectorParameter S C z)) :=
  (hN.uniformSmoothFamilyOn_sectorReturnResidualCircle (I := I) hS hT hflow).congr
    (fun _ z hz => hN.sectorReturnResidualCircle_eq_of_N02 hS hT hR z hz)

include hR hflow in
theorem N01Properties.uniformSmoothFamilyOn_returnCorrectionPulledResidual_of_N02
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    UniformSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun i z => hN.returnCorrectionPulledDisplacementCircleLinear hS hT χ hχrange
        (rsel i) (hrsel i) z (R.residual (liftSectorParameter S C z))) :=
  (hN.uniformSmoothFamilyOn_returnCorrectionPulledResidualCircle
    hS hT hflow χ hχrange rsel hrsel).congr
      (fun i z hz => congrArg
        (hN.returnCorrectionPulledDisplacementCircleLinear hS hT χ hχrange
          (rsel i) (hrsel i) z)
        (hN.sectorReturnResidualCircle_eq_of_N02 hS hT hR z hz))

include hR hflow in
theorem N01Properties.returnCorrectionPulledResidual_uniformFamilyJetBounds_of_N02
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m))
    (J : ∀ i, SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => hN.returnCorrectionPulledDisplacementCircleLinear hS hT χ hχrange
        (rsel i) (hrsel i) z (R.residual (liftSectorParameter S C z)))) :
    UniformFamilyJetBounds (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading J :=
  (hN.uniformSmoothFamilyOn_returnCorrectionPulledResidual_of_N02
    hS hT hR hflow χ hχrange rsel hrsel).jets J

end ContinuousFlexibility.Statements
