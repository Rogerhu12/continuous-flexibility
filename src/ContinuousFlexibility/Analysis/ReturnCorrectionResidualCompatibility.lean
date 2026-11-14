module

public import ContinuousFlexibility.Analysis.ReturnCorrectionResidualError
public import ContinuousFlexibility.Scalar.Conservation

/-!
# Symmetry and compatibility of the actual residual error

The independent residual argument is retained throughout. Reflection
symmetrization gives the required coefficient parity before the argument
is specialized to the actual residual. The actual component selector
also makes both error fluxes zero at the radial endpoints.

The source-integral calculation uses the existing rectangle conservation
theorem, hence actual one-dimensional FTC and Fubini. Its remaining
analytic input is the regularity of the actual error fluxes on the closed
rectangle; it does not assume that the error already belongs to the
source kernel.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem returnCorrectionDriftLinear_reflection
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (m : ℕ) (r θ : ℝ)
    (ρ : CircleSpace S) :
    returnCorrectionDriftLinear D S C χ z m (r, -θ) ρ =
      -returnCorrectionDriftLinear D S C χ z m (r, θ) ρ := by
  simp only [returnCorrectionDriftLinear_apply, neg_neg]
  ring

theorem returnCorrectionSpeedLinear_reflection
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (m : ℕ) (r θ : ℝ)
    (ρ : CircleSpace S) :
    returnCorrectionSpeedLinear D S C χ z m (r, -θ) ρ =
      returnCorrectionSpeedLinear D S C χ z m (r, θ) ρ := by
  simp only [returnCorrectionSpeedLinear_apply, neg_neg]
  ring

theorem returnCorrectionLocalCoefficientError_reflection
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (C : NonlinearGeometryData S)
    (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ)
    (z : AnnularState S × ℝ) (m : ℕ) (ρ : CircleSpace S) (r θ : ℝ) :
    (returnCorrectionLocalCoefficientError D S C R χ z m (r, -θ) ρ).1 =
        -(returnCorrectionLocalCoefficientError D S C R χ z m (r, θ) ρ).1 ∧
    (returnCorrectionLocalCoefficientError D S C R χ z m (r, -θ) ρ).2 =
        (returnCorrectionLocalCoefficientError D S C R χ z m (r, θ) ρ).2 := by
  have hpar := originalCoefficients_parity_of_physical hS C z r θ
  simp only [returnCorrectionLocalCoefficientError, returnCoefficientError_apply,
    hpar.1, hpar.2.1, hpar.2.2, neg_sq, neg_div,
    returnCorrectionDriftLinear_reflection, returnCorrectionSpeedLinear_reflection]
  constructor <;> ring

theorem returnCorrectionCoefficientError_reflection
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (C : NonlinearGeometryData S)
    (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ)
    (z : AnnularState S × ℝ) (ρ : CircleSpace S) (r θ : ℝ) :
    (returnCorrectionCoefficientError D S C R χ z (r, -θ) ρ).1 =
        -(returnCorrectionCoefficientError D S C R χ z (r, θ) ρ).1 ∧
    (returnCorrectionCoefficientError D S C R χ z (r, -θ) ρ).2 =
        (returnCorrectionCoefficientError D S C R χ z (r, θ) ρ).2 := by
  classical
  by_cases h : ∃ m, r ∈ Ioo (C.left m) (C.right m) ∧ deriv (χ m) r ≠ 0
  · simpa only [returnCorrectionCoefficientError, dif_pos h] using
      returnCorrectionLocalCoefficientError_reflection hS C R χ z
        (Classical.choose h) ρ r θ
  · simp only [returnCorrectionCoefficientError, dif_neg h, LinearMap.zero_apply,
      Prod.fst_zero, Prod.snd_zero, neg_zero, and_self]

theorem returnCorrectionCoefficientError_eq_zero_of_outside
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions D S C) (R : ReturnEquationData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (p : PolarPoint)
    (hp : p.1 ∉ Ioo D.a D.b) :
    returnCorrectionCoefficientError D S C R χ z p = 0 := by
  classical
  have h : ¬ ∃ m, p.1 ∈ Ioo (C.left m) (C.right m) ∧ deriv (χ m) p.1 ≠ 0 := by
    rintro ⟨m, hm, _⟩
    exact hp ⟨(hC.1 m).1.trans hm.1, hm.2.trans (hC.1 m).2.2⟩
  simp only [returnCorrectionCoefficientError, dif_neg h]

/-- The actual radial error flux from the frozen coefficient map. -/
def returnCorrectionRadialErrorFlux (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ)
    (z : AnnularState S × ℝ) (ρ : CircleSpace S) (η : HeightPair S)
    (p : PolarPoint) : ℝ :=
  (returnCorrectionCoefficientError D S C R χ z p ρ).1 *
    angularPartial (heightPairField S η) p

/-- The actual angular error flux from the frozen coefficient map. -/
def returnCorrectionAngularErrorFlux (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ)
    (z : AnnularState S × ℝ) (ρ : CircleSpace S) (η : HeightPair S)
    (p : PolarPoint) : ℝ :=
  (returnCorrectionCoefficientError D S C R χ z p ρ).1 *
      radialPartial (heightPairField S η) p +
    (returnCorrectionCoefficientError D S C R χ z p ρ).2 *
      angularPartial (heightPairField S η) p

theorem heightPairField_even_of_physical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (η : HeightPair S) (r θ : ℝ) :
    heightPairField S η (r, -θ) = heightPairField S η (r, θ) := by
  have h := ((hS.1 (3 / 4 : ℝ)).2.2.2.1 η.1).2.1 r θ
  simp only [heightPairField, h]

theorem returnCorrectionErrorFluxes_reflection
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (C : NonlinearGeometryData S)
    (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ)
    (z : AnnularState S × ℝ) (ρ : CircleSpace S) (η : HeightPair S) (r θ : ℝ) :
    returnCorrectionRadialErrorFlux D S C R χ z ρ η (r, -θ) =
        returnCorrectionRadialErrorFlux D S C R χ z ρ η (r, θ) ∧
    returnCorrectionAngularErrorFlux D S C R χ z ρ η (r, -θ) =
        -returnCorrectionAngularErrorFlux D S C R χ z ρ η (r, θ) := by
  have hcoeff := returnCorrectionCoefficientError_reflection hS C R χ z ρ r θ
  have hur := radialPartial_of_even (heightPairField S η)
    (heightPairField_even_of_physical hS η) r θ
  have huθ := angularPartial_of_even (heightPairField S η)
    (heightPairField_even_of_physical hS η) r θ
  simp only [returnCorrectionRadialErrorFlux, returnCorrectionAngularErrorFlux,
    hcoeff.1, hcoeff.2, hur, huθ]
  constructor <;> ring

theorem returnCorrectionResidualErrorField_even
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (C : NonlinearGeometryData S)
    (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ)
    (z : AnnularState S × ℝ) (ρ : CircleSpace S) (η : HeightPair S) (r θ : ℝ) :
    returnCorrectionResidualErrorField D S C R χ z ρ η (r, -θ) =
      returnCorrectionResidualErrorField D S C R χ z ρ η (r, θ) := by
  classical
  have hF := radialPartial_of_even (returnCorrectionRadialErrorFlux D S C R χ z ρ η)
    (fun s t => (returnCorrectionErrorFluxes_reflection hS C R χ z ρ η s t).1) r θ
  have hG := angularPartial_of_odd (returnCorrectionAngularErrorFlux D S C R χ z ρ η)
    (fun s t => (returnCorrectionErrorFluxes_reflection hS C R χ z ρ η s t).2) r θ
  by_cases hr : r ∈ Ioo D.a D.b
  · have hp : (r, θ) ∈ annularOpen D := ⟨hr, mem_univ _⟩
    have hp' : (r, -θ) ∈ annularOpen D := ⟨hr, mem_univ _⟩
    simp only [returnCorrectionResidualErrorField, if_pos hp, if_pos hp']
    exact congrArg₂ (· + ·) hF hG
  · have hp : (r, θ) ∉ annularOpen D := fun h => hr h.1
    have hp' : (r, -θ) ∉ annularOpen D := fun h => hr h.1
    simp only [returnCorrectionResidualErrorField, if_neg hp, if_neg hp']

theorem returnCorrectionErrorFluxes_zero_outside
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions D S C) (R : ReturnEquationData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ)
    (ρ : CircleSpace S) (η : HeightPair S) (p : PolarPoint)
    (hp : p.1 ∉ Ioo D.a D.b) :
    returnCorrectionRadialErrorFlux D S C R χ z ρ η p = 0 ∧
      returnCorrectionAngularErrorFlux D S C R χ z ρ η p = 0 := by
  simp only [returnCorrectionRadialErrorFlux, returnCorrectionAngularErrorFlux,
    returnCorrectionCoefficientError_eq_zero_of_outside hC R χ z p hp,
    LinearMap.zero_apply, Prod.fst_zero, Prod.snd_zero, zero_mul, zero_add, and_self]

/-- Actual divergence compatibility, using the existing FTC/Fubini
rectangle conservation theorem with the one-form `-G dr + F dθ`. -/
theorem physicalSourceIntegral_divergence_eq_zero
    (D : ReferenceData) (F G : PolarPoint → ℝ)
    (hF : ∀ p ∈ uIcc D.a D.b ×ˢ uIcc (0 : ℝ) Real.pi, ContDiffAt ℝ 1 F p)
    (hG : ∀ p ∈ uIcc D.a D.b ×ˢ uIcc (0 : ℝ) Real.pi, ContDiffAt ℝ 1 G p)
    (hperiod : ∀ r ∈ uIcc D.a D.b, G (r, Real.pi) = G (r, 0))
    (hboundary : ∀ θ ∈ uIcc (0 : ℝ) Real.pi, F (D.b, θ) = F (D.a, θ)) :
    physicalSourceIntegral D (fun p => radialPartial F p + angularPartial G p) = 0 := by
  let α : PlaneOneForm := ⟨fun p => -G p, F⟩
  have h := integral_exteriorCoefficient_eq_zero (α := α)
    (fun p hp => (hG p hp).neg) hF
    (fun r hr => congrArg Neg.neg (hperiod r hr)) hboundary
  change (∫ r in D.a..D.b, ∫ θ in (0 : ℝ)..Real.pi,
    radialPartial F (r, θ) - angularPartial (fun p => -G p) (r, θ)) = 0 at h
  simp only [angularPartial_neg_total, sub_neg_eq_add] at h
  change (∫ r in D.a..D.b, (1 / Real.pi) *
    ∫ θ in (0 : ℝ)..Real.pi, radialPartial F (r, θ) + angularPartial G (r, θ)) = 0
  rw [intervalIntegral.integral_const_mul, h, mul_zero]

theorem physicalSourceIntegral_congr_on_annularOpen
    (D : ReferenceData) (hab : D.a ≤ D.b) (f g : PolarPoint → ℝ)
    (hfg : ∀ p ∈ annularOpen D, f p = g p) :
    physicalSourceIntegral D f = physicalSourceIntegral D g := by
  apply intervalIntegral.integral_congr_Ioo_of_le hab
  intro r hr
  apply congrArg ((1 / Real.pi) * ·)
  apply intervalIntegral.integral_congr
  intro θ _
  exact hfg (r, θ) ⟨hr, mem_univ _⟩

/-- Compatibility for the actual independent-residual error field.
The radial boundary terms are discharged by the actual component
selector; only flux regularity and angular matching remain. -/
theorem returnCorrectionResidualErrorField_sourceIntegral_eq_zero
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions D S C) (R : ReturnEquationData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ)
    (ρ : CircleSpace S) (η : HeightPair S)
    (hF : ∀ p ∈ uIcc D.a D.b ×ˢ uIcc (0 : ℝ) Real.pi,
      ContDiffAt ℝ 1 (returnCorrectionRadialErrorFlux D S C R χ z ρ η) p)
    (hG : ∀ p ∈ uIcc D.a D.b ×ˢ uIcc (0 : ℝ) Real.pi,
      ContDiffAt ℝ 1 (returnCorrectionAngularErrorFlux D S C R χ z ρ η) p)
    (hperiod : ∀ r ∈ uIcc D.a D.b,
      returnCorrectionAngularErrorFlux D S C R χ z ρ η (r, Real.pi) =
        returnCorrectionAngularErrorFlux D S C R χ z ρ η (r, 0)) :
    physicalSourceIntegral D (returnCorrectionResidualErrorField D S C R χ z ρ η) = 0 := by
  have hab : D.a ≤ D.b := ((hC.1 0).1.trans ((hC.1 0).2.1.trans (hC.1 0).2.2)).le
  have hfield : ∀ p ∈ annularOpen D,
      returnCorrectionResidualErrorField D S C R χ z ρ η p =
        radialPartial (returnCorrectionRadialErrorFlux D S C R χ z ρ η) p +
          angularPartial (returnCorrectionAngularErrorFlux D S C R χ z ρ η) p := by
    intro p hp
    unfold returnCorrectionResidualErrorField
    rw [if_pos hp]
    rfl
  rw [physicalSourceIntegral_congr_on_annularOpen D hab _ _ hfield]
  apply physicalSourceIntegral_divergence_eq_zero D _ _ hF hG hperiod
  intro θ _
  rw [(returnCorrectionErrorFluxes_zero_outside hC R χ z ρ η (D.b, θ)
    (by simp)).1,
    (returnCorrectionErrorFluxes_zero_outside hC R χ z ρ η (D.a, θ)
      (by simp)).1]

end ContinuousFlexibility.Statements
