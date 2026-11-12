import ContinuousFlexibility.Analysis.ReturnCorrectionComponentIntegral
import ContinuousFlexibility.Analysis.SolveNormalization
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Bilinearity of the actual independent-residual differential error

Spatial differentiation is linear on the actual differentiable flux
families. The decoder of the existing height-pair space and the existing
coefficient-error linear map supply the two factors. Consequently the
actual scalar differential error is bilinear in the independent residual
and height increment. Its source compatibility is already proved; only
weighted height membership remains for realization in the source space.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff Classical

set_option backward.isDefEq.respectTransparency false

/-- Differentiate an actual linear family on an open region, extending
the result by zero outside that region. Differentiability is required
before asserting additivity of the total Fréchet derivative. -/
def spatialDirectionalLinear {E : Type*} [AddCommGroup E] [Module ℝ E]
    (U : Set PolarPoint) (v : PolarPoint) (F : E →ₗ[ℝ] (PolarPoint → ℝ))
    (hF : ∀ e p, p ∈ U → DifferentiableAt ℝ (F e) p) :
    E →ₗ[ℝ] (PolarPoint → ℝ) := by
  classical
  exact {
    toFun := fun e p => if p ∈ U then fderiv ℝ (F e) p v else 0
    map_add' := by
      intro e e'
      funext p
      by_cases hp : p ∈ U
      · simp only [if_pos hp, map_add, fderiv_add (hF e p hp) (hF e' p hp),
          ContinuousLinearMap.add_apply, Pi.add_apply]
      · simp only [if_neg hp, Pi.add_apply, add_zero]
    map_smul' := by
      intro c e
      funext p
      by_cases hp : p ∈ U
      · simp only [if_pos hp, map_smul, fderiv_const_smul (hF e p hp) c,
          ContinuousLinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply]
      · simp only [if_neg hp, Pi.smul_apply, smul_zero, RingHom.id_apply] }

theorem spatialDirectionalLinear_apply {E : Type*} [AddCommGroup E] [Module ℝ E]
    (U : Set PolarPoint) (v : PolarPoint) (F : E →ₗ[ℝ] (PolarPoint → ℝ))
    (hF : ∀ e p, p ∈ U → DifferentiableAt ℝ (F e) p) (e : E) (p : PolarPoint) :
    spatialDirectionalLinear U v F hF e p =
      if p ∈ U then fderiv ℝ (F e) p v else 0 := by
  classical
  rfl

/-- The same spatial operation preserves both arguments of an actual
bilinear differentiable family. -/
def spatialDirectionalBilinear {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (U : Set PolarPoint) (v : PolarPoint) (B : E →ₗ[ℝ] F →ₗ[ℝ] (PolarPoint → ℝ))
    (hB : ∀ e f p, p ∈ U → DifferentiableAt ℝ (B e f) p) :
    E →ₗ[ℝ] F →ₗ[ℝ] (PolarPoint → ℝ) := by
  classical
  exact {
    toFun := fun e => spatialDirectionalLinear U v (B e) (hB e)
    map_add' := by
      intro e e'
      apply LinearMap.ext
      intro f
      funext p
      by_cases hp : p ∈ U
      · simp only [spatialDirectionalLinear_apply, if_pos hp, map_add,
          LinearMap.add_apply, fderiv_add (hB e f p hp) (hB e' f p hp),
          ContinuousLinearMap.add_apply, Pi.add_apply]
      · simp only [spatialDirectionalLinear_apply, if_neg hp,
          LinearMap.add_apply, Pi.add_apply, add_zero]
    map_smul' := by
      intro c e
      apply LinearMap.ext
      intro f
      funext p
      by_cases hp : p ∈ U
      · simp only [spatialDirectionalLinear_apply, if_pos hp, map_smul,
          LinearMap.smul_apply, fderiv_const_smul (hB e f p hp) c,
          ContinuousLinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply]
      · simp only [spatialDirectionalLinear_apply, if_neg hp,
          LinearMap.smul_apply, Pi.smul_apply, smul_zero, RingHom.id_apply] }

theorem spatialDirectionalBilinear_apply {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (U : Set PolarPoint) (v : PolarPoint) (B : E →ₗ[ℝ] F →ₗ[ℝ] (PolarPoint → ℝ))
    (hB : ∀ e f p, p ∈ U → DifferentiableAt ℝ (B e f) p) (e : E) (f : F) (p : PolarPoint) :
    spatialDirectionalBilinear U v B hB e f p =
      if p ∈ U then fderiv ℝ (B e f) p v else 0 := by
  classical
  rfl

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

/-- Coordinate differentiation of the already existing height-pair
decoder, rather than a second height representation. -/
def heightPairPartialLinear
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (v : PolarPoint) :
    HeightPair S →ₗ[ℝ] (PolarPoint → ℝ) :=
  spatialDirectionalLinear univ v (heightPairFieldLinear S)
    (fun η p _ => by
      have hu : ContDiff ℝ ∞ (heightPairField S η) :=
        physical_height_with_cutoff_contDiff hT hS
          (by norm_num : (0 : ℝ) < 3 / 4) η.1 η.2
      rw [heightPairFieldLinear_apply]
      exact hu.differentiable (by simp) p)

theorem heightPairPartialLinear_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (v : PolarPoint)
    (η : HeightPair S) (p : PolarPoint) :
    heightPairPartialLinear hS hT v η p = fderiv ℝ (heightPairField S η) p v := by
  simp only [heightPairPartialLinear, spatialDirectionalLinear_apply, mem_univ,
    if_true, heightPairFieldLinear_apply]

def returnCorrectionRadialErrorFluxBilinear
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (C : NonlinearGeometryData S) (R : ReturnEquationData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) :
    CircleSpace S →ₗ[ℝ] HeightPair S →ₗ[ℝ] (PolarPoint → ℝ) :=
  (LinearMap.mul ℝ (PolarPoint → ℝ)).compl₁₂
    (LinearMap.pi fun p => (LinearMap.fst ℝ ℝ ℝ).comp
      (returnCorrectionCoefficientError D S C R χ z p))
    (heightPairPartialLinear hS hT (0, 1))

theorem returnCorrectionRadialErrorFluxBilinear_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (C : NonlinearGeometryData S) (R : ReturnEquationData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ)
    (ρ : CircleSpace S) (η : HeightPair S) :
    returnCorrectionRadialErrorFluxBilinear hS hT C R χ z ρ η =
      returnCorrectionRadialErrorFlux D S C R χ z ρ η := by
  funext p
  simp only [returnCorrectionRadialErrorFluxBilinear, LinearMap.compl₁₂_apply,
    LinearMap.mul_apply', Pi.mul_apply, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, heightPairPartialLinear_apply, returnCorrectionRadialErrorFlux,
    angularPartial]

def returnCorrectionAngularErrorFluxBilinear
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (C : NonlinearGeometryData S) (R : ReturnEquationData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) :
    CircleSpace S →ₗ[ℝ] HeightPair S →ₗ[ℝ] (PolarPoint → ℝ) :=
  (LinearMap.mul ℝ (PolarPoint → ℝ)).compl₁₂
      (LinearMap.pi fun p => (LinearMap.fst ℝ ℝ ℝ).comp
        (returnCorrectionCoefficientError D S C R χ z p))
      (heightPairPartialLinear hS hT (1, 0)) +
    (LinearMap.mul ℝ (PolarPoint → ℝ)).compl₁₂
      (LinearMap.pi fun p => (LinearMap.snd ℝ ℝ ℝ).comp
        (returnCorrectionCoefficientError D S C R χ z p))
      (heightPairPartialLinear hS hT (0, 1))

theorem returnCorrectionAngularErrorFluxBilinear_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (C : NonlinearGeometryData S) (R : ReturnEquationData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ)
    (ρ : CircleSpace S) (η : HeightPair S) :
    returnCorrectionAngularErrorFluxBilinear hS hT C R χ z ρ η =
      returnCorrectionAngularErrorFlux D S C R χ z ρ η := by
  funext p
  simp only [returnCorrectionAngularErrorFluxBilinear, LinearMap.add_apply, Pi.add_apply,
    LinearMap.compl₁₂_apply, LinearMap.mul_apply', Pi.mul_apply, LinearMap.pi_apply,
    LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, heightPairPartialLinear_apply,
    returnCorrectionAngularErrorFlux, radialPartial, angularPartial]

section ActualError

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN01 : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (R : ReturnEquationData S) {z : AnnularState S × ℝ}
  (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
  (hdisc : ∀ m p, p.1 ∈ Icc ((2 * C.left m + C.right m) / 3)
      ((C.left m + 2 * C.right m) / 3) →
    0 < (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)

include hN01 hS hT hz hsector hdisc

/-- The actual independent-residual differential error as a bilinear map
on the original residual and height-pair spaces. -/
def returnCorrectionResidualErrorBilinear :
    CircleSpace S →ₗ[ℝ] HeightPair S →ₗ[ℝ] (PolarPoint → ℝ) :=
  spatialDirectionalBilinear (annularOpen D) (1, 0)
      (returnCorrectionRadialErrorFluxBilinear hS hT C R (returnCorrectionCutoffs C) z)
      (fun ρ η p hp => by
        rw [returnCorrectionRadialErrorFluxBilinear_apply]
        exact (hN01.returnCorrectionErrorFluxes_contDiffAt_one hS hT R hz hsector hdisc
          ρ η p hp).1.differentiableAt one_ne_zero) +
    spatialDirectionalBilinear (annularOpen D) (0, 1)
      (returnCorrectionAngularErrorFluxBilinear hS hT C R (returnCorrectionCutoffs C) z)
      (fun ρ η p hp => by
        rw [returnCorrectionAngularErrorFluxBilinear_apply]
        exact (hN01.returnCorrectionErrorFluxes_contDiffAt_one hS hT R hz hsector hdisc
          ρ η p hp).2.differentiableAt one_ne_zero)

theorem returnCorrectionResidualErrorBilinear_apply
    (ρ : CircleSpace S) (η : HeightPair S) :
    returnCorrectionResidualErrorBilinear hN01 hS hT R hz hsector hdisc ρ η =
      returnCorrectionResidualErrorField D S C R (returnCorrectionCutoffs C) z ρ η := by
  classical
  funext p
  simp only [returnCorrectionResidualErrorBilinear, LinearMap.add_apply, Pi.add_apply,
    spatialDirectionalBilinear_apply, returnCorrectionRadialErrorFluxBilinear_apply,
    returnCorrectionAngularErrorFluxBilinear_apply]
  by_cases hp : p ∈ annularOpen D
  · simp only [if_pos hp, returnCorrectionResidualErrorField, if_pos hp,
      radialPartial, angularPartial]
    unfold returnCorrectionRadialErrorFlux returnCorrectionAngularErrorFlux
    rfl
  · simp only [if_neg hp, returnCorrectionResidualErrorField, if_neg hp, add_zero]

theorem returnCorrectionResidualErrorBilinear_sourceIntegral_eq_zero
    (ρ : CircleSpace S) (η : HeightPair S) :
    physicalSourceIntegral D
      (returnCorrectionResidualErrorBilinear hN01 hS hT R hz hsector hdisc ρ η) = 0 := by
  rw [returnCorrectionResidualErrorBilinear_apply]
  exact hN01.returnCorrectionResidualErrorField_sourceIntegral_eq_zero_of_collar
    hS hT R hz hsector hdisc ρ η

/-- The remaining source-realization obligation is exactly weighted
height membership; the source integral has already been proved zero. -/
theorem returnCorrectionResidualErrorBilinear_mem_source_range_iff
    (ρ : CircleSpace S) (η : HeightPair S) :
    returnCorrectionResidualErrorBilinear hN01 hS hT R hz hsector hdisc ρ η ∈
        LinearMap.range (physicalSourceDecode S) ↔
      HeightMember D T (3 / 4 : ℝ)
        (returnCorrectionResidualErrorField D S C R (returnCorrectionCutoffs C) z ρ η) := by
  rw [physicalSourceDecode_mem_range_iff hS,
    returnCorrectionResidualErrorBilinear_apply]
  simp only [hN01.returnCorrectionResidualErrorField_sourceIntegral_eq_zero_of_collar
    hS hT R hz hsector hdisc ρ η, and_true]

end ActualError

end ContinuousFlexibility.Statements
