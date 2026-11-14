module

public import ContinuousFlexibility.Analysis.AngularSpectralCoordinates
public import ContinuousFlexibility.Analysis.AngularRealSpectralDecomposition
public import ContinuousFlexibility.Analysis.AngularYosida

/-!
# Angular Sobolev scales on a general Hilbert space

The spectral decomposition is proved for both scalar fields. The public
scale is built from the original bounded resolvent; no coordinate system
or decomposition is an assumption on its users.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

/-- A proved scalar-field interface for the spectral theorem used here.
Instances below discharge it for both real and complex Hilbert spaces. -/
class HasAngularSpectralDecomposition (𝕜 H : Type*) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H] : Prop where
  decompose (A : AngularResolventData 𝕜 H) :
    IsHilbertSum 𝕜 (fun n => angularResolventEigenspace A.operator n)
      (fun n => (angularResolventEigenspace A.operator n).subtypeₗᵢ)

instance {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    HasAngularSpectralDecomposition ℂ H where
  decompose A := angularResolvent_isHilbertSum A.selfAdjoint A.injective A.spectrum_subset

instance {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] :
    HasAngularSpectralDecomposition ℝ H where
  decompose A := angularRealResolvent_isHilbertSum A.selfAdjoint A.injective A.spectrum_subset

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]
  [HasAngularSpectralDecomposition 𝕜 H]

namespace AngularResolventData

/-- The canonical full spectral coordinates of the given angular resolvent. -/
def coordinates (A : AngularResolventData 𝕜 H) :
    H ≃ₗᵢ[𝕜] lp (fun n => angularResolventEigenspace A.operator n) 2 :=
  angularResolventCoordinates A.operator (HasAngularSpectralDecomposition.decompose A)

/-- Membership in the integer angular Sobolev space. -/
def Sobolev (A : AngularResolventData 𝕜 H) (p : ℕ) (v : H) : Prop :=
  MemAngularSobolev (𝕜 := 𝕜) p (A.coordinates v)

/-- The exact Japanese-bracket norm `‖⟨Λ⟩^p v‖`, on its Sobolev domain. -/
def sobolevNorm (A : AngularResolventData 𝕜 H) (p : ℕ) (v : H) : ℝ :=
  angularSobolevNorm (𝕜 := 𝕜) p (A.coordinates v)

/-- The angular frequency action, extended by zero off its maximal domain. -/
def derivative (A : AngularResolventData 𝕜 H) (v : H) : H :=
  A.coordinates.symm (angularDerivative (𝕜 := 𝕜) (A.coordinates v))

@[simp] theorem coordinates_derivative (A : AngularResolventData 𝕜 H) (v : H) :
    A.coordinates (A.derivative v) = angularDerivative (𝕜 := 𝕜) (A.coordinates v) :=
  A.coordinates.apply_symm_apply _

@[simp] theorem sobolev_zero (A : AngularResolventData 𝕜 H) (v : H) : A.Sobolev 0 v :=
  memAngularSobolev_zero _

@[simp] theorem sobolevNorm_zero (A : AngularResolventData 𝕜 H) (v : H) :
    A.sobolevNorm 0 v = ‖v‖ := by
  rw [sobolevNorm, angularSobolevNorm_zero, A.coordinates.norm_map]

theorem Sobolev.of_le {A : AngularResolventData 𝕜 H} {p q : ℕ} {v : H}
    (hv : A.Sobolev q v) (hpq : p ≤ q) : A.Sobolev p v :=
  MemAngularSobolev.of_le hv hpq

theorem coordinates_operator (A : AngularResolventData 𝕜 H) (v : H) (n : ℕ) :
    A.coordinates (A.operator v) n =
      (angularResolventEigenvalue n : 𝕜) • A.coordinates v n :=
  angularResolventCoordinates_operator_apply A.operator
    (HasAngularSpectralDecomposition.decompose A) v n

end AngularResolventData

section Conjugation

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Transport a bounded operator through a Hilbert-space isometry. -/
def angularConjugate (e : H ≃ₗᵢ[𝕜] F) (T : H →L[𝕜] H) : F →L[𝕜] F :=
  e.toLinearIsometry.toContinuousLinearMap.comp
    (T.comp e.symm.toLinearIsometry.toContinuousLinearMap)

@[simp] theorem angularConjugate_apply (e : H ≃ₗᵢ[𝕜] F) (T : H →L[𝕜] H) (v : F) :
    angularConjugate e T v = e (T (e.symm v)) := by
  simp only [angularConjugate, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]

@[simp] theorem angularConjugate_apply_coordinates (e : H ≃ₗᵢ[𝕜] F)
    (T : H →L[𝕜] H) (v : H) : angularConjugate e T (e v) = e (T v) := by
  rw [angularConjugate_apply, e.symm_apply_apply]

/-- Unitary transport preserves the base inverse norm exactly. -/
theorem norm_angularConjugate (e : H ≃ₗᵢ[𝕜] F) (T : H →L[𝕜] H) :
    ‖angularConjugate e T‖ = ‖T‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    intro v
    rw [angularConjugate_apply, e.norm_map]
    simpa only [e.symm.norm_map] using T.le_opNorm (e.symm v)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    have h := (angularConjugate e T).le_opNorm (e v)
    simpa only [angularConjugate_apply_coordinates, e.norm_map] using h

end Conjugation

end ContinuousFlexibility.Analysis
