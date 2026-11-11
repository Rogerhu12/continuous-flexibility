import ContinuousFlexibility.Radial.PositiveBufferFullInverse
import ContinuousFlexibility.Radial.PositiveBufferSurgery
import ContinuousFlexibility.Radial.PositiveBufferMatrixBounds

/-!
# Actual normalized Green columns and their cut matrix

These definitions retain the energy domain, its true continuous traces, and
the physical L² × ℝ pairing throughout the finite-dimensional subtraction.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real Matrix
open ContinuousFlexibility.Statements
open scoped Topology InnerProductSpace

def positiveBufferBoundaryPairing : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ i, x i * y i)
    (by intro x y z; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (by intro a x y; simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum])
    (by intro x y z; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (by
      intro a x y
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring)

@[simp] theorem positiveBufferBoundaryPairing_apply (x y : Fin 2 → ℝ) :
    positiveBufferBoundaryPairing x y = ∑ i, x i * y i :=
  LinearMap.mk₂_apply ℝ _ x y

def positiveBufferColumnLinear {W : Type*} [AddCommGroup W] [Module ℝ W]
    (g : Fin 2 → W) : (Fin 2 → ℝ) →ₗ[ℝ] W where
  toFun z := ∑ i, z i • g i
  map_add' := by
    intro z w
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro a z
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

@[simp] theorem positiveBufferColumnLinear_apply {W : Type*} [AddCommGroup W] [Module ℝ W]
    (g : Fin 2 → W) (z : Fin 2 → ℝ) :
    positiveBufferColumnLinear g z = ∑ i, z i • g i := rfl

def positiveBufferNormalizedTrace (V : ℝ → ℝ) (bordered : Bool)
    (c A : Fin 2 → ℝ) :
    PositiveBufferBorderedEnergy V bordered →ₗ[ℝ] (Fin 2 → ℝ) :=
  LinearMap.pi (fun i => sqrt (A i) •
    ((positiveBufferTraceAt V (c i)).toLinearMap.comp
      (positiveBufferBorderedField V bordered).toLinearMap))

@[simp] theorem positiveBufferNormalizedTrace_apply (V : ℝ → ℝ) (bordered : Bool)
    (c A : Fin 2 → ℝ) (U : PositiveBufferBorderedEnergy V bordered) (i : Fin 2) :
    positiveBufferNormalizedTrace V bordered c A U i =
      sqrt (A i) * positiveBufferTraceAt V (c i) U.val.1 := by
  simp only [positiveBufferNormalizedTrace, LinearMap.pi_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, ContinuousLinearMap.coe_coe, positiveBufferBorderedField_apply,
    smul_eq_mul]

def positiveBufferCutMatrix {V : ℝ → ℝ} {bordered : Bool}
    (c A : Fin 2 → ℝ) (g : Fin 2 → PositiveBufferBorderedEnergy V bordered) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => positiveBufferNormalizedTrace V bordered c A (g j) i

theorem positiveBuffer_trace_columns {V : ℝ → ℝ} {bordered : Bool}
    (c A : Fin 2 → ℝ) (g : Fin 2 → PositiveBufferBorderedEnergy V bordered)
    (z : Fin 2 → ℝ) :
    positiveBufferNormalizedTrace V bordered c A (positiveBufferColumnLinear g z) =
      positiveBufferCutMatrix c A g *ᵥ z := by
  ext i
  simp only [positiveBufferColumnLinear_apply, map_sum, map_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, positiveBufferCutMatrix]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

def positiveBufferCutEquiv (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : IsUnit M.det) :
    (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toLinearMap := M.mulVecLin
  invFun := fun z => M⁻¹ *ᵥ z
  left_inv := by
    intro z
    change M⁻¹ *ᵥ (M *ᵥ z) = z
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM, Matrix.one_mulVec]
  right_inv := by
    intro z
    change M *ᵥ (M⁻¹ *ᵥ z) = z
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]

@[simp] theorem positiveBufferCutEquiv_apply (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : IsUnit M.det) (z : Fin 2 → ℝ) :
    positiveBufferCutEquiv M hM z = M *ᵥ z := rfl

@[simp] theorem positiveBufferCutEquiv_symm_apply (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : IsUnit M.det) (z : Fin 2 → ℝ) :
    (positiveBufferCutEquiv M hM).symm z = M⁻¹ *ᵥ z := rfl

theorem positiveBuffer_green_columns_form {V : ℝ → ℝ} (hV : Continuous V)
    (border : RadialL2) (bordered : Bool) (c A : Fin 2 → ℝ)
    (g : Fin 2 → PositiveBufferBorderedEnergy V bordered)
    (hg : ∀ i W, positiveBufferBorderedForm V hV border bordered (g i) W =
      positiveBufferNormalizedTrace V bordered c A W i)
    (z : Fin 2 → ℝ) (W : PositiveBufferBorderedEnergy V bordered) :
    positiveBufferBorderedForm V hV border bordered (positiveBufferColumnLinear g z) W =
      positiveBufferBoundaryPairing z (positiveBufferNormalizedTrace V bordered c A W) := by
  change positiveBufferBorderedFormLinear V hV border bordered
    (positiveBufferColumnLinear g z) W = _
  rw [positiveBufferColumnLinear_apply, map_sum, LinearMap.sum_apply,
    positiveBufferBoundaryPairing_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul,
    positiveBufferBorderedFormLinear_apply, hg]

theorem positiveBuffer_green_inverse_trace {V : ℝ → ℝ}
    (hreal : ActualClosedFormRealization V) (hV : Continuous V)
    (border : RadialL2) (bordered : Bool)
    (H : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ))
    (hH : ∀ F, (bordered = false → F.2 = 0) →
      BorderedFullGraph V border bordered (H F) F)
    (c A : Fin 2 → ℝ) (g : Fin 2 → PositiveBufferBorderedEnergy V bordered)
    (hg : ∀ i W, positiveBufferBorderedForm V hV border bordered (g i) W =
      positiveBufferNormalizedTrace V bordered c A W i)
    (F : RadialL2 × ℝ) (i : Fin 2) :
    positiveBufferNormalizedTrace V bordered c A
        (positiveBufferLiftedInverse hreal border bordered H hH F) i =
      positiveBufferStatePairing (positiveBufferBorderedState V bordered (g i)) F := by
  rw [← hg, positiveBufferBorderedForm_symm, positiveBufferLiftedInverse_form,
    positiveBufferStatePairing_symm]

end ContinuousFlexibility.Radial
