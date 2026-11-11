import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic.Abel

/-!
# Exact Dirichlet subtraction in a symmetric energy space

This is the algebraic part of the positive-buffer Green formula.  Actual
Green columns represent the cut traces for the energy form.  Subtracting
their cut values produces the zero-trace inverse, and its uniqueness uses
the given full inverse, without a positivity assumption on the interior
potential or the bordered form.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open scoped RealInnerProductSpace

variable {W S F : Type*}
  [AddCommGroup W] [Module ℝ W]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The zero-trace correction, before restricting a field to the retained
interval. The inverse cut matrix is written as a linear equivalence. -/
def positiveBufferDirichletCorrection
    (H : S →ₗ[ℝ] W) (trace : W →ₗ[ℝ] F) (columns : F →ₗ[ℝ] W)
    (Γ : F ≃ₗ[ℝ] F) : S →ₗ[ℝ] W :=
  H - columns.comp (Γ.symm.toLinearMap.comp (trace.comp H))

theorem positiveBufferDirichletCorrection_apply
    (H : S →ₗ[ℝ] W) (trace : W →ₗ[ℝ] F) (columns : F →ₗ[ℝ] W)
    (Γ : F ≃ₗ[ℝ] F) (f : S) :
    positiveBufferDirichletCorrection H trace columns Γ f =
      H f - columns (Γ.symm (trace (H f))) := rfl

/-- The cut-value subtraction is exact. -/
theorem positiveBufferDirichletCorrection_trace
    (H : S →ₗ[ℝ] W) (trace : W →ₗ[ℝ] F) (columns : F →ₗ[ℝ] W)
    (Γ : F ≃ₗ[ℝ] F) (hΓ : ∀ z, trace (columns z) = Γ z) (f : S) :
    trace (positiveBufferDirichletCorrection H trace columns Γ f) = 0 := by
  rw [positiveBufferDirichletCorrection_apply, map_sub, hΓ,
    LinearEquiv.apply_symm_apply, sub_self]

/-- On zero-trace tests the correction changes no source equation. -/
theorem positiveBufferDirichletCorrection_form
    (a : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (J : W →ₗ[ℝ] S)
    (H : S →ₗ[ℝ] W) (trace : W →ₗ[ℝ] F) (columns : F →ₗ[ℝ] W)
    (Γ : F ≃ₗ[ℝ] F)
    (hH : ∀ f v, a (H f) v = ⟪f, J v⟫_ℝ)
    (hcolumns : ∀ z v, a (columns z) v = ⟪z, trace v⟫_ℝ)
    (f : S) (v : W) (hv : trace v = 0) :
    a (positiveBufferDirichletCorrection H trace columns Γ f) v = ⟪f, J v⟫_ℝ := by
  rw [positiveBufferDirichletCorrection_apply, map_sub, LinearMap.sub_apply,
    hH, hcolumns, hv, inner_zero_right, sub_zero]

/-- Green reciprocity identifies the cut values of a full-model inverse
with pairings against its exact Green columns. -/
theorem positiveBuffer_cut_reciprocity
    (a : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (J : W →ₗ[ℝ] S)
    (H : S →ₗ[ℝ] W) (trace : W →ₗ[ℝ] F) (columns : F →ₗ[ℝ] W)
    (hsymm : ∀ u v, a u v = a v u)
    (hH : ∀ f v, a (H f) v = ⟪f, J v⟫_ℝ)
    (hcolumns : ∀ z v, a (columns z) v = ⟪z, trace v⟫_ℝ)
    (f : S) (z : F) :
    ⟪z, trace (H f)⟫_ℝ = ⟪f, J (columns z)⟫_ℝ := by
  rw [← hcolumns, hsymm, hH]

/-- The actual cut-value matrix is symmetric because the full form is
symmetric, including its scalar border. -/
theorem positiveBuffer_cut_matrix_symmetric
    (a : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (trace : W →ₗ[ℝ] F)
    (columns : F →ₗ[ℝ] W) (hsymm : ∀ u v, a u v = a v u)
    (hcolumns : ∀ z v, a (columns z) v = ⟪z, trace v⟫_ℝ)
    (x y : F) :
    ⟪x, trace (columns y)⟫_ℝ = ⟪y, trace (columns x)⟫_ℝ := by
  rw [← hcolumns, hsymm, hcolumns]

/-- There is no hidden zero-trace kernel.  This argument needs neither
a coercive retained form nor an a priori Dirichlet inverse. -/
theorem positiveBuffer_zero_trace_kernel
    (a : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (J : W →ₗ[ℝ] S)
    (hJ : Function.Injective J)
    (H : S →ₗ[ℝ] W) (trace : W →ₗ[ℝ] F) (columns : F →ₗ[ℝ] W)
    (Γ : F ≃ₗ[ℝ] F) (hΓ : ∀ z, trace (columns z) = Γ z)
    (hsymm : ∀ u v, a u v = a v u)
    (hH : ∀ f v, a (H f) v = ⟪f, J v⟫_ℝ)
    (hcolumns : ∀ z v, a (columns z) v = ⟪z, trace v⟫_ℝ)
    (u : W) (hu : trace u = 0)
    (hkernel : ∀ v, trace v = 0 → a u v = 0) : u = 0 := by
  let v := positiveBufferDirichletCorrection H trace columns Γ (J u)
  have hv : trace v = 0 := positiveBufferDirichletCorrection_trace H trace columns Γ hΓ _
  have heq : a v u = ⟪J u, J u⟫_ℝ :=
    positiveBufferDirichletCorrection_form a J H trace columns Γ hH hcolumns _ u hu
  have hzero : ⟪J u, J u⟫_ℝ = 0 := heq.symm.trans ((hsymm v u).trans (hkernel v hv))
  apply hJ
  rw [map_zero]
  exact inner_self_eq_zero.mp hzero

/-- The corrected field is the unique zero-trace solution. -/
theorem positiveBufferDirichletCorrection_unique
    (a : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (J : W →ₗ[ℝ] S)
    (hJ : Function.Injective J)
    (H : S →ₗ[ℝ] W) (trace : W →ₗ[ℝ] F) (columns : F →ₗ[ℝ] W)
    (Γ : F ≃ₗ[ℝ] F) (hΓ : ∀ z, trace (columns z) = Γ z)
    (hsymm : ∀ u v, a u v = a v u)
    (hH : ∀ f v, a (H f) v = ⟪f, J v⟫_ℝ)
    (hcolumns : ∀ z v, a (columns z) v = ⟪z, trace v⟫_ℝ)
    (f : S) (u : W) (hu : trace u = 0)
    (hsource : ∀ v, trace v = 0 → a u v = ⟪f, J v⟫_ℝ) :
    u = positiveBufferDirichletCorrection H trace columns Γ f := by
  apply sub_eq_zero.mp
  apply positiveBuffer_zero_trace_kernel a J hJ H trace columns Γ hΓ hsymm hH hcolumns
  · rw [map_sub, hu, positiveBufferDirichletCorrection_trace H trace columns Γ hΓ,
      sub_self]
  · intro v hv
    rw [map_sub, LinearMap.sub_apply, hsource v hv,
      positiveBufferDirichletCorrection_form a J H trace columns Γ hH hcolumns f v hv,
      sub_self]

end ContinuousFlexibility.Radial
