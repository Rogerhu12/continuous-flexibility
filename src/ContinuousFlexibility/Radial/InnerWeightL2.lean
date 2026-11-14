module

public import ContinuousFlexibility.Radial.InnerWeightInterpolation
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Actual inner weights on the physical L² space

Multiplication uses mathlib's continuous Hölder map from L∞ × L² to L².
A bounded measurable real weight is self-adjoint, and a positive weight
with bounded reciprocal gives a continuous linear equivalence whose
inverse is multiplication by that same reciprocal. The measure is
arbitrary, so these operators apply directly to the physical radial
measure and its restrictions.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- The existing Hölder multiplication map, with the exponents ∞, 2, 2. -/
def innerLpMultiplier (w : Lp ℝ ∞ μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL μ ∞ 2 2 w

theorem innerLpMultiplier_ae (w : Lp ℝ ∞ μ) (f : Lp ℝ 2 μ) :
    innerLpMultiplier μ w f =ᵐ[μ] fun x => w x * f x := by
  simpa only [innerLpMultiplier, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.mul_apply'] using
    (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) w f

theorem innerLpMultiplier_inner (w : Lp ℝ ∞ μ) (f g : Lp ℝ 2 μ) :
    ⟪innerLpMultiplier μ w f, g⟫_ℝ = ⟪f, innerLpMultiplier μ w g⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [innerLpMultiplier_ae μ w f, innerLpMultiplier_ae μ w g] with x hf hg
  rw [hf, hg]
  simpa only [smul_eq_mul] using
    (real_inner_smul_left (f x) (g x) (w x)).trans
      (real_inner_smul_right (f x) (g x) (w x)).symm

theorem innerLpMultiplier_adjoint (w : Lp ℝ ∞ μ) :
    (innerLpMultiplier μ w).adjoint = innerLpMultiplier μ w :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr (innerLpMultiplier_inner μ w)).symm

/-- A pointwise bounded measurable weight, as an element of L∞. -/
def innerBoundedWeightValue (W : α → ℝ) (hW : Measurable W) (C : ℝ)
    (hbound : ∀ x, |W x| ≤ C) : Lp ℝ ∞ μ :=
  (memLp_top_of_bound (μ := μ) hW.aestronglyMeasurable C
    (.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbound x)).toLp W

theorem innerBoundedWeightValue_ae (W : α → ℝ) (hW : Measurable W) (C : ℝ)
    (hbound : ∀ x, |W x| ≤ C) : innerBoundedWeightValue μ W hW C hbound =ᵐ[μ] W := by
  exact MemLp.coeFn_toLp _

/-- Multiplication by the actual real-valued weight, on the same L² space. -/
def innerWeightMultiplier (W : α → ℝ) (hW : Measurable W) (C : ℝ)
    (hbound : ∀ x, |W x| ≤ C) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  innerLpMultiplier μ (innerBoundedWeightValue μ W hW C hbound)

theorem innerWeightMultiplier_ae (W : α → ℝ) (hW : Measurable W) (C : ℝ)
    (hbound : ∀ x, |W x| ≤ C) (f : Lp ℝ 2 μ) :
    innerWeightMultiplier μ W hW C hbound f =ᵐ[μ] fun x => W x * f x := by
  filter_upwards [innerLpMultiplier_ae μ (innerBoundedWeightValue μ W hW C hbound) f,
    innerBoundedWeightValue_ae μ W hW C hbound] with x hf hW'
  exact hf.trans (congrArg (fun z : ℝ => z * f x) hW')

theorem innerWeightMultiplier_norm_apply_le (W : α → ℝ) (hW : Measurable W) (C : ℝ)
    (hbound : ∀ x, |W x| ≤ C) (f : Lp ℝ 2 μ) :
    ‖innerWeightMultiplier μ W hW C hbound f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [innerWeightMultiplier_ae μ W hW C hbound f] with x hx
  rw [hx, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hbound x) (abs_nonneg _)

theorem norm_innerWeightMultiplier_le (W : α → ℝ) (hW : Measurable W) (C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ x, |W x| ≤ C) :
    ‖innerWeightMultiplier μ W hW C hbound‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC
    (innerWeightMultiplier_norm_apply_le μ W hW C hbound)

theorem innerWeightMultiplier_adjoint (W : α → ℝ) (hW : Measurable W) (C : ℝ)
    (hbound : ∀ x, |W x| ≤ C) :
    (innerWeightMultiplier μ W hW C hbound).adjoint =
      innerWeightMultiplier μ W hW C hbound :=
  innerLpMultiplier_adjoint μ _

theorem innerWeightMultiplier_selfAdjoint (W : α → ℝ) (hW : Measurable W) (C : ℝ)
    (hbound : ∀ x, |W x| ≤ C) : IsSelfAdjoint (innerWeightMultiplier μ W hW C hbound) :=
  ContinuousLinearMap.isSelfAdjoint_iff'.mpr (innerWeightMultiplier_adjoint μ W hW C hbound)

/-- One composition identity supplies both inverse laws, with the same
actual functions and without identifying chosen Lp representatives. -/
theorem innerWeightMultiplier_comp_apply (W V : α → ℝ)
    (hW : Measurable W) (hV : Measurable V) (C D : ℝ)
    (hWC : ∀ x, |W x| ≤ C) (hVD : ∀ x, |V x| ≤ D)
    (hmul : ∀ x, V x * W x = 1) (f : Lp ℝ 2 μ) :
    innerWeightMultiplier μ V hV D hVD (innerWeightMultiplier μ W hW C hWC f) = f := by
  apply Lp.ext
  filter_upwards [innerWeightMultiplier_ae μ V hV D hVD
    (innerWeightMultiplier μ W hW C hWC f),
    innerWeightMultiplier_ae μ W hW C hWC f] with x hV' hW'
  rw [hV', hW', ← mul_assoc, hmul, one_mul]

section Equivalence

variable (W : α → ℝ) (hW : Measurable W) (hpos : ∀ x, 0 < W x)
  (C D : ℝ) (hWC : ∀ x, |W x| ≤ C) (hWD : ∀ x, |(W x)⁻¹| ≤ D)

/-- The inverse of multiplication by a positive bounded weight is
multiplication by its actual reciprocal. -/
def innerWeightEquiv : Lp ℝ 2 μ ≃L[ℝ] Lp ℝ 2 μ :=
  ContinuousLinearEquiv.equivOfInverse
    (innerWeightMultiplier μ W hW C hWC)
    (innerWeightMultiplier μ (fun x => (W x)⁻¹) hW.inv D hWD)
    (innerWeightMultiplier_comp_apply μ W (fun x => (W x)⁻¹) hW hW.inv C D hWC hWD
      (fun x => inv_mul_cancel₀ (hpos x).ne'))
    (innerWeightMultiplier_comp_apply μ (fun x => (W x)⁻¹) W hW.inv hW D C hWD hWC
      (fun x => mul_inv_cancel₀ (hpos x).ne'))

theorem innerWeightEquiv_apply (f : Lp ℝ 2 μ) :
    innerWeightEquiv μ W hW hpos C D hWC hWD f = innerWeightMultiplier μ W hW C hWC f := by
  unfold innerWeightEquiv
  exact ContinuousLinearEquiv.equivOfInverse_apply _ _ _ _ _

theorem innerWeightEquiv_symm_apply (f : Lp ℝ 2 μ) :
    (innerWeightEquiv μ W hW hpos C D hWC hWD).symm f =
      innerWeightMultiplier μ (fun x => (W x)⁻¹) hW.inv D hWD f := by
  unfold innerWeightEquiv
  rw [ContinuousLinearEquiv.symm_equivOfInverse, ContinuousLinearEquiv.equivOfInverse_apply]

theorem innerWeightEquiv_toContinuousLinearMap :
    (innerWeightEquiv μ W hW hpos C D hWC hWD : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) =
      innerWeightMultiplier μ W hW C hWC := by
  unfold innerWeightEquiv
  exact ContinuousLinearEquiv.toContinuousLinearMap_equivOfInverse _ _ _ _

theorem innerWeightEquiv_symm_toContinuousLinearMap :
    ((innerWeightEquiv μ W hW hpos C D hWC hWD).symm : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) =
      innerWeightMultiplier μ (fun x => (W x)⁻¹) hW.inv D hWD := by
  unfold innerWeightEquiv
  rw [ContinuousLinearEquiv.symm_equivOfInverse,
    ContinuousLinearEquiv.toContinuousLinearMap_equivOfInverse]

theorem innerWeightEquiv_ae (f : Lp ℝ 2 μ) :
    innerWeightEquiv μ W hW hpos C D hWC hWD f =ᵐ[μ] fun x => W x * f x := by
  rw [innerWeightEquiv_apply]
  exact innerWeightMultiplier_ae μ W hW C hWC f

theorem innerWeightEquiv_symm_ae (f : Lp ℝ 2 μ) :
    (innerWeightEquiv μ W hW hpos C D hWC hWD).symm f =ᵐ[μ] fun x => (W x)⁻¹ * f x := by
  rw [innerWeightEquiv_symm_apply]
  exact innerWeightMultiplier_ae μ (fun x => (W x)⁻¹) hW.inv D hWD f

theorem innerWeightEquiv_adjoint :
    (innerWeightEquiv μ W hW hpos C D hWC hWD : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ).adjoint =
      (innerWeightEquiv μ W hW hpos C D hWC hWD : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) := by
  rw [innerWeightEquiv_toContinuousLinearMap]
  exact innerWeightMultiplier_adjoint μ W hW C hWC

theorem innerWeightEquiv_selfAdjoint :
    IsSelfAdjoint (innerWeightEquiv μ W hW hpos C D hWC hWD : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :=
  ContinuousLinearMap.isSelfAdjoint_iff'.mpr (innerWeightEquiv_adjoint μ W hW hpos C D hWC hWD)

theorem norm_innerWeightEquiv_le (hC : 0 ≤ C) :
    ‖(innerWeightEquiv μ W hW hpos C D hWC hWD : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)‖ ≤ C := by
  rw [innerWeightEquiv_toContinuousLinearMap]
  exact norm_innerWeightMultiplier_le μ W hW C hC hWC

theorem norm_innerWeightEquiv_symm_le (hD : 0 ≤ D) :
    ‖((innerWeightEquiv μ W hW hpos C D hWC hWD).symm : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)‖ ≤ D := by
  rw [innerWeightEquiv_symm_toContinuousLinearMap]
  exact norm_innerWeightMultiplier_le μ (fun x => (W x)⁻¹) hW.inv D hD hWD

end Equivalence

section FiniteInterpolation

variable {ι : Type*} [Fintype ι]

/-- Every finite family of actual interpolated cell weights admits one
positive bound for both signs. No finite-measure hypothesis is involved. -/
theorem innerInterpolatedWeight_finite_bounds (l r u v : ι → ℝ)
    (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i) :
    ∃ C : ℝ, 0 < C ∧ ∀ i x,
      |innerInterpolatedWeight (l i) (r i) (u i) (v i) x| ≤ C ∧
      |(innerInterpolatedWeight (l i) (r i) (u i) (v i) x)⁻¹| ≤ C := by
  classical
  let B : ι → ℝ := fun i => Real.exp (max |Real.log (u i)| |Real.log (v i)|)
  have hB : ∀ i, 0 ≤ B i := fun i => (Real.exp_pos _).le
  refine ⟨1 + ∑ i, B i,
    add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun i _ => hB i), ?_⟩
  intro i x
  have hsum : B i ≤ 1 + ∑ k, B k :=
    (Finset.single_le_sum (fun k _ => hB k) (Finset.mem_univ i)).trans (by linarith)
  have h := innerInterpolatedWeight_bounds (l i) (r i) (hu i) (hv i) x
  have hpos := innerInterpolatedWeight_pos (l i) (r i) (u i) (v i) x
  exact ⟨(abs_of_pos hpos).trans_le (h.1.trans hsum),
    (abs_of_pos (inv_pos.mpr hpos)).trans_le (h.2.trans hsum)⟩

end FiniteInterpolation

end ContinuousFlexibility.Radial
