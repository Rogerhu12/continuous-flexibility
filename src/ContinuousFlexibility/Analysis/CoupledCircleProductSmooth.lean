import ContinuousFlexibility.Analysis.CoupledCircleCompositionMultilinear
import ContinuousFlexibility.Scalar.WeightedSmoothTameAlgebra

/-!
# Actual circle multiplication from the composition kernels

The kernel with zero chart and one direction factor is pointwise
multiplication. Its existing one-high estimate gives the genuine bilinear
map a smooth tame tower without another weighted product construction.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
  (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  (hγ : 0 < γ) (hM : IsCircleModel T γ M) (hI : HasInterpolation M.grading)

def coupledCircleProduct (u v : M.Space) : M.Space :=
  bilinearJetValue (coupledCircleKernelContinuousMultilinear hD hT hγ hM hI 0 1 0) u v

theorem coupledCircleProduct_decode (u v : M.Space) (m : ℕ) (θ : ℝ) :
    M.decode (coupledCircleProduct hD hT hγ hM hI u v) m θ =
      M.decode u m θ * M.decode v m θ := by
  have htail : Fin.tail (![u, v] : Fin 2 → M.Space) = ![v] := Fin.tail_cons u ![v]
  simp only [coupledCircleProduct, bilinearJetValue,
    coupledCircleKernelContinuousMultilinear_apply, coupledCircleKernel_decode_apply,
    iteratedDeriv_zero, map_zero, Pi.zero_apply, add_zero,
    Fin.prod_univ_one, htail, Fin.cons_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one]

omit hD hT hγ hM hI in
private theorem coupled_circle_product_majorant_le
    (base high : ℕ) (hbh : base ≤ high) (u v : M.Space) :
    coupledCircleKernelMajorant M base high 0 ![u, v] ≤
      2 * (M.grading high u * M.grading base v +
        M.grading base u * M.grading high v) := by
  have h0 : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have h1 : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  simp only [coupledCircleKernelMajorant, map_zero, add_zero, one_mul,
    Fin.prod_univ_two, Fin.sum_univ_two, h0, h1, Finset.prod_singleton,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have hlow := mul_le_mul_of_nonneg_right
    (gradedSeminorm_monotone (fun n => M.level n) M.bond hbh u)
    (apply_nonneg (M.grading base) v)
  have hnonneg := mul_nonneg (apply_nonneg (M.grading base) u)
    (apply_nonneg (M.grading high) v)
  nlinarith only [hlow, hnonneg]

theorem coupledCircleProduct_oneHigh_bound :
    ∃ base loss : ℕ, ∀ s, ∃ A : ℝ, 0 ≤ A ∧ ∀ u v : M.Space,
      M.grading s (coupledCircleProduct hD hT hγ hM hI u v) ≤
        A * (M.grading (s + loss) u * M.grading base v +
          M.grading base u * M.grading (s + loss) v) := by
  obtain ⟨base, loss, hb⟩ := coupled_circle_kernel_grading_bounds hD hT hγ hM hI
  refine ⟨base, base + loss, fun s => ?_⟩
  obtain ⟨A, hA, hbound⟩ := hb 0 1 s 1 le_rfl
  refine ⟨2 * A, mul_nonneg (by norm_num) hA, fun u v => ?_⟩
  have hraw := hbound 0 (by simp) (![u, v] 0) (Fin.tail ![u, v])
  have hproduct : M.grading s (coupledCircleProduct hD hT hγ hM hI u v) ≤
      A * coupledCircleKernelMajorant M base (s + loss) 0 ![u, v] := by
    simpa only [coupledCircleProduct, bilinearJetValue,
      coupledCircleKernelContinuousMultilinear_apply, coupled_fin_cons_head_tail,
      Nat.zero_add] using hraw
  have hmajor := (coupledCircleKernelMajorant_mono_high (M := M)
    (show s + loss ≤ s + (base + loss) by omega) base 0 ![u, v]).trans
      (coupled_circle_product_majorant_le base (s + (base + loss)) (by omega) u v)
  exact hproduct.trans ((mul_le_mul_of_nonneg_left hmajor hA).trans_eq (by ring))

/-- Joint smooth tameness of the product on the original circle space. -/
theorem coupled_circleProduct_smoothTameOn :
    SmoothTameOn (pairGrading M.grading M.grading) M.grading univ
      (fun z : M.Space × M.Space => coupledCircleProduct hD hT hγ hM hI z.1 z.2) := by
  obtain ⟨base, loss, hb⟩ := coupledCircleProduct_oneHigh_bound hD hT hγ hM hI
  exact smoothTameOn_bilinearMultilinear
    (coupledCircleKernelContinuousMultilinear hD hT hγ hM hI 0 1 0)
    (fun s _ => hb s)

end ContinuousFlexibility.Statements
