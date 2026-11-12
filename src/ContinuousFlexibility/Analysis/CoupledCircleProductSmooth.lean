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
set_option backward.isDefEq.respectTransparency.types false

private theorem coupled_product_tail_pair {E : Type*} (u v : E) :
    Fin.tail (![u, v] : Fin 2 → E) = ![v] := by
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst i
  rfl

private theorem coupled_product_cons_pair {E : Type*} (u v : E) :
    (Fin.cons u ![v] : Fin 2 → E) = ![u, v] := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem coupled_product_seminorm_zero
    {E : Type*} [AddCommGroup E] [Module ℝ E] (p : Seminorm ℝ E) :
    p (0 : E) = 0 := map_zero p

private theorem coupled_product_majorant_le
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p q : Seminorm ℝ E) (hpq : ∀ x, p x ≤ q x) (u v : E) :
    (1 + q (0 : E)) * (∏ i : Fin 2, p ((![u, v] : Fin 2 → E) i)) +
      (∑ i : Fin 2, q ((![u, v] : Fin 2 → E) i) *
        ∏ j ∈ Finset.univ.erase i, p ((![u, v] : Fin 2 → E) j)) ≤
      2 * (q u * p v + p u * q v) := by
  have h0 : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have h1 : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  simp only [coupled_product_seminorm_zero q, add_zero, one_mul,
    Fin.prod_univ_two, Fin.sum_univ_two, h0, h1, Finset.prod_singleton,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have hlow := mul_le_mul_of_nonneg_right (hpq u) (apply_nonneg p v)
  have hnonneg := mul_nonneg (apply_nonneg p u) (apply_nonneg q v)
  nlinarith only [hlow, hnonneg]

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
  (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  (hγ : 0 < γ) (hM : IsCircleModel T γ M) (hI : HasInterpolation M.grading)

def coupledCircleProduct (u v : M.Space) : M.Space :=
  bilinearJetValue (coupledCircleKernelContinuousMultilinear hD hT hγ hM hI 0 1 0) u v

private theorem coupledCircleProduct_eq_kernel (u v : M.Space) :
    coupledCircleProduct hD hT hγ hM hI u v =
      coupledCircleKernel hD hT hγ hM hI 0 1 0 u ![v] := by
  calc
    coupledCircleProduct hD hT hγ hM hI u v =
        coupledCircleKernel hD hT hγ hM hI 0 1 0 u
          (Fin.tail (![u, v] : Fin 2 → M.Space)) :=
      coupledCircleKernelContinuousMultilinear_apply hD hT hγ hM hI 0 1 0 ![u, v]
    _ = _ := congrArg
      (fun w : Fin 1 → M.Space => coupledCircleKernel hD hT hγ hM hI 0 1 0 u w)
      (coupled_product_tail_pair u v)

theorem coupledCircleProduct_decode (u v : M.Space) (m : ℕ) (θ : ℝ) :
    M.decode (coupledCircleProduct hD hT hγ hM hI u v) m θ =
      M.decode u m θ * M.decode v m θ := by
  have hzero : M.decode (0 : M.Space) m θ = 0 :=
    congrArg (fun f : ℕ → ℝ → ℝ => f m θ) M.decode.map_zero
  simp only [coupledCircleProduct_eq_kernel,
    coupledCircleKernel_decode_apply, iteratedDeriv_zero, hzero, add_zero,
    Fin.prod_univ_one, Matrix.cons_val_zero]

omit hD hT hγ hM hI in
private theorem coupled_circle_product_majorant_le
    (base high : ℕ) (hbh : base ≤ high) (u v : M.Space) :
    coupledCircleKernelMajorant M base high 0 ![u, v] ≤
      2 * (M.grading high u * M.grading base v +
        M.grading base u * M.grading high v) := by
  exact coupled_product_majorant_le (M.grading base) (M.grading high)
    (fun x => gradedSeminorm_monotone (fun n => M.level n) M.bond hbh x) u v

theorem coupledCircleProduct_oneHigh_bound :
    ∃ base loss : ℕ, ∀ s, ∃ A : ℝ, 0 ≤ A ∧ ∀ u v : M.Space,
      M.grading s (coupledCircleProduct hD hT hγ hM hI u v) ≤
        A * (M.grading (s + loss) u * M.grading base v +
          M.grading base u * M.grading (s + loss) v) := by
  have hexists := coupled_circle_kernel_grading_bounds hD hT hγ hM hI
  let base : ℕ := hexists.choose
  let loss : ℕ := hexists.choose_spec.choose
  have hb := hexists.choose_spec.choose_spec
  refine ⟨base, base + loss, fun s => ?_⟩
  have hdata := hb 0 1 s 1 le_rfl
  let A : ℝ := hdata.choose
  have hA : 0 ≤ A := hdata.choose_spec.1
  have hbound : ∀ ψ : M.Space, M.grading base ψ ≤ (1 : ℝ) →
      ∀ (v : M.Space) (w : Fin 1 → M.Space),
        M.grading s (coupledCircleKernel hD hT hγ hM hI 0 1 ψ v w) ≤
          A * coupledCircleKernelMajorant M base (0 + s + loss) ψ (Fin.cons v w) :=
    hdata.choose_spec.2
  refine ⟨2 * A, mul_nonneg (by norm_num) hA, fun u v => ?_⟩
  have hzero : M.grading base (0 : M.Space) ≤ (1 : ℝ) :=
    (coupled_product_seminorm_zero (M.grading base)).trans_le zero_le_one
  have hraw := hbound (0 : M.Space) hzero u ![v]
  have hproduct : M.grading s (coupledCircleProduct hD hT hγ hM hI u v) ≤
      A * coupledCircleKernelMajorant M base (s + loss) 0 ![u, v] := by
    simpa only [coupledCircleProduct_eq_kernel, coupled_product_cons_pair,
      Nat.zero_add] using hraw
  have hmajor := (coupledCircleKernelMajorant_mono_high (M := M)
    (show s + loss ≤ s + (base + loss) by omega) base 0 ![u, v]).trans
      (coupled_circle_product_majorant_le base (s + (base + loss)) (by omega) u v)
  exact hproduct.trans ((mul_le_mul_of_nonneg_left hmajor hA).trans_eq (by ring))

/-- Joint smooth tameness of the product on the original circle space. -/
theorem coupled_circleProduct_smoothTameOn :
    SmoothTameOn (pairGrading M.grading M.grading) M.grading univ
      (fun z : M.Space × M.Space => coupledCircleProduct hD hT hγ hM hI z.1 z.2) := by
  have hexists := coupledCircleProduct_oneHigh_bound hD hT hγ hM hI
  let base : ℕ := hexists.choose
  let loss : ℕ := hexists.choose_spec.choose
  have hb := hexists.choose_spec.choose_spec
  exact smoothTameOn_bilinearMultilinear (E := M.Space) (F := M.Space)
    (p := M.grading) (q := M.grading) (base := base) (loss := loss)
    (coupledCircleKernelContinuousMultilinear hD hT hγ hM hI 0 1 0)
    (fun s _ => hb s)

end ContinuousFlexibility.Statements
