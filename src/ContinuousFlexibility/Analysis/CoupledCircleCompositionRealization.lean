import ContinuousFlexibility.Analysis.CoupledCircleCompositionKernels

/-!
# Realization of circle composition kernels

Each kernel is realized through the original circle model. The decoder
identity and its injectivity determine the element uniquely, and the
weighted estimates pass to every projective seminorm.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
  (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  (hγ : 0 < γ) (hM : IsCircleModel T γ M) (hI : HasInterpolation M.grading)

def coupledCircleKernel (r k : ℕ) (ψ v : M.Space) (w : Fin k → M.Space) : M.Space :=
  (hM.2.2.2.2.1 (coupledCircleKernelField M r k ψ v w)
    (coupledCircleKernelField_mem hD hT hγ hM hI r k ψ v w)).choose

theorem coupledCircleKernel_decode (r k : ℕ) (ψ v : M.Space) (w : Fin k → M.Space) :
    M.decode (coupledCircleKernel hD hT hγ hM hI r k ψ v w) =
      coupledCircleKernelField M r k ψ v w :=
  (hM.2.2.2.2.1 (coupledCircleKernelField M r k ψ v w)
    (coupledCircleKernelField_mem hD hT hγ hM hI r k ψ v w)).choose_spec

theorem coupledCircleKernel_decode_apply (r k : ℕ) (ψ v : M.Space)
    (w : Fin k → M.Space) (m : ℕ) (θ : ℝ) :
    M.decode (coupledCircleKernel hD hT hγ hM hI r k ψ v w) m θ =
      iteratedDeriv r (M.decode v m) (θ + M.decode ψ m θ) * ∏ i, M.decode (w i) m θ :=
  congrFun (congrFun (coupledCircleKernel_decode hD hT hγ hM hI r k ψ v w) m) θ

omit hD hT hγ hM hI in
theorem coupledCircleKernelMajorant_mono_high {a b : ℕ} (hab : a ≤ b)
    (base : ℕ) (ψ : M.Space) {n : ℕ} (v : Fin n → M.Space) :
    coupledCircleKernelMajorant M base a ψ v ≤ coupledCircleKernelMajorant M base b ψ v := by
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right
      (add_le_add le_rfl (gradedSeminorm_monotone _ _ hab ψ))
      (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))
  · exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right
      (gradedSeminorm_monotone _ _ hab (v i))
      (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)))

/-- One high input seminorm controls the actual realized kernel, uniformly
on each fixed low-seminorm neighborhood of chart displacements. -/
theorem coupled_circle_kernel_grading_bounds :
    ∃ base loss : ℕ, ∀ (r k s : ℕ) (R : ℝ), 1 ≤ R →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : M.Space, M.grading base ψ ≤ R →
        ∀ (v : M.Space) (w : Fin k → M.Space),
          M.grading s (coupledCircleKernel hD hT hγ hM hI r k ψ v w) ≤
            C * coupledCircleKernelMajorant M base (r + s + loss) ψ (Fin.cons v w) := by
  classical
  have hexists := coupled_circle_kernel_norm_bounds hD hT hγ hM hI
  let base : ℕ := hexists.choose
  let loss : ℕ := hexists.choose_spec.choose
  have hb := hexists.choose_spec.choose_spec
  refine ⟨base, loss, fun r k s R hR => ?_⟩
  have hcoord (i : ℕ) := hb r k i R hR
  choose C hC hbound using hcoord
  let A : ℝ := ∑ i ∈ Finset.Iic s, C i
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => hC i)
  refine ⟨A, hA, fun ψ hψ v w => ?_⟩
  apply (gradedSeminorm_le_iff (fun n => M.level n) M.bond s _
    (mul_nonneg hA (coupledCircleKernelMajorant_nonneg M base (r + s + loss) ψ
      (Fin.cons v w)))).mpr
  intro i hi
  have hCi : C i ≤ A := Finset.single_le_sum (fun j _ => hC j) (Finset.mem_Iic.mpr hi)
  calc
    ‖(coupledCircleKernel hD hT hγ hM hI r k ψ v w).val i‖ =
        circleNorm T γ i (M.decode (coupledCircleKernel hD hT hγ hM hI r k ψ v w)) :=
      hM.2.2.2.2.2.2.2 _ _
    _ = circleNorm T γ i (coupledCircleKernelField M r k ψ v w) :=
      congrArg (circleNorm T γ i) (coupledCircleKernel_decode hD hT hγ hM hI r k ψ v w)
    _ ≤ C i * coupledCircleKernelMajorant M base (r + i + loss) ψ (Fin.cons v w) :=
      hbound i ψ hψ v w
    _ ≤ A * coupledCircleKernelMajorant M base (r + s + loss) ψ (Fin.cons v w) :=
      mul_le_mul hCi (coupledCircleKernelMajorant_mono_high (by omega) base ψ (Fin.cons v w))
        (coupledCircleKernelMajorant_nonneg M base (r + i + loss) ψ (Fin.cons v w)) hA

omit hD hT hγ hM hI in
theorem coupledCircleKernelMajorant_le_coarse {base high N n : ℕ}
    (hb : base ≤ N) (hh : high ≤ N) (ψ : M.Space) (v : Fin n → M.Space) :
    coupledCircleKernelMajorant M base high ψ v ≤
      ((n : ℝ) + 1) * (1 + M.grading N ψ) * ∏ i, M.grading N (v i) := by
  classical
  let P : ℝ := ∏ i, M.grading N (v i)
  have hP : 0 ≤ P := Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)
  have hv : (∏ i, M.grading base (v i)) ≤ P :=
    Finset.prod_le_prod₀ (fun _ _ => apply_nonneg _ _)
      (fun i _ => gradedSeminorm_monotone _ _ hb (v i))
  have hterm (i : Fin n) :
      M.grading high (v i) * (∏ j ∈ Finset.univ.erase i, M.grading base (v j)) ≤ P := by
    calc
      _ ≤ M.grading N (v i) * ∏ j ∈ Finset.univ.erase i, M.grading N (v j) :=
        mul_le_mul (gradedSeminorm_monotone _ _ hh (v i))
          (Finset.prod_le_prod₀ (fun _ _ => apply_nonneg _ _)
            (fun j _ => gradedSeminorm_monotone _ _ hb (v j)))
          (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)) (apply_nonneg _ _)
      _ = P := Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)
  have hsum : (∑ i, M.grading high (v i) *
      ∏ j ∈ Finset.univ.erase i, M.grading base (v j)) ≤ (n : ℝ) * P := by
    calc
      _ ≤ ∑ _i : Fin n, P := Finset.sum_le_sum (fun i _ => hterm i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hscalar (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
      (1 + a) * c + b * c ≤ (b + 1) * (1 + a) * c := by
    nlinarith only [mul_nonneg (mul_nonneg ha hb) hc]
  exact (add_le_add
    (mul_le_mul (add_le_add le_rfl (gradedSeminorm_monotone _ _ hh ψ)) hv
      (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))
      (add_nonneg zero_le_one (apply_nonneg _ _))) hsum).trans
        (hscalar _ _ _ (apply_nonneg _ _) (Nat.cast_nonneg _) hP)

theorem coupled_circle_kernel_coarse :
    ∃ base : ℕ, ∀ (r k s : ℕ) (R : ℝ), 1 ≤ R →
      ∃ N : ℕ, base ≤ N ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∀ ψ : M.Space, M.grading base ψ ≤ R →
          ∀ (v : M.Space) (w : Fin k → M.Space),
            M.grading s (coupledCircleKernel hD hT hγ hM hI r k ψ v w) ≤
              C * (1 + M.grading N ψ) *
                ∏ i : Fin (k + 1), M.grading N ((Fin.cons v w : Fin (k + 1) → M.Space) i) := by
  have hexists := coupled_circle_kernel_grading_bounds hD hT hγ hM hI
  let base : ℕ := hexists.choose
  let loss : ℕ := hexists.choose_spec.choose
  have hb := hexists.choose_spec.choose_spec
  refine ⟨base, fun r k s R hR => ?_⟩
  obtain ⟨C, hC, hc⟩ := hb r k s R hR
  refine ⟨max base (r + s + loss), le_max_left _ _, C * (((k + 1 : ℕ) : ℝ) + 1),
    mul_nonneg hC (by positivity), fun ψ hψ v w => ?_⟩
  exact (hc ψ hψ v w).trans
    ((mul_le_mul_of_nonneg_left
      (coupledCircleKernelMajorant_le_coarse (le_max_left _ _) (le_max_right _ _) ψ
        (Fin.cons v w)) hC).trans_eq (by simp only [Nat.cast_add, Nat.cast_one]; ac_rfl))

end ContinuousFlexibility.Statements
