import ContinuousFlexibility.Analysis.CoupledCircleCompositionParameter
import ContinuousFlexibility.Analysis.SpacesLpCurveDerivative

/-!
# Summable majorants for affine chart curves

On every compact real parameter interval, each weighted jet has a
common constant times the summable inverse material weight. These bounds
apply to the actual angular L² classes used in each Hilbert row.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}

theorem coupled_circle_affine_grading_le (n : ℕ) (ψ u : M.Space)
    {R t : ℝ} (ht : |t| ≤ R) :
    M.grading n (ψ + t • u) ≤ M.grading n ψ + R * M.grading n u := by
  calc
    _ ≤ M.grading n ψ + M.grading n (t • u) := map_add_le_add _ _ _
    _ = M.grading n ψ + |t| * M.grading n u := by
      rw [map_smul_eq_mul, Real.norm_eq_abs]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right ht (apply_nonneg _ _))

theorem coupled_circle_kernel_majorant_affine_bound (base high : ℕ)
    (ψ u : M.Space) {n : ℕ} (v : Fin n → M.Space) {R : ℝ} (hR : 0 ≤ R) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, |t| ≤ R →
      coupledCircleKernelMajorant M base high (ψ + t • u) v ≤ A := by
  let P : ℝ := ∏ i, M.grading base (v i)
  let Q : ℝ := ∑ i, M.grading high (v i) *
    ∏ j ∈ Finset.univ.erase i, M.grading base (v j)
  refine ⟨(1 + (M.grading high ψ + R * M.grading high u)) * P + Q, ?_, ?_⟩
  · exact add_nonneg
      (mul_nonneg (add_nonneg zero_le_one
        (add_nonneg (apply_nonneg _ _) (mul_nonneg hR (apply_nonneg _ _))))
        (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)))
      (Finset.sum_nonneg (fun i _ => mul_nonneg (apply_nonneg _ _)
        (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))))
  · intro t ht
    exact add_le_add
      (mul_le_mul_of_nonneg_right
        (add_le_add le_rfl (coupled_circle_affine_grading_le high ψ u ht))
        (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))) le_rfl

/-- The same envelope controls every jet in a fixed Hilbert row. -/
theorem coupled_circle_kernel_affine_jet_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hγ : 0 < γ) (hM : IsCircleModel T γ M) (hI : HasInterpolation M.grading)
    (r k s : ℕ) (ψ u v : M.Space) (w : Fin k → M.Space)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, |t| ≤ R →
      ∀ (m : ℕ) (j : CircleJetIndex s) (θ : ℝ),
        |(T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)) *
            iteratedDeriv (j.val 0).val
              (coupledCircleKernelField M r k (ψ + t • u) v w m) θ| ≤
          A * (T.M (T.sample m))⁻¹ := by
  have hs := spaces_trace_sample_mem hD hT
  have hexists := coupled_circle_kernel_jet_bounds hT hs hγ hM hI
  let base : ℕ := hexists.choose
  let loss : ℕ := hexists.choose_spec.choose
  have hb := hexists.choose_spec.choose_spec
  let L : ℝ := max 1 (M.grading base ψ + R * M.grading base u)
  obtain ⟨C, hC, hc⟩ := hb r k s L (le_max_left _ _)
  obtain ⟨A, hA, ha⟩ := coupled_circle_kernel_majorant_affine_bound
    base (r + s + loss) ψ u (Fin.cons v w) hR
  refine ⟨C * A, mul_nonneg hC hA, fun t ht m j θ => ?_⟩
  have hlow : M.grading base (ψ + t • u) ≤ L :=
    (coupled_circle_affine_grading_le base ψ u ht).trans (le_max_right _ _)
  exact (hc (ψ + t • u) hlow v w m j θ).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ha t ht) hC)
      (inv_nonneg.mpr (zero_le_one.trans (hT.2.1 _ (hs m)).2.2.2)))

def coupledCircleKernelJetLp
    (hM : IsCircleModel T γ M) (r k b c : ℕ)
    (ψ v : M.Space) (w : Fin k → M.Space) (m : ℕ) : AngleL2 :=
  ((memLp_angleMeasure_iteratedDeriv_of_contDiff
    (coupledCircleKernelField_contDiff hM r k ψ v w m) b).const_mul
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ))).toLp
    (fun θ => (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
      iteratedDeriv b (coupledCircleKernelField M r k ψ v w m) θ)

theorem coupledCircleKernelJetLp_ae
    (hM : IsCircleModel T γ M) (r k b c : ℕ)
    (ψ v : M.Space) (w : Fin k → M.Space) (m : ℕ) :
    (coupledCircleKernelJetLp hM r k b c ψ v w m : ℝ → ℝ) =ᵐ[angleMeasure]
      (fun θ => (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
        iteratedDeriv b (coupledCircleKernelField M r k ψ v w m) θ) :=
  MemLp.coeFn_toLp _

theorem coupledCircleKernelJetLp_norm_le
    (hM : IsCircleModel T γ M) (r k b c : ℕ)
    (ψ v : M.Space) (w : Fin k → M.Space) (m : ℕ)
    {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ θ, |(T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
      iteratedDeriv b (coupledCircleKernelField M r k ψ v w m) θ| ≤ A) :
    ‖coupledCircleKernelJetLp hM r k b c ψ v w m‖ ≤ spacesAngleL2Constant * A := by
  rw [coupledCircleKernelJetLp, Lp.norm_toLp]
  exact spaces_angle_norm_le_of_abs_le
    (continuous_const.mul (spaces_contDiff_iteratedDeriv
      (coupledCircleKernelField_contDiff hM r k ψ v w m) b).continuous).aestronglyMeasurable hA hb

end ContinuousFlexibility.Statements
