module

public import ContinuousFlexibility.Analysis.SpacesNemytskiiTermBounds

/-!
# The zero-factor term of the composition formula

The only composition term without an explicit height factor has scalar
order zero. The condition `F 0 = 0` supplies the missing factor through a
global first-derivative bound, cancelling the inverse physical height.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

theorem spaces_memLp_lpNorm_le_of_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : AEStronglyMeasurable g μ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, |g x| ≤ C * |f x|) :
    MemLp g 2 μ ∧ lpNorm g 2 μ ≤ C * lpNorm f 2 μ := by
  have he : eLpNorm g 2 μ ≤ eLpNorm (C • f) 2 μ := by
    apply eLpNorm_mono_ae hg
    filter_upwards [] with x
    simpa only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hC] using hbound x
  refine ⟨lt_of_le_of_lt he (hf.const_smul C), ?_⟩
  have ht := ENNReal.toReal_mono (hf.const_smul C).eLpNorm_ne_top he
  simpa only [toReal_eLpNorm, lpNorm_const_smul, coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hC] using ht

theorem spaces_nemytskii_zero_factor_bound {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {γ : ℝ} (t : SpacesNemytskiiTerm T γ 0) (hq : t.baseFactors = 0)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hzero : F 0 = 0)
    (hFb : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |deriv F x| ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℕ) (u : PhysicalJetProjectiveLimit hT)
      (v : Fin 0 → PhysicalJetProjectiveLimit hT),
      MemLp (t.weightedEvaluate hT F c u v) 2 materialCylinderMeasure ∧
      lpNorm (t.weightedEvaluate hT F c u v) 2 materialCylinderMeasure ≤
        C * spacesPhysicalGrading hT c u := by
  obtain ⟨A, hA, hAbound⟩ := t.coefficient_mem.bound
  have hAb (x : ℝ) : |t.coefficient x| ≤ A * T.H (T.radius x) ^ (-γ) := by
    simpa only [hq, Nat.zero_add, Nat.cast_zero, zero_sub, neg_one_mul] using hAbound x
  obtain ⟨B, hB, hBbound⟩ := hFb
  have hFlin (x : ℝ) : |F x| ≤ B * |x| := by
    simpa only [hzero, sub_zero] using spaces_scalar_lipschitz_of_derivative_bound
      (hF.differentiable (by simp)) hBbound x 0
  refine ⟨A * B, mul_nonneg hA hB, fun c u v => ?_⟩
  have hcont : Continuous (t.weightedEvaluate hT F c u v) := by
    have hM : ContDiff ℝ ∞ (fun p : PolarPoint => T.M (T.radius p.1)) :=
      (hT.1 T.M (by simp)).comp_contDiff (hT.2.2.2.2.2.2.1.comp contDiff_fst)
        (fun p => (hT.2.2.2.2.2.2.2.1 p.1).1)
    exact (hM.pow c).continuous.mul
      (t.evaluate_contDiff hT hF (spacesPhysicalRepresentative_contDiff hT u)
        (fun i => spacesPhysicalRepresentative_contDiff hT (v i))).continuous
  have hpoint (p : PolarPoint) : |t.weightedEvaluate hT F c u v p| ≤
      (A * B) * |spacesNormalizedJet hT 0 0 c u p| := by
    let H := T.H (T.radius p.1)
    let U := spacesPhysicalRepresentative hT u p
    have hH : 0 < H := (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 p.1).1).2.1
    have hM : 0 ≤ T.M (T.radius p.1) ^ c :=
      pow_nonneg (zero_le_one.trans (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 p.1).1).2.2.2) c
    let : IsEmpty (Fin t.baseFactors) := by
      rw [hq]
      infer_instance
    have he : t.weightedEvaluate hT F c u v p =
        T.M (T.radius p.1) ^ c * (t.coefficient p.1 * F (H ^ γ * U)) := by
      simp only [SpacesNemytskiiTerm.weightedEvaluate, SpacesNemytskiiTerm.evaluate,
        Finset.univ_eq_empty, Finset.prod_empty, mul_one, Nat.zero_add, hq, iteratedDeriv_zero, H, U]
    have hcancel : H ^ (-γ) * H ^ γ = 1 := by
      rw [← Real.rpow_add hH, neg_add_cancel, Real.rpow_zero]
    have hz : |spacesNormalizedJet hT 0 0 c u p| = T.M (T.radius p.1) ^ c * |U| := by
      simp only [spacesNormalizedJet, mixedDerivative, iteratedDeriv_zero, abs_mul, abs_of_nonneg hM, U]
    rw [he, abs_mul, abs_of_nonneg hM, abs_mul, hz]
    calc
      T.M (T.radius p.1) ^ c * (|t.coefficient p.1| * |F (H ^ γ * U)|) ≤
          T.M (T.radius p.1) ^ c * ((A * H ^ (-γ)) * (B * |H ^ γ * U|)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (hAb p.1) (hFlin _)
          (abs_nonneg _) (mul_nonneg hA (Real.rpow_pos_of_pos hH _).le)) hM
      _ = T.M (T.radius p.1) ^ c * ((A * H ^ (-γ)) * (B * (H ^ γ * |U|))) := by
        rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hH γ)]
      _ = (A * B) * (T.M (T.radius p.1) ^ c * ((H ^ (-γ) * H ^ γ) * |U|)) := by ring
      _ = (A * B) * (T.M (T.radius p.1) ^ c * |U|) := by rw [hcancel, one_mul]
  have h := spaces_memLp_lpNorm_le_of_abs_le (spacesNormalizedJet_memLp hT 0 0 c u)
    hcont.aestronglyMeasurable (mul_nonneg hA hB) hpoint
  exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_left
    (spacesNormalizedJet_lpNorm_le hT 0 0 c c (by omega) u) (mul_nonneg hA hB))⟩

end ContinuousFlexibility.Statements
