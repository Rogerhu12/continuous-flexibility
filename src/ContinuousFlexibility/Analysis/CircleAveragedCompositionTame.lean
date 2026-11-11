import ContinuousFlexibility.Analysis.CircleAveragedComposition

/-!
# Fixed loss estimates for the averaged chart operator

The scalar parameter interval has length one.  Its angular derivatives
therefore retain the same component-energy bound as each fixed chart.
The averaged operator has one angular derivative of loss and defines an
actual continuous linear map in the supplied circle model.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem weighted_iteratedDeriv_unitParameterIntegral_le
    {F : ℝ → ℝ → ℝ} (hF : ∀ n, AngularRegular n F)
    (n : ℕ) (θ : ℝ) {w K : ℝ} (hw : 0 ≤ w)
    (hb : ∀ a ∈ Icc (0 : ℝ) 1, w * |iteratedDeriv n (F a) θ| ≤ K) :
    w * |iteratedDeriv n (fun x => ∫ a in (0 : ℝ)..1, F a x) θ| ≤ K := by
  rw [iteratedDeriv_unitParameterIntegral hF]
  have hnorm : ‖∫ a in (0 : ℝ)..1, w * iteratedDeriv n (F a) θ‖ ≤ K := by
    have hpoint : ∀ a ∈ uIoc (0 : ℝ) 1, ‖w * iteratedDeriv n (F a) θ‖ ≤ K := by
      intro a ha
      have ha' : a ∈ Icc (0 : ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using (uIoc_subset_uIcc ha)
      simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw] using hb a ha'
    simpa only [sub_zero, abs_one, mul_one] using
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  simpa only [intervalIntegral.integral_const_mul, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg hw] using hnorm

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ContDiff ENNReal NNReal BigOperators

theorem contDiff_circleAverageComposeField
    {u e : ℕ → ℝ → ℝ}
    (hu : ∀ m, ContDiff ℝ ∞ (u m)) (he : ∀ m, ContDiff ℝ ∞ (e m))
    (travel : ℕ → ℝ) (m : ℕ) :
    ContDiff ℝ ∞ (circleAverageComposeField u travel e m) := by
  have hg : ContDiff ℝ ∞ (fun p : PolarPoint =>
      p.2 + travel m + p.1 * e m p.2) :=
    (contDiff_snd.add contDiff_const).add (contDiff_fst.mul ((he m).comp contDiff_snd))
  exact contDiff_unitParameterIntegral
    (fun n => angularRegular_of_contDiff ((hu m).comp hg) n)

theorem circleWeighted_averageCompose_pointwise_le
    {T : MaterialData} {γ : ℝ} {u e : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (he : ∀ m, ContDiff ℝ ∞ (e m))
    (hM : ∀ m, 0 < T.M (T.sample m)) (hH : ∀ m, 0 < T.H (T.sample m))
    (travel : ℕ → ℝ) {s : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ m i θ, i ≤ s → |iteratedDeriv i (e m) θ| ≤ B)
    (m b k : ℕ) (horder : b + k ≤ s) (θ : ℝ) :
    (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
      |iteratedDeriv b (circleAverageComposeField u travel e m) θ| ≤
      circleCompositionJetConstant s (1 + B) *
        Real.sqrt (circleComponentEnergy T γ (s + 1) u m).toReal := by
  have hg : ContDiff ℝ ∞ (fun p : PolarPoint =>
      p.2 + travel m + p.1 * e m p.2) :=
    (contDiff_snd.add contDiff_const).add (contDiff_fst.mul ((he m).comp contDiff_snd))
  have hbase : 0 ≤ 1 + B := by linarith only [hB]
  apply weighted_iteratedDeriv_unitParameterIntegral_le
    (fun n => angularRegular_of_contDiff ((hu.1 m).1.comp hg) n) b θ
    (mul_nonneg (pow_nonneg (hM m).le k) (Real.rpow_nonneg (hH m).le _))
  intro a ha
  have hpoint := circleWeighted_comp_iteratedDeriv_abs_le hu (hM m) (hH m)
    (n := b) (k := k) (s := s + 1) (by omega)
    (circleAffineLift_contDiff he travel a m) θ
    (fun i hi hib => circleAffineLift_uniform_jets he travel hB hb ha m i θ hi (by omega))
  exact hpoint.trans (mul_le_mul_of_nonneg_right
    (circleCompositionJetConstant_term_le hbase (by omega)) (Real.sqrt_nonneg _))

theorem circleNorm_averageCompose_le
    {T : MaterialData} {γ : ℝ} {u e : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (he : ∀ m, ContDiff ℝ ∞ (e m))
    (hM : ∀ m, 0 < T.M (T.sample m)) (hH : ∀ m, 0 < T.H (T.sample m))
    (travel : ℕ → ℝ) (s : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ m i θ, i ≤ s → |iteratedDeriv i (e m) θ| ≤ B) :
    circleNorm T γ s (circleAverageComposeField u travel e) ≤
      circleCompositionNormConstant s (1 + B) * circleNorm T γ (s + 1) u := by
  let A := (Fintype.card (CircleJetIndex s) : ℝ) *
    (Real.pi * circleCompositionJetConstant s (1 + B) ^ 2)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hbase : 0 ≤ 1 + B := by linarith only [hB]
  have henergy :
      (∑' m, circleComponentEnergy T γ s (circleAverageComposeField u travel e) m) ≤
        ENNReal.ofReal A * ∑' m, circleComponentEnergy T γ (s + 1) u m := by
    rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro m
    exact circleComponentEnergy_le_of_pointwise hu
      (contDiff_circleAverageComposeField (fun i => (hu.1 i).1) he travel)
      (fun i => (hM i).le) (fun i => (hH i).le) s (s + 1)
      (circleCompositionJetConstant_nonneg s hbase)
      (circleWeighted_averageCompose_pointwise_le hu he hM hH travel hB hb) m
  have hfinite := ENNReal.mul_lt_top
    (ENNReal.ofReal_lt_top (r := A)) (hu.2.2 (s + 1))
  have hr := ENNReal.toReal_mono hfinite.ne henergy
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA] at hr
  have hs := Real.sqrt_le_sqrt hr
  rw [Real.sqrt_mul hA] at hs
  exact hs

section Model

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}
  (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
  (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
  (travel : ℕ → ℝ) (e : S.Space)

include hS hT hD hγ in
theorem circleAverageComposeField_grading_bound (n : ℕ) :
    ∃ K : ℝ≥0, ∀ u : S.Space,
      circleNorm T γ n (circleAverageComposeField (S.decode u) travel (S.decode e)) ≤
        (K : ℝ) * S.grading (n + 1) u := by
  obtain ⟨B, hB, hb⟩ := circleModel_uniform_jets_of_material hS hT hD hγ e n
  refine ⟨⟨circleCompositionNormConstant n (1 + B),
    circleCompositionNormConstant_nonneg n (1 + B)⟩, fun u => ?_⟩
  have hn := circleNorm_averageCompose_le (hS.2.2.2.1 u)
    (fun m => ((hS.2.2.2.1 e).1 m).1)
    (material_circle_sample_weights_pos hT hD).1
    (material_circle_sample_weights_pos hT hD).2 travel n hB hb
  have hg := ((circleGrading_le_iff_circleNorm hS (n + 1) u (apply_nonneg _ _)).mp
    (le_refl (S.grading (n + 1) u))) (n + 1) le_rfl
  exact hn.trans (mul_le_mul_of_nonneg_left hg
    (circleCompositionNormConstant_nonneg n (1 + B)))

theorem circleAverageComposeLinear_isTame :
    IsTameLinear S.grading S.grading
      (circleAverageComposeLinear hS hT hD hγ travel e) 1 0 := by
  unfold circleAverageComposeLinear
  apply liftCircleLinear_isTame hS
    (circleAverageComposeFieldLinear hS travel (S.decode e))
    (fun u => circleMember_averageCompose (hS.2.2.2.1 u) (hS.2.2.2.1 e).1
      (material_circle_sample_weights_pos hT hD).1
      (material_circle_sample_weights_pos hT hD).2
      (circleModel_uniform_jets_of_material hS hT hD hγ e) travel)
    S.grading (gradedSeminorm_monotone (fun i => S.level i) S.bond) 1
  intro n
  exact circleAverageComposeField_grading_bound hS hT hD hγ travel e n

def circleAverageComposeContinuousLinear : S.Space →L[ℝ] S.Space :=
  (circleAverageComposeLinear_isTame hS hT hD hγ travel e).toContinuousLinearMap
    (withSeminorms_graded (fun i => S.level i) S.bond)
    (withSeminorms_graded (fun i => S.level i) S.bond)
    (gradedSeminorm_monotone (fun i => S.level i) S.bond)

theorem circleAverageComposeContinuousLinear_decode
    (u : S.Space) (m : ℕ) (θ : ℝ) :
    S.decode (circleAverageComposeContinuousLinear hS hT hD hγ travel e u) m θ =
      ∫ a in (0 : ℝ)..1, S.decode u m
        (θ + travel m + a * S.decode e m θ) := by
  have heq : circleAverageComposeContinuousLinear hS hT hD hγ travel e u =
      circleAverageComposeLinear hS hT hD hγ travel e u :=
    IsTameLinear.toContinuousLinearMap_apply
      (circleAverageComposeLinear_isTame hS hT hD hγ travel e)
      (withSeminorms_graded (fun i => S.level i) S.bond)
      (withSeminorms_graded (fun i => S.level i) S.bond)
      (gradedSeminorm_monotone (fun i => S.level i) S.bond) u
  exact (congrArg (fun v : S.Space => S.decode v m θ) heq).trans
    (circleAverageComposeLinear_decode hS hT hD hγ travel e u m θ)

end Model

end ContinuousFlexibility.Statements
