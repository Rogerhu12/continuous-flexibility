import ContinuousFlexibility.Analysis.NeighborhoodCircleChartsState

/-!
# The actual left root label, with all finite angular jet differences

The left label is the original stateLeftChart. Its difference from the
reference identity is exactly the decoded circle coordinate, so the
original circle norm gives every finite boundary jet with its actual
sample weight. No independently prescribed boundary label is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff ENNReal

set_option backward.isDefEq.respectTransparency false

private theorem n06_root_circle_unweight {a H γ B : ℝ}
    (hH : 0 < H) (h : |H ^ (-γ) * a| ≤ B) : |a| ≤ B * H ^ γ := by
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hH (-γ)),
    Real.rpow_neg hH.le, ← div_eq_inv_mul] at h
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hH γ)).mp h

theorem n06_circleModel_finite_jet_weight_bound
    {T : MaterialData} {M : CircleModelData} {γ : ℝ}
    (hM : IsCircleModel T γ M) (hH : ∀ m, 0 < T.H (T.sample m))
    (u : M.Space) (n m j : ℕ) (hj : j ≤ n) (θ : ℝ) :
    |iteratedDeriv j (M.decode u m) θ| ≤
      (anglePairEvaluationConstant * M.grading (n + 1) u) * T.H (T.sample m) ^ γ := by
  have hu : CircleMember T γ (M.decode u) := hM.2.2.2.1 u
  have hw : |T.H (T.sample m) ^ (-γ) * iteratedDeriv j (M.decode u m) θ| ≤
      anglePairEvaluationConstant * ‖circleJetEncodeHilbert hu (n + 1) m‖ := by
    simpa only [pow_zero, one_mul] using
      spaces_circle_weighted_pointwise hu (n + 1) m j 0 (by omega) θ
  have hrow : ‖circleJetEncodeHilbert hu (n + 1) m‖ ≤ circleNorm T γ (n + 1) (M.decode u) :=
    (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (circleJetEncodeHilbert hu (n + 1)) m).trans_eq (circleJetEncodeHilbert_norm hu (n + 1))
  have hgrade : circleNorm T γ (n + 1) (M.decode u) ≤ M.grading (n + 1) u :=
    (hM.2.2.2.2.2.2.2 u (n + 1)).symm.trans_le
      (norm_coordinate_le_graded _ _ le_rfl u)
  exact n06_root_circle_unweight (hH m)
    (hw.trans (mul_le_mul_of_nonneg_left (hrow.trans hgrade) anglePairEvaluationConstant_nonneg))

private theorem n06_root_label_jet_difference
    {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) (n : ℕ) (θ : ℝ) :
    iteratedDeriv n (fun t => t + η t) θ - iteratedDeriv n (fun t : ℝ => t) θ =
      iteratedDeriv n η θ := by
  have hid : ContDiffAt ℝ (n : ℕ) (fun t : ℝ => t) θ := contDiffAt_id
  have h := iteratedDeriv_fun_add hid (hη.contDiffAt.of_le (by simp))
  change iteratedDeriv n (fun t : ℝ => t + η t) θ =
    iteratedDeriv n (fun t : ℝ => t) θ + iteratedDeriv n η θ at h
  rw [h]
  ring

theorem n06_stateLeftChart_boundary_label_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (href : referenceStateConditions D S C)
    (n : ℕ) (x : AnnularState S) (m j : ℕ) (hj : j ≤ n) (θ : ℝ) :
    |iteratedDeriv j (stateLeftChart S x m) θ - iteratedDeriv j (fun t : ℝ => t) θ| ≤
      (anglePairEvaluationConstant * stateGrading S (n + 1) (x - C.referenceState)) *
        T.H (T.sample m) ^ (3 / 4 : ℝ) := by
  have hmodel := hS.2.1 (3 / 4 : ℝ)
  have hH (i : ℕ) : 0 < T.H (T.sample i) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT hD.choose_spec.2.1 i)).2.1
  have hbound := n06_circleModel_finite_jet_weight_bound hmodel hH x.2.2.2 n m j hj θ
  have hzero : C.referenceState.2.2.2 = 0 := href.2.2.2.2.1
  have hcoord : (x - C.referenceState).2.2.2 = x.2.2.2 := by
    simp only [Prod.snd_sub, hzero, sub_zero]
  have hgrade : (S.circle (3 / 4 : ℝ)).grading (n + 1) x.2.2.2 ≤
      stateGrading S (n + 1) (x - C.referenceState) :=
    (congrArg ((S.circle (3 / 4 : ℝ)).grading (n + 1)) hcoord).symm.trans_le
      (neighborhoodStateGrading_chart_le S (n + 1) (x - C.referenceState))
  have hη : ContDiff ℝ ∞ ((S.circle (3 / 4 : ℝ)).decode x.2.2.2 m) :=
    ((hmodel.2.2.2.1 x.2.2.2).1 m).1
  have he := n06_root_label_jet_difference hη j θ
  change iteratedDeriv j (stateLeftChart S x m) θ -
    iteratedDeriv j (fun t : ℝ => t) θ =
      iteratedDeriv j ((S.circle (3 / 4 : ℝ)).decode x.2.2.2 m) θ at he
  exact (congrArg abs he).trans_le
    (hbound.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgrade anglePairEvaluationConstant_nonneg)
        (Real.rpow_nonneg (hH m).le _)))

end ContinuousFlexibility.Statements
