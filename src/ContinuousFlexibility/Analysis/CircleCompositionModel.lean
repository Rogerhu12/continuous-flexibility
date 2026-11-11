import ContinuousFlexibility.Analysis.CircleWeightedComposition

/-!
# Chart composition in the supplied circle model

A decoded chart perturbation has uniformly bounded angular derivatives:
its weighted Sobolev evaluation bound and the material envelope give this
directly.  Thus composition by its degree-one lift is an actual continuous
linear operator on the same circle model, with one fixed derivative loss.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ContDiff ENNReal BigOperators NNReal

set_option backward.isDefEq.respectTransparency false

def circleComposeFieldLinear (S : CircleModelData) (φ : ℕ → ℝ → ℝ) :
    S.Space →ₗ[ℝ] (ℕ → ℝ → ℝ) where
  toFun u := circleComposeField (S.decode u) φ
  map_add' u v := by
    funext m θ
    simp only [circleComposeField_apply, map_add, Pi.add_apply]
  map_smul' r u := by
    funext m θ
    simp only [circleComposeField_apply, map_smul, Pi.smul_apply, RingHom.id_apply]

theorem circleComposeFieldLinear_apply (S : CircleModelData) (φ : ℕ → ℝ → ℝ)
    (u : S.Space) (m : ℕ) (θ : ℝ) :
    circleComposeFieldLinear S φ u m θ = S.decode u m (φ m θ) := rfl

section FixedLift

variable {T : MaterialData} {γ : ℝ} {S : CircleModelData}
  (hS : IsCircleModel T γ S)
  (hM : ∀ m, 0 < T.M (T.sample m)) (hH : ∀ m, 0 < T.H (T.sample m))
  (φ : ℕ → ℝ → ℝ)
  (hφ : ∀ m, ContDiff ℝ ∞ (φ m))
  (hp : ∀ m θ, φ m (θ + Real.pi) = φ m θ + Real.pi)
  (hjets : ∀ s, ∃ B : ℝ, 0 ≤ B ∧
    ∀ m i θ, 1 ≤ i → i ≤ s → |iteratedDeriv i (φ m) θ| ≤ B ^ i)

include hS hM hH hφ hp hjets

theorem circleComposeFieldLinear_member (u : S.Space) :
    CircleMember T γ (circleComposeFieldLinear S φ u) := by
  change CircleMember T γ (circleComposeField (S.decode u) φ)
  exact circleMember_comp_of_uniform_jets (u := S.decode u) (φ := φ)
    (hS.2.2.2.1 u) hM hH hφ hp hjets

def circleComposeModelLinear : S.Space →ₗ[ℝ] S.Space :=
  liftCircleLinear hS (circleComposeFieldLinear S φ)
    (circleComposeFieldLinear_member hS hM hH φ hφ hp hjets)

theorem circleComposeModelLinear_decode (u : S.Space) :
    S.decode (circleComposeModelLinear hS hM hH φ hφ hp hjets u) =
      circleComposeField (S.decode u) φ :=
  liftCircleLinear_decode hS (circleComposeFieldLinear S φ)
    (circleComposeFieldLinear_member hS hM hH φ hφ hp hjets) u

theorem circleComposeModelLinear_isTame :
    IsTameLinear S.grading S.grading
      (circleComposeModelLinear hS hM hH φ hφ hp hjets) 1 0 := by
  apply liftCircleLinear_isTame hS (circleComposeFieldLinear S φ)
    (circleComposeFieldLinear_member hS hM hH φ hφ hp hjets)
    S.grading (gradedSeminorm_monotone (fun i => S.level i) S.bond) 1
  intro n
  obtain ⟨B, hB0, hB⟩ := hjets n
  refine ⟨⟨circleCompositionNormConstant n B, circleCompositionNormConstant_nonneg n B⟩, ?_⟩
  intro u
  have hbound := circleNorm_comp_le (hS.2.2.2.1 u) hM hH hφ n hB0 hB
  have hgrade := ((circleGrading_le_iff_circleNorm hS (n + 1) u (apply_nonneg _ _)).mp
    (le_refl (S.grading (n + 1) u))) (n + 1) le_rfl
  exact hbound.trans (mul_le_mul_of_nonneg_left hgrade (circleCompositionNormConstant_nonneg n B))

theorem circleComposeModelLinear_continuous :
    Continuous (circleComposeModelLinear hS hM hH φ hφ hp hjets) :=
  (circleComposeModelLinear_isTame hS hM hH φ hφ hp hjets).continuous
    (withSeminorms_graded (fun i => S.level i) S.bond)
    (withSeminorms_graded (fun i => S.level i) S.bond)
    (gradedSeminorm_monotone (fun i => S.level i) S.bond)

end FixedLift

def circleModelLift (S : CircleModelData) (u : S.Space) : ℕ → ℝ → ℝ :=
  fun m θ => θ + S.decode u m θ

theorem circleModelLift_apply (S : CircleModelData) (u : S.Space) (m : ℕ) (θ : ℝ) :
    circleModelLift S u m θ = θ + S.decode u m θ := rfl

theorem circleModelLift_contDiff {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (u : S.Space) (m : ℕ) :
    ContDiff ℝ ∞ (circleModelLift S u m) := by
  have hu := ((hS.2.2.2.1 u).1 m).1
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  exact (contDiff_id.add hu).contDiffAt.congr_of_eventuallyEq
    (Eventually.of_forall fun t => by
      simp only [circleModelLift_apply, Pi.add_apply, id_eq])

theorem circleModelLift_periodic {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (u : S.Space) (m : ℕ) (θ : ℝ) :
    circleModelLift S u m (θ + Real.pi) = circleModelLift S u m θ + Real.pi := by
  rw [circleModelLift_apply, circleModelLift_apply, ((hS.2.2.2.1 u).1 m).2 θ]
  ring

/-- An upper bound on the material envelope turns the actual weighted
Sobolev pointwise estimate into uniform bounds on lift derivatives. -/
theorem circleModelLift_uniform_jets {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (hH : ∀ m, 0 < T.H (T.sample m))
    {A : ℝ} (hA : 0 ≤ A) (hHA : ∀ m, T.H (T.sample m) ^ γ ≤ A)
    (u : S.Space) (s : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m i θ, 1 ≤ i → i ≤ s →
      |iteratedDeriv i (circleModelLift S u m) θ| ≤ B ^ i := by
  let B : ℝ := 1 + (2 * circleSobolevConstant * S.grading (s + 1) u) * A
  have hB1 : 1 ≤ B := le_add_of_nonneg_right
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) circleSobolevConstant_nonneg)
      (apply_nonneg _ _)) hA)
  refine ⟨B, zero_le_one.trans hB1, ?_⟩
  intro m i θ hi his
  have hui := ((hS.2.2.2.1 u).1 m).1
  have hsplit :
      iteratedDeriv i (circleModelLift S u m) θ =
        iteratedDeriv i (fun t : ℝ => t) θ + iteratedDeriv i (S.decode u m) θ := by
    have hidreg : ContDiffAt ℝ (i : ℕ∞ω) (fun t : ℝ => t) θ := contDiffAt_id
    exact iteratedDeriv_fun_add hidreg (hui.contDiffAt.of_le (by simp))
  have hid : |iteratedDeriv i (fun t : ℝ => t) θ| ≤ 1 := by
    rw [iteratedDeriv_fun_id, if_neg (by omega : i ≠ 0)]
    split_ifs <;> norm_num
  have hgrade : S.grading (i + 1) u ≤ S.grading (s + 1) u :=
    gradedSeminorm_monotone (fun j => S.level j) S.bond (Nat.add_le_add_right his 1) u
  have hscale : 0 ≤ 2 * circleSobolevConstant := mul_nonneg (by norm_num) circleSobolevConstant_nonneg
  have hpoint := circleModel_iteratedDeriv_abs_le hS hH u m i θ
  have hpoint' : |iteratedDeriv i (S.decode u m) θ| ≤
      (2 * circleSobolevConstant * S.grading (s + 1) u) * A :=
    hpoint.trans (mul_le_mul (mul_le_mul_of_nonneg_left hgrade hscale) (hHA m)
      (Real.rpow_nonneg (hH m).le _) (mul_nonneg hscale (apply_nonneg _ _)))
  calc
    |iteratedDeriv i (circleModelLift S u m) θ| ≤
        |iteratedDeriv i (fun t : ℝ => t) θ| + |iteratedDeriv i (S.decode u m) θ| := by
      rw [hsplit]
      exact abs_add_le _ _
    _ ≤ B := add_le_add hid hpoint'
    _ ≤ B ^ i := by simpa only [pow_one] using pow_le_pow_right₀ hB1 hi

theorem material_circle_sample_weights_pos {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D) :
    (∀ m, 0 < T.M (T.sample m)) ∧ (∀ m, 0 < T.H (T.sample m)) := by
  obtain ⟨_, hbounds⟩ := hD
  have hs := materialSample_mem_radialCore hT hbounds.2.1
  exact ⟨fun m => zero_lt_one.trans_le (hT.2.1 _ (hs m)).2.2.2,
    fun m => (hT.2.1 _ (hs m)).2.1⟩

theorem circleModelLift_uniform_jets_of_material
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (u : S.Space) (s : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m i θ, 1 ≤ i → i ≤ s →
      |iteratedDeriv i (circleModelLift S u m) θ| ≤ B ^ i := by
  have hH := (material_circle_sample_weights_pos hT hD).2
  obtain ⟨_, hbounds⟩ := hD
  have hs := materialSample_mem_radialCore hT hbounds.2.1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hdecay, _⟩ := hT
  obtain ⟨A, hA, hbound, _⟩ := hdecay 0 γ hγ
  apply circleModelLift_uniform_jets hS hH hA.le (u := u) (s := s)
  intro m
  simpa only [Real.rpow_zero, mul_one] using hbound (T.sample m) (hs m)

/-- Composition by a decoded degree-one chart is realized in the very
same physical circle model. -/
def circleChartComposeLinear
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (h : S.Space) :
    S.Space →ₗ[ℝ] S.Space :=
  circleComposeModelLinear hS (material_circle_sample_weights_pos hT hD).1
    (material_circle_sample_weights_pos hT hD).2 (circleModelLift S h)
    (circleModelLift_contDiff hS h) (circleModelLift_periodic hS h)
    (circleModelLift_uniform_jets_of_material hS hT hD hγ h)

theorem circleChartComposeLinear_decode
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (h u : S.Space) (m : ℕ) (θ : ℝ) :
    S.decode (circleChartComposeLinear hS hT hD hγ h u) m θ =
      S.decode u m (θ + S.decode h m θ) := by
  have hdecode := circleComposeModelLinear_decode hS (material_circle_sample_weights_pos hT hD).1
    (material_circle_sample_weights_pos hT hD).2 (circleModelLift S h)
    (circleModelLift_contDiff hS h) (circleModelLift_periodic hS h)
    (circleModelLift_uniform_jets_of_material hS hT hD hγ h) u
  exact congrFun (congrFun hdecode m) θ

theorem circleChartComposeLinear_isTame
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (h : S.Space) :
    IsTameLinear S.grading S.grading (circleChartComposeLinear hS hT hD hγ h) 1 0 :=
  circleComposeModelLinear_isTame hS (material_circle_sample_weights_pos hT hD).1
    (material_circle_sample_weights_pos hT hD).2 (circleModelLift S h)
    (circleModelLift_contDiff hS h) (circleModelLift_periodic hS h)
    (circleModelLift_uniform_jets_of_material hS hT hD hγ h)

end ContinuousFlexibility.Statements
