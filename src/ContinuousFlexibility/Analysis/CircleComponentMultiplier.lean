module

public import ContinuousFlexibility.Analysis.CircleComponentContraction
public import ContinuousFlexibility.Analysis.CircleWeightedProduct

/-!
# Component multipliers with a fixed sample-weight loss

The scalar multiplying each circle may grow by a fixed power of its
actual material sample weight. The complete weighted jet norm then
shifts only that weight index. The construction uses the same decoder
and the same scalar field map as the component contractions.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff ENNReal NNReal

theorem circle_component_multiplier_eLpNorm
    {T : MaterialData} {u : ℕ → ℝ → ℝ}
    (c : ℕ → ℝ) (d : ℕ) (K : ℝ)
    (hc : ∀ m, |c m| ≤ K * T.M (T.sample m) ^ d) (m b : ℕ) :
    eLpNorm (iteratedDeriv b (fun θ => c m * u m θ)) 2 angleMeasure ≤
      ENNReal.ofReal (K * T.M (T.sample m) ^ d) *
        eLpNorm (iteratedDeriv b (u m)) 2 angleMeasure := by
  have heq : iteratedDeriv b (fun θ => c m * u m θ) =
      (c m) • iteratedDeriv b (u m) := by
    funext θ
    exact iteratedDeriv_const_mul_field (c m) (u m)
  rw [heq, eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs]
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hc m)) _

theorem circleMember_component_multiplier
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u)
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (c : ℕ → ℝ) (d : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hc : ∀ m, |c m| ≤ K * T.M (T.sample m) ^ d) :
    CircleMember T γ (fun m θ => c m * u m θ) := by
  apply circleMember_of_L2_derivative_bound hu 0 d hK hM hH
  · intro m
    refine ⟨contDiff_const.mul (hu.1 m).1, fun θ => ?_⟩
    change c m * u m (θ + Real.pi) = c m * u m θ
    rw [(hu.1 m).2 θ]
  · intro m b
    simpa only [Nat.add_zero] using circle_component_multiplier_eLpNorm c d K hc m b

theorem circleNorm_component_multiplier_le
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u)
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (c : ℕ → ℝ) (d : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hc : ∀ m, |c m| ≤ K * T.M (T.sample m) ^ d) (s : ℕ) :
    circleNorm T γ s (fun m θ => c m * u m θ) ≤ K * circleNorm T γ (s + d) u := by
  have h := circleNorm_le_of_L2_derivative_bound hu s 0 d hK hM hH
    (fun m b => by simpa only [Nat.add_zero] using
      circle_component_multiplier_eLpNorm c d K hc m b)
  simpa only [Nat.add_zero] using h

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

def circleComponentMultiplierLinear (hS : IsCircleModel T γ S)
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    (c : ℕ → ℝ) (d : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hc : ∀ m, |c m| ≤ K * T.M (T.sample m) ^ d) : S.Space →ₗ[ℝ] S.Space :=
  liftCircleLinear hS (circleComponentContractionFieldLinear c)
    (fun u => circleMember_component_multiplier (hS.2.2.2.1 u)
      (fun m => ((material_circle_sample_weights_pos hT hD).1 m).le)
      (fun m => ((material_circle_sample_weights_pos hT hD).2 m).le) c d K hK hc)

theorem circleComponentMultiplierLinear_decode (hS : IsCircleModel T γ S)
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    (c : ℕ → ℝ) (d : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hc : ∀ m, |c m| ≤ K * T.M (T.sample m) ^ d) (u : S.Space) :
    S.decode (circleComponentMultiplierLinear hS hT hD c d K hK hc u) =
      fun m θ => c m * S.decode u m θ :=
  liftCircleLinear_decode hS (circleComponentContractionFieldLinear c)
    (fun v => circleMember_component_multiplier (hS.2.2.2.1 v)
      (fun m => ((material_circle_sample_weights_pos hT hD).1 m).le)
      (fun m => ((material_circle_sample_weights_pos hT hD).2 m).le) c d K hK hc) u

theorem circleComponentMultiplierLinear_grading_le (hS : IsCircleModel T γ S)
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    (c : ℕ → ℝ) (d : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hc : ∀ m, |c m| ≤ K * T.M (T.sample m) ^ d) (s : ℕ) (u : S.Space) :
    S.grading s (circleComponentMultiplierLinear hS hT hD c d K hK hc u) ≤
      K * S.grading (s + d) u := by
  apply (circleGrading_le_iff_circleNorm hS s _
    (mul_nonneg hK (apply_nonneg _ _))).mpr
  intro i hi
  rw [circleComponentMultiplierLinear_decode]
  have hn := circleNorm_component_multiplier_le (hS.2.2.2.1 u)
    (fun m => ((material_circle_sample_weights_pos hT hD).1 m).le)
    (fun m => ((material_circle_sample_weights_pos hT hD).2 m).le) c d K hK hc i
  exact hn.trans (mul_le_mul_of_nonneg_left
    (((circleGrading_le_iff_circleNorm hS (s + d) u (apply_nonneg _ _)).mp (le_refl _))
      (i + d) (Nat.add_le_add_right hi d)) hK)

theorem circleComponentMultiplierLinear_isTame (hS : IsCircleModel T γ S)
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    (c : ℕ → ℝ) (d : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hc : ∀ m, |c m| ≤ K * T.M (T.sample m) ^ d) :
    IsTameLinear S.grading S.grading
      (circleComponentMultiplierLinear hS hT hD c d K hK hc) d 0 := by
  intro s hs
  exact ⟨⟨K, hK⟩, fun u => circleComponentMultiplierLinear_grading_le hS hT hD c d K hK hc s u⟩

def circleComponentMultiplierContinuousLinear (hS : IsCircleModel T γ S)
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    (c : ℕ → ℝ) (d : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hc : ∀ m, |c m| ≤ K * T.M (T.sample m) ^ d) : S.Space →L[ℝ] S.Space :=
  (circleComponentMultiplierLinear_isTame hS hT hD c d K hK hc).toContinuousLinearMap
    (withSeminorms_graded (fun i => S.level i) S.bond)
    (withSeminorms_graded (fun i => S.level i) S.bond)
    (gradedSeminorm_monotone (fun i => S.level i) S.bond)

theorem circleComponentMultiplierContinuousLinear_apply (hS : IsCircleModel T γ S)
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    (c : ℕ → ℝ) (d : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hc : ∀ m, |c m| ≤ K * T.M (T.sample m) ^ d) (u : S.Space) :
    circleComponentMultiplierContinuousLinear hS hT hD c d K hK hc u =
      circleComponentMultiplierLinear hS hT hD c d K hK hc u :=
  IsTameLinear.toContinuousLinearMap_apply
    (circleComponentMultiplierLinear_isTame hS hT hD c d K hK hc)
    (withSeminorms_graded (fun i => S.level i) S.bond)
    (withSeminorms_graded (fun i => S.level i) S.bond)
    (gradedSeminorm_monotone (fun i => S.level i) S.bond) u

theorem smoothTameOn_circleComponentMultiplierLinear (hS : IsCircleModel T γ S)
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    (c : ℕ → ℝ) (d : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hc : ∀ m, |c m| ≤ K * T.M (T.sample m) ^ d) :
    SmoothTameOn S.grading S.grading Set.univ
      (circleComponentMultiplierLinear hS hT hD c d K hK hc) := by
  have h := smoothTameOn_continuousLinear
    (circleComponentMultiplierContinuousLinear hS hT hD c d K hK hc)
    (circleComponentMultiplierLinear_isTame hS hT hD c d K hK hc)
  exact smoothTameOn_congr h (fun u _ =>
    circleComponentMultiplierContinuousLinear_apply hS hT hD c d K hK hc u)

end ContinuousFlexibility.Statements
