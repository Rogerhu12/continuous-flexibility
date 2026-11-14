module

public import ContinuousFlexibility.Analysis.CircleInverseCompositionGrowth
public import ContinuousFlexibility.Analysis.CircleCompositionJetModels

/-!
# The actual inverse lift and its circle composition operator

Every decoded circle perturbation is bounded, so its degree-one lift is
surjective. A common positive derivative bound makes the actual invFun
its two-sided smooth inverse. Its uniform angular jets realize inverse
composition in the supplied circle model, without assuming membership of
the inverse lift itself.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

theorem bounded_perturbation_surjective
    {f : ℝ → ℝ} (hf : Continuous f) (c K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ x, |f x - (x + c)| ≤ K) : Function.Surjective f := by
  intro y
  let l : ℝ := y - c - K - 1
  let r : ℝ := y - c + K + 1
  have hlr : l ≤ r := by dsimp [l, r]; linarith
  have hl : f l ≤ y := by
    have h := (abs_le.mp (hb l)).2
    dsimp [l] at h
    linarith
  have hr : y ≤ f r := by
    have h := (abs_le.mp (hb r)).1
    dsimp [r] at h
    linarith
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hlr hf.continuousOn ⟨hl, hr⟩
  exact ⟨x, hfx⟩

theorem positive_jet_bounds_to_powers
    {ι : Type*} (f : ι → ℝ → ℝ)
    (hb : ∀ n : ℕ, 1 ≤ n → ∃ B : ℝ, 0 ≤ B ∧
      ∀ i θ, |iteratedDeriv n (f i) θ| ≤ B) (s : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i n θ, 1 ≤ n → n ≤ s →
      |iteratedDeriv n (f i) θ| ≤ B ^ n := by
  classical
  have hfinite (n : Fin (s + 1)) : ∃ B : ℝ, 0 ≤ B ∧
      ∀ i θ, 1 ≤ n.val → |iteratedDeriv n.val (f i) θ| ≤ B := by
    by_cases hn : 1 ≤ n.val
    · obtain ⟨B, hB, hbound⟩ := hb n.val hn
      exact ⟨B, hB, fun i θ _ => hbound i θ⟩
    · exact ⟨0, le_rfl, fun _ _ hn' => False.elim (hn hn')⟩
  choose B hB hbound using hfinite
  let K : ℝ := 1 + ∑ n : Fin (s + 1), B n
  have hK : 1 ≤ K := le_add_of_nonneg_right (Finset.sum_nonneg (fun n _ => hB n))
  refine ⟨K, zero_le_one.trans hK, ?_⟩
  intro i n θ hn hns
  let j : Fin (s + 1) := ⟨n, by omega⟩
  have hj : B j ≤ ∑ k, B k :=
    Finset.single_le_sum (f := B) (fun k _ => hB k) (Finset.mem_univ j)
  have hpow : K ≤ K ^ n := by simpa only [pow_one] using pow_le_pow_right₀ hK hn
  exact (hbound j i θ hn).trans
    ((hj.trans (by dsimp [K]; linarith)).trans hpow)

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

def circleAffineInverse (travel : ℕ → ℝ) (e : S.Space) : ℕ → ℝ → ℝ :=
  fun m => Function.invFun (circleAffineLift travel (S.decode e) 1 m)

theorem circleAffineLift_surjective
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (e : S.Space) (m : ℕ) :
    Function.Surjective (circleAffineLift travel (S.decode e) 1 m) := by
  obtain ⟨A, hA, hHA⟩ := material_circle_power_upper hT hD hγ
  let K : ℝ := (2 * circleSobolevConstant * A) * S.grading 1 e
  have hK : 0 ≤ K := mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) circleSobolevConstant_nonneg) hA)
    (apply_nonneg _ _)
  apply bounded_perturbation_surjective
    (circleAffineLift_contDiff (fun j => ((hS.2.2.2.1 e).1 j).1) travel 1 m).continuous
    (travel m) K hK
  intro θ
  have hb := circleModel_jet_abs_le_material_upper hS
    (material_circle_sample_weights_pos hT hD).2 hA hHA e m 0 θ
  simpa only [circleAffineLift, one_mul, add_sub_cancel_left,
    iteratedDeriv_zero, Nat.zero_add] using hb

theorem circleAffineInverse_right
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (e : S.Space) (m : ℕ) (θ : ℝ) :
    circleAffineLift travel (S.decode e) 1 m (circleAffineInverse travel e m θ) = θ :=
  Function.rightInverse_invFun (circleAffineLift_surjective hS hT hD hγ travel e m) θ

theorem circleAffineInverse_left
    (travel : ℕ → ℝ) (e : S.Space) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ m θ, a ≤ deriv (circleAffineLift travel (S.decode e) 1 m) θ)
    (m : ℕ) (θ : ℝ) :
    circleAffineInverse travel e m (circleAffineLift travel (S.decode e) 1 m θ) = θ :=
  Function.leftInverse_invFun
    (strictMono_of_deriv_pos (fun θ => ha.trans_le (hlower m θ))).injective θ

theorem circleAffineInverse_contDiff
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (e : S.Space) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ m θ, a ≤ deriv (circleAffineLift travel (S.decode e) 1 m) θ) (m : ℕ) :
    ContDiff ℝ ∞ (circleAffineInverse travel e m) :=
  returnChart_inverse_contDiff _ _
    (circleAffineLift_contDiff (fun j => ((hS.2.2.2.1 e).1 j).1) travel 1 m)
    (fun θ => ha.trans_le (hlower m θ)) (circleAffineInverse_left travel e ha hlower m)
    (circleAffineInverse_right hS hT hD hγ travel e m)

theorem circleAffineInverse_period
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (e : S.Space) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ m θ, a ≤ deriv (circleAffineLift travel (S.decode e) 1 m) θ)
    (m : ℕ) (θ : ℝ) :
    circleAffineInverse travel e m (θ + Real.pi) = circleAffineInverse travel e m θ + Real.pi :=
  returnChart_inverse_add_period _ _ Real.pi
    (circleAffineLift_periodic (fun j => ((hS.2.2.2.1 e).1 j).2) travel 1 m)
    (circleAffineInverse_left travel e ha hlower m)
    (circleAffineInverse_right hS hT hD hγ travel e m) θ

theorem circleAffineInverse_uniform_jets
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (e : S.Space) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ m θ, a ≤ deriv (circleAffineLift travel (S.decode e) 1 m) θ)
    (s : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m i θ, 1 ≤ i → i ≤ s →
      |iteratedDeriv i (circleAffineInverse travel e m) θ| ≤ B ^ i := by
  apply positive_jet_bounds_to_powers (circleAffineInverse travel e) _ s
  apply inverse_iteratedDeriv_uniform_bound
    (circleAffineLift travel (S.decode e) 1) (circleAffineInverse travel e)
    (circleAffineLift_contDiff (fun m => ((hS.2.2.2.1 e).1 m).1) travel 1)
    ha hlower (circleAffineInverse_left travel e ha hlower)
    (circleAffineInverse_right hS hT hD hγ travel e)
  intro n hn
  obtain ⟨B, hB, hb⟩ := circleShiftedChart_uniform_jets hS hT hD hγ travel e n
  exact ⟨B ^ n, pow_nonneg hB _, fun m θ => hb m n θ hn le_rfl⟩

def circleInverseComposeLinear
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (a : ℝ) (ha : 0 < a) (e : S.Space) :
    S.Space →ₗ[ℝ] S.Space := by
  classical
  exact if hlower : ∀ m θ, a ≤ deriv (circleAffineLift travel (S.decode e) 1 m) θ then
    circleComposeModelLinear hS (material_circle_sample_weights_pos hT hD).1
      (material_circle_sample_weights_pos hT hD).2 (circleAffineInverse travel e)
      (circleAffineInverse_contDiff hS hT hD hγ travel e ha hlower)
      (circleAffineInverse_period hS hT hD hγ travel e ha hlower)
      (circleAffineInverse_uniform_jets hS hT hD hγ travel e ha hlower)
  else 0

theorem circleInverseComposeLinear_decode
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (a : ℝ) (ha : 0 < a) (e u : S.Space)
    (hlower : ∀ m θ, a ≤ deriv (circleAffineLift travel (S.decode e) 1 m) θ) :
    S.decode (circleInverseComposeLinear hS hT hD hγ travel a ha e u) =
      fun m θ => S.decode u m (circleAffineInverse travel e m θ) := by
  classical
  have hmap : circleInverseComposeLinear hS hT hD hγ travel a ha e =
      circleComposeModelLinear hS (material_circle_sample_weights_pos hT hD).1
        (material_circle_sample_weights_pos hT hD).2 (circleAffineInverse travel e)
        (circleAffineInverse_contDiff hS hT hD hγ travel e ha hlower)
        (circleAffineInverse_period hS hT hD hγ travel e ha hlower)
        (circleAffineInverse_uniform_jets hS hT hD hγ travel e ha hlower) :=
    dif_pos hlower
  have hdecode := circleComposeModelLinear_decode (T := T) (γ := γ) (S := S)
    hS (material_circle_sample_weights_pos hT hD).1
    (material_circle_sample_weights_pos hT hD).2 (circleAffineInverse travel e)
    (circleAffineInverse_contDiff hS hT hD hγ travel e ha hlower)
    (circleAffineInverse_period hS hT hD hγ travel e ha hlower)
    (circleAffineInverse_uniform_jets hS hT hD hγ travel e ha hlower) u
  exact (congrArg (fun L : S.Space →ₗ[ℝ] S.Space => S.decode (L u)) hmap).trans hdecode

private theorem circleShiftedChartCompose_decode_at
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (e u : S.Space) (m : ℕ) (θ : ℝ) :
    S.decode (circleShiftedChartComposeContinuousLinear hS hT hD hγ travel e u) m θ =
      S.decode u m (circleAffineLift travel (S.decode e) 1 m θ) := by
  have hmap : circleShiftedChartComposeContinuousLinear hS hT hD hγ travel e u =
      circleShiftedChartComposeLinear hS hT hD hγ travel e u :=
    circleShiftedChartComposeContinuousLinear_apply (D := D) (T := T) (γ := γ) (S := S)
      hS hT hD hγ travel e u
  have hdecode : S.decode (circleShiftedChartComposeLinear hS hT hD hγ travel e u) m θ =
      S.decode u m (circleAffineLift travel (S.decode e) 1 m θ) := by
    simpa only [circleAffineLift, one_mul] using
      circleShiftedChartComposeLinear_decode (D := D) (T := T) (γ := γ) (S := S)
        hS hT hD hγ travel e u m θ
  exact (congrArg (fun v : S.Space => S.decode v m θ) hmap).trans hdecode

theorem circleInverseComposeLinear_left_inverse
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (a : ℝ) (ha : 0 < a) (e u : S.Space)
    (hlower : ∀ m θ, a ≤ deriv (circleAffineLift travel (S.decode e) 1 m) θ) :
    circleInverseComposeLinear hS hT hD hγ travel a ha e
      (circleShiftedChartComposeContinuousLinear hS hT hD hγ travel e u) = u := by
  apply hS.2.2.2.2.2.1
  funext m θ
  have hi := congrFun (congrFun
    (circleInverseComposeLinear_decode (D := D) (T := T) (γ := γ) (S := S)
      hS hT hD hγ travel a ha e
      (circleShiftedChartComposeContinuousLinear hS hT hD hγ travel e u) hlower) m) θ
  calc
    _ = S.decode (circleShiftedChartComposeContinuousLinear hS hT hD hγ travel e u)
        m (circleAffineInverse travel e m θ) := hi
    _ = S.decode u m (circleAffineLift travel (S.decode e) 1 m
        (circleAffineInverse travel e m θ)) :=
      circleShiftedChartCompose_decode_at hS hT hD hγ travel e u m
        (circleAffineInverse travel e m θ)
    _ = S.decode u m θ := congrArg (fun t : ℝ => S.decode u m t)
      (circleAffineInverse_right hS hT hD hγ travel e m θ)

theorem circleInverseComposeLinear_right_inverse
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (a : ℝ) (ha : 0 < a) (e u : S.Space)
    (hlower : ∀ m θ, a ≤ deriv (circleAffineLift travel (S.decode e) 1 m) θ) :
    circleShiftedChartComposeContinuousLinear hS hT hD hγ travel e
      (circleInverseComposeLinear hS hT hD hγ travel a ha e u) = u := by
  apply hS.2.2.2.2.2.1
  funext m θ
  have hi := congrFun (congrFun
    (circleInverseComposeLinear_decode (D := D) (T := T) (γ := γ) (S := S)
      hS hT hD hγ travel a ha e u hlower) m)
      (circleAffineLift travel (S.decode e) 1 m θ)
  calc
    _ = S.decode (circleInverseComposeLinear hS hT hD hγ travel a ha e u) m
        (circleAffineLift travel (S.decode e) 1 m θ) :=
      circleShiftedChartCompose_decode_at hS hT hD hγ travel e
        (circleInverseComposeLinear hS hT hD hγ travel a ha e u) m θ
    _ = S.decode u m (circleAffineInverse travel e m
        (circleAffineLift travel (S.decode e) 1 m θ)) := hi
    _ = S.decode u m θ := congrArg (fun t : ℝ => S.decode u m t)
      (circleAffineInverse_left travel e ha hlower m θ)

end ContinuousFlexibility.Statements
