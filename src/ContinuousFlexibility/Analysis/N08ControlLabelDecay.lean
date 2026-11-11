import ContinuousFlexibility.Analysis.N08ControlProfileModes

/-!
# Uniform decay at the control label

Bounded displacement of the two sample labels makes every positive power of
the control amplitude dominate a fixed coefficient power. This argument uses
the actual samples only and makes no claim about placement of control supports
inside reference cells.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n08_iteratedDeriv_zero_off_open_interval {a b r : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : Function.support f ⊆ Ioo a b)
    (n : ℕ) (hr : r ∉ Ioo a b) : iteratedDeriv n f r = 0 := by
  have hc : IsClosed {x : ℝ | iteratedDeriv n f x = 0} :=
    isClosed_eq (hf.continuous_iteratedDeriv n (by simp)) continuous_const
  by_cases ha : r ≤ a
  · have hzero : Iio a ⊆ {x : ℝ | iteratedDeriv n f x = 0} := by
      intro x hx
      have heq : f =ᶠ[𝓝 x] (0 : ℝ → ℝ) := by
        filter_upwards [Iio_mem_nhds hx] with y hy
        change f y = 0
        by_contra h
        exact (not_lt_of_ge (hs h).1.le) hy
      change iteratedDeriv n f x = 0
      simpa only [iteratedDeriv_const_zero] using heq.iteratedDeriv_eq n
    apply closure_minimal hzero hc
    rwa [closure_Iio]
  · have hb : b ≤ r := le_of_not_gt fun hb => hr ⟨lt_of_not_ge ha, hb⟩
    have hzero : Ioi b ⊆ {x : ℝ | iteratedDeriv n f x = 0} := by
      intro x hx
      have heq : f =ᶠ[𝓝 x] (0 : ℝ → ℝ) := by
        filter_upwards [Ioi_mem_nhds hx] with y hy
        change f y = 0
        by_contra h
        exact (not_lt_of_ge (hs h).2.le) hy
      change iteratedDeriv n f x = 0
      simpa only [iteratedDeriv_const_zero] using heq.iteratedDeriv_eq n
    apply closure_minimal hzero hc
    rwa [closure_Ioi]

theorem n08_sample_weightedCoefficient_tendsto
    {D : ReferenceData} {T : MaterialData} (hD : IsAccumulatingProfile D)
    (hT : IsMaterialData D T) {σ : ℕ → ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hindex : ∀ m, |(D.cellIndex (σ m) : ℝ) - D.cellIndex m| ≤ B)
    {γ : ℝ} (hγ : 0 < γ) (A : ℝ) :
    Tendsto (fun m => T.H (T.sample m) ^ γ * T.E0 (T.sample (σ m)) ^ A)
      cofinite (𝓝 0) := by
  obtain ⟨δ, K, hδ, hK, henv⟩ := materialSample_endpoint_weight_bound hT hD hγ A hB
  have hσ : Tendsto σ cofinite cofinite := controlCell_tendsto_cofinite hD σ hindex
  have hnear : ∀ᶠ m in cofinite, endpointDistance D (T.sample (σ m)) < δ :=
    ((materialSample_endpointDistance_tendsto_zero hT hD).comp hσ).eventually_lt_const hδ
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hdecay, _, _, hsamp, _, _⟩ := hdata
  obtain ⟨_, _, _, hleft, hright⟩ := hdecay 0 (γ / 16) (by positivity)
  have hweight : Tendsto (fun m => T.H (T.sample m) ^ (γ / 16)) cofinite (𝓝 0) := by
    apply materialSample_tendsto_zero_of_endpoint_limits hT hD
    · simpa only [Real.rpow_zero, mul_one] using hleft
    · simpa only [Real.rpow_zero, mul_one] using hright
  obtain ⟨C0, hC0⟩ := hD
  have hp (m : ℕ) := hT.2.1 (T.sample m) (materialSample_mem_radialCore hT hC0.2.1 m)
  have hnonneg (m : ℕ) : 0 ≤ T.H (T.sample m) ^ γ * T.E0 (T.sample (σ m)) ^ A :=
    mul_nonneg (Real.rpow_nonneg (hp m).2.1.le _) (Real.rpow_nonneg (hp (σ m)).2.2.1.le _)
  have hbound : ∀ᶠ m in cofinite,
      T.H (T.sample m) ^ γ * T.E0 (T.sample (σ m)) ^ A ≤
        K * T.H (T.sample (σ m)) ^ (γ / 16) := by
    filter_upwards [hnear] with m hm
    exact henv m (σ m) (T.sample (σ m))
      (materialSample_mem_radialCore hT hC0.2.1 (σ m)) (hsamp (σ m))
      ((abs_sub_comm _ _).trans_le (hindex m)) hm
  apply squeeze_zero' (Eventually.of_forall hnonneg) hbound
  simpa only [mul_zero] using (hweight.comp hσ).const_mul K

private theorem n08_cofinite_limit_bounded {f : ℕ → ℝ}
    (hf : Tendsto f cofinite (𝓝 0)) : ∃ K : ℝ, 0 < K ∧ ∀ m, f m ≤ K := by
  have he : ∀ᶠ m in cofinite, f m ≤ 1 :=
    (hf.eventually_lt_const zero_lt_one).mono (fun _ h => h.le)
  have hfinite : {m : ℕ | ¬ f m ≤ 1}.Finite := mem_cofinite.mp he
  obtain ⟨A, hA⟩ := (hfinite.image f).bddAbove
  refine ⟨max 1 A, zero_lt_one.trans_le (le_max_left _ _), fun m => ?_⟩
  by_cases hm : f m ≤ 1
  · exact hm.trans (le_max_left _ _)
  · exact (hA ⟨m, hm, rfl⟩).trans (le_max_right _ _)

theorem n08_sample_weightedCoefficient_bounded
    {D : ReferenceData} {T : MaterialData} (hD : IsAccumulatingProfile D)
    (hT : IsMaterialData D T) {σ : ℕ → ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hindex : ∀ m, |(D.cellIndex (σ m) : ℝ) - D.cellIndex m| ≤ B)
    {γ : ℝ} (hγ : 0 < γ) (A : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m,
      T.H (T.sample m) ^ γ * T.E0 (T.sample (σ m)) ^ A ≤ K :=
  n08_cofinite_limit_bounded (n08_sample_weightedCoefficient_tendsto hD hT hB hindex hγ A)

/-- Half of the original amplitude remains after paying every ordinary
control derivative. Its exponent is tied to the control label, uniformly
over the entire actual control interval. -/
theorem n08_weightedControlProfile_label_jet_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m r, r ∈ Ioo (C.left m) (C.right m) →
      |iteratedDeriv s (n08WeightedControlProfile T C m) r| ≤
        K * T.H (T.sample m) ^ (3 / 8 : ℝ) := by
  obtain ⟨B, hB, hindex⟩ := hN.2.2.2.2.1
  obtain ⟨A, hA, hj⟩ := hN.2.2.2.2.2.1 s
  obtain ⟨K, hK, hKbound⟩ := n08_sample_weightedCoefficient_bounded hN.1.1 hT
    hB.le hindex (γ := (3 / 8 : ℝ)) (by norm_num) A
  refine ⟨A * K, mul_pos hA hK, fun m r hr => ?_⟩
  have hH := (n08_material_sample_bounds hN.1.1 hT m).1
  have hpow : T.H (T.sample m) ^ (3 / 4 : ℝ) =
      T.H (T.sample m) ^ (3 / 8 : ℝ) * T.H (T.sample m) ^ (3 / 8 : ℝ) := by
    rw [← Real.rpow_add hH]
    norm_num
  change |iteratedDeriv s (fun t => T.H (T.sample m) ^ (3 / 4 : ℝ) * C.control m t) r| ≤ _
  rw [iteratedDeriv_const_mul_field, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos hH _)]
  calc
    _ ≤ T.H (T.sample m) ^ (3 / 4 : ℝ) *
        (A * T.E0 (T.sample (C.cell m)) ^ A) :=
      mul_le_mul_of_nonneg_left (hj m r hr) (Real.rpow_pos_of_pos hH _).le
    _ = A * T.H (T.sample m) ^ (3 / 8 : ℝ) *
        (T.H (T.sample m) ^ (3 / 8 : ℝ) * T.E0 (T.sample (C.cell m)) ^ A) := by
      rw [hpow]
      ring
    _ ≤ A * T.H (T.sample m) ^ (3 / 8 : ℝ) * K :=
      mul_le_mul_of_nonneg_left (hKbound m) (mul_nonneg hA.le (Real.rpow_pos_of_pos hH _).le)
    _ = _ := by ring

theorem n08_weightedControlProfile_label_jet_bound_global
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m r,
      |iteratedDeriv s (n08WeightedControlProfile T C m) r| ≤
        K * T.H (T.sample m) ^ (3 / 8 : ℝ) := by
  obtain ⟨K, hK, hKb⟩ := n08_weightedControlProfile_label_jet_bound hT hN s
  have hcontrol := hN.2.2.2.1.2.2.2.2.2.1
  refine ⟨K, hK, fun m r => ?_⟩
  by_cases hr : r ∈ Ioo (C.left m) (C.right m)
  · exact hKb m r hr
  · change |iteratedDeriv s (fun t => T.H (T.sample m) ^ (3 / 4 : ℝ) * C.control m t) r| ≤ _
    rw [iteratedDeriv_const_mul_field,
      n08_iteratedDeriv_zero_off_open_interval (hcontrol m).1 (hcontrol m).2.2 s hr,
      mul_zero, abs_zero]
    exact mul_nonneg hK.le
      (Real.rpow_nonneg (n08_material_sample_bounds hN.1.1 hT m).1.le _)

end ContinuousFlexibility.Statements
