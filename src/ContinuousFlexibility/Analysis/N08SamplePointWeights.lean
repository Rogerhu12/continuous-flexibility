import ContinuousFlexibility.Scalar.WeightedReferenceBounds

/-!
# Moving a sample estimate to the actual radial point

The endpoint comparison is made inside the actual reference cell. Compact
local finiteness supplies one constant on the remaining middle interval.
Control interval placement is not involved.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

theorem n08_referenceCell_near_bound_global
    {D : ReferenceData} {T : MaterialData} (hD : IsAccumulatingProfile D)
    (hT : IsMaterialData D T) {weight : ℕ → ℝ} {γ δ K : ℝ}
    (hweight : ∀ m, 0 ≤ weight m) (hδ : 0 < δ) (hK : 0 < K)
    (hnear : ∀ m r, r ∈ D.cells m → endpointDistance D r < δ →
      weight m ≤ K * T.H r ^ γ) :
    ∃ L : ℝ, 0 < L ∧ ∀ m r, r ∈ D.cells m → weight m ≤ L * T.H r ^ γ := by
  obtain ⟨B, hB⟩ := hD
  let middle : Set ℝ := Icc (D.a + δ) (D.b - δ)
  have hmiddle : middle ⊆ Ioo D.a D.b := by
    intro r hr
    exact ⟨by linarith only [hr.1, hδ], by linarith only [hr.2, hδ]⟩
  have hfinite : {m | (D.cells m ∩ middle).Nonempty}.Finite :=
    hB.2.2.2.2.2.1 middle isCompact_Icc hmiddle
  obtain ⟨R, hR⟩ := (hfinite.image weight).bddAbove
  have hc : ContinuousOn (fun r => T.H r ^ (-γ)) middle :=
    (((hT.1 T.H (by simp)).continuousOn).rpow_const
      (fun r hr => Or.inl (hT.2.1 r hr).2.1.ne')).mono hmiddle
  obtain ⟨A, hA⟩ := (isCompact_Icc : IsCompact middle).bddAbove_image hc
  refine ⟨max K (max R 0 * max A 0), hK.trans_le (le_max_left _ _), ?_⟩
  intro m r hrm
  have hr : r ∈ Ioo D.a D.b := hB.2.1.2.2.2.1 m hrm
  have hp : 0 < T.H r := (hT.2.1 r hr).2.1
  by_cases hn : endpointDistance D r < δ
  · exact (hnear m r hrm hn).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_pos_of_pos hp _).le)
  · have hd : δ ≤ min (r - D.a) (D.b - r) := le_of_not_gt hn
    have hrmid : r ∈ middle :=
      ⟨by linarith only [hd.trans (min_le_left _ _)],
        by linarith only [hd.trans (min_le_right _ _)]⟩
    have hwm : weight m ≤ max R 0 :=
      (hR ⟨m, ⟨r, hrm, hrmid⟩, rfl⟩).trans (le_max_left _ _)
    have hhm : T.H r ^ (-γ) ≤ max A 0 :=
      (hA ⟨r, hrmid, rfl⟩).trans (le_max_left _ _)
    calc
      weight m = (weight m * T.H r ^ (-γ)) * T.H r ^ γ := by
        rw [mul_assoc, ← Real.rpow_add hp, neg_add_cancel, Real.rpow_zero, mul_one]
      _ ≤ (max R 0 * max A 0) * T.H r ^ γ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hwm hhm (Real.rpow_pos_of_pos hp _).le (le_max_right _ _))
          (Real.rpow_pos_of_pos hp _).le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_pos_of_pos hp _).le

/-- Sample weights in the actual reference cell retain a positive fraction
of their height exponent at the evaluation point, uniformly over all cells. -/
theorem n08_materialSample_point_weight_bound
    {D : ReferenceData} {T : MaterialData} (hD : IsAccumulatingProfile D)
    (hT : IsMaterialData D T) {γ : ℝ} (hγ : 0 < γ) (A : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m r, r ∈ D.cells m →
      T.H (T.sample m) ^ γ * T.E0 (T.sample m) ^ A ≤ K * T.H r ^ (γ / 16) := by
  obtain ⟨δ, K, hδ, hK, hb⟩ := materialSample_endpoint_weight_bound hT hD hγ A
    (B := 0) le_rfl
  obtain ⟨B, hB⟩ := hD
  have hsample (m : ℕ) := hT.2.1 (T.sample m) (materialSample_mem_radialCore hT hB.2.1 m)
  exact n08_referenceCell_near_bound_global ⟨B, hB⟩ hT
    (fun m => mul_nonneg (Real.rpow_nonneg (hsample m).2.1.le _)
      (Real.rpow_nonneg (hsample m).2.2.1.le _)) hδ hK
    (fun m r hrm hn => hb m m r (hB.2.1.2.2.2.1 m hrm) hrm
      (by rw [sub_self, abs_zero]) hn)

end ContinuousFlexibility.Statements
