import ContinuousFlexibility.Analysis.N08ControlSpatialBounds

/-!
# Positive actual spatial gain for weak control profiles

Multiplying the actual-cell bound and the independent control-label bound
removes every high label order. The estimate keeps positive decay at both
the actual evaluation point and the control label.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n08_weightedControlProfile_sq_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i r, r ∈ Ioo D.a D.b →
      |iteratedDeriv s (n08WeightedControlProfile T C i) r| ^ 2 ≤
        K * T.M r * T.H r ^ (3 / 64 : ℝ) * T.H (T.sample i) ^ (3 / 16 : ℝ) := by
  obtain ⟨A, hA, hAb⟩ := n08_weightedControlProfile_point_jet_bound hT hS hN s
  obtain ⟨B, hB, hBb⟩ := n08_weightedControlProfile_label_jet_bound_global hT hN s
  have hdata := hT
  obtain ⟨_, hpos, _, _, _, _, _, _, _, _, _, _, henv, _⟩ := hdata
  obtain ⟨L, hL, hLb, _, _⟩ := henv (base + (s + loss)) (3 / 16) (by norm_num)
  refine ⟨A * B * L, mul_nonneg (mul_nonneg hA hB.le) hL.le, fun i r hr => ?_⟩
  have hi := n08_material_sample_bounds hN.1.1 hT i
  have hH : 0 < T.H r := (hpos r hr).2.1
  have hM : 0 ≤ T.M r := zero_le_one.trans (hpos r hr).2.2.2
  have hp : 0 ≤ A * T.M r * T.H r ^ (3 / 64 : ℝ) *
      T.M (T.sample i) ^ (base + (s + loss)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hA hM) (Real.rpow_pos_of_pos hH _).le)
      (pow_nonneg (zero_le_one.trans hi.2) _)
  have hsample : T.sample i ∈ Ioo D.a D.b := by
    obtain ⟨Q, hQ⟩ := hN.1.1
    exact materialSample_mem_radialCore hT hQ.2.1 i
  have hpay : T.H (T.sample i) ^ (3 / 16 : ℝ) *
      T.M (T.sample i) ^ (base + (s + loss)) ≤ L := by
    simpa only [Real.rpow_natCast] using hLb (T.sample i) hsample
  have hsplit : T.H (T.sample i) ^ (3 / 8 : ℝ) =
      T.H (T.sample i) ^ (3 / 16 : ℝ) * T.H (T.sample i) ^ (3 / 16 : ℝ) := by
    rw [← Real.rpow_add hi.1]
    norm_num
  calc
    _ = |iteratedDeriv s (n08WeightedControlProfile T C i) r| *
        |iteratedDeriv s (n08WeightedControlProfile T C i) r| := pow_two _
    _ ≤ (A * T.M r * T.H r ^ (3 / 64 : ℝ) *
          T.M (T.sample i) ^ (base + (s + loss))) *
        (B * T.H (T.sample i) ^ (3 / 8 : ℝ)) :=
      mul_le_mul (hAb i r hr) (hBb i r) (abs_nonneg _) hp
    _ = (A * B * T.M r * T.H r ^ (3 / 64 : ℝ) * T.H (T.sample i) ^ (3 / 16 : ℝ)) *
        (T.H (T.sample i) ^ (3 / 16 : ℝ) * T.M (T.sample i) ^ (base + (s + loss))) := by
      rw [hsplit]
      ring
    _ ≤ (A * B * T.M r * T.H r ^ (3 / 64 : ℝ) * T.H (T.sample i) ^ (3 / 16 : ℝ)) * L :=
      mul_le_mul_of_nonneg_left hpay
        (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hA hB.le) hM)
          (Real.rpow_pos_of_pos hH _).le) (Real.rpow_pos_of_pos hi.1 _).le)
    _ = _ := by ring

/-- Each individual weak unit control has simultaneous actual spatial and
label decay. No control-to-reference-cell placement is assumed. -/
theorem n08_weightedControlProfile_label_decay_jet_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i r, r ∈ Ioo D.a D.b →
      |iteratedDeriv s (n08WeightedControlProfile T C i) r| ≤
        K * T.H r ^ (3 / 128 : ℝ) * T.M r * T.H (T.sample i) ^ (3 / 32 : ℝ) := by
  obtain ⟨K, hK, hKb⟩ := n08_weightedControlProfile_sq_bound hT hS hN s
  refine ⟨K + 1, by positivity, fun i r hr => ?_⟩
  have hH : 0 < T.H r := (hT.2.1 r hr).2.1
  have hM : 1 ≤ T.M r := (hT.2.1 r hr).2.2.2
  have hi : 0 < T.H (T.sample i) := (n08_material_sample_bounds hN.1.1 hT i).1
  have hhp : (T.H r ^ (3 / 128 : ℝ)) ^ 2 = T.H r ^ (3 / 64 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hH.le]
    norm_num
  have hip : (T.H (T.sample i) ^ (3 / 32 : ℝ)) ^ 2 = T.H (T.sample i) ^ (3 / 16 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hi.le]
    norm_num
  have hKM : K * T.M r ≤ (K + 1) ^ 2 * (T.M r) ^ 2 := by
    have hc : K ≤ (K + 1) ^ 2 := by nlinarith only [sq_nonneg K, hK]
    have hm : T.M r ≤ (T.M r) ^ 2 := by
      simpa only [one_mul, ← pow_two] using
        mul_le_mul_of_nonneg_right hM (zero_le_one.trans hM)
    exact mul_le_mul hc hm (zero_le_one.trans hM) (sq_nonneg _)
  have hsq : |iteratedDeriv s (n08WeightedControlProfile T C i) r| ^ 2 ≤
      ((K + 1) * T.H r ^ (3 / 128 : ℝ) * T.M r * T.H (T.sample i) ^ (3 / 32 : ℝ)) ^ 2 := by
    calc
      _ ≤ K * T.M r * T.H r ^ (3 / 64 : ℝ) * T.H (T.sample i) ^ (3 / 16 : ℝ) := hKb i r hr
      _ ≤ ((K + 1) ^ 2 * (T.M r) ^ 2) * T.H r ^ (3 / 64 : ℝ) *
          T.H (T.sample i) ^ (3 / 16 : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hKM (Real.rpow_pos_of_pos hH _).le)
          (Real.rpow_pos_of_pos hi _).le
      _ = _ := by rw [mul_pow, mul_pow, mul_pow, hhp, hip]; ring
  exact (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (Real.rpow_pos_of_pos hH _).le)
      (zero_le_one.trans hM)) (Real.rpow_pos_of_pos hi _).le)).mp hsq

theorem n08_weightedControlProfile_decay_jet_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i r, r ∈ Ioo D.a D.b →
      |iteratedDeriv s (n08WeightedControlProfile T C i) r| ≤
        K * T.H r ^ (3 / 128 : ℝ) * T.M r := by
  obtain ⟨K, hK, hKb⟩ := n08_weightedControlProfile_label_decay_jet_bound hT hS hN s
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, henv, _⟩ := hdata
  obtain ⟨A, hA, hAb, _, _⟩ := henv 0 (3 / 32) (by norm_num)
  refine ⟨K * A, mul_nonneg hK hA.le, fun i r hr => ?_⟩
  have hsample : T.sample i ∈ Ioo D.a D.b := by
    obtain ⟨Q, hQ⟩ := hN.1.1
    exact materialSample_mem_radialCore hT hQ.2.1 i
  have hb : T.H (T.sample i) ^ (3 / 32 : ℝ) ≤ A := by
    simpa only [Real.rpow_zero, mul_one] using hAb (T.sample i) hsample
  have hc : 0 ≤ K * T.H r ^ (3 / 128 : ℝ) * T.M r :=
    mul_nonneg (mul_nonneg hK (Real.rpow_nonneg (hT.2.1 r hr).2.1.le _))
      (zero_le_one.trans (hT.2.1 r hr).2.2.2)
  exact (hKb i r hr).trans ((mul_le_mul_of_nonneg_left hb hc).trans_eq (by ring))

end ContinuousFlexibility.Statements
