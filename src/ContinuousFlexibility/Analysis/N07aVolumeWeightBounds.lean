import ContinuousFlexibility.Analysis.N07aVolumeCell
import ContinuousFlexibility.Analysis.N07aModeBudgetMaterial

/-! Exact volume weights in the relative-source block estimate. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S} {V : VolumeModelData S K}

theorem n07aVolume_forget_norm_le
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) {γ t : ℝ} {s : ℕ}
    (W : V.level γ t s) (m : ℕ) :
    ‖V.forget γ t s W m‖ ≤ n07aVolumeWeight T K γ t m * ‖W.val m‖ := by
  rw [n07aVolume_forget_apply hV, norm_smul, Real.norm_eq_abs,
    abs_of_pos (n07aVolumeWeight_pos hD hT γ t m)]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le (W.val m) 0)
    (n07aVolumeWeight_pos hD hT γ t m).le

theorem n07aVolumeWeight_antitone
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (γ : ℝ) {r t : ℝ} (hrt : r ≤ t) (m : ℕ) :
    n07aVolumeWeight T K γ t m ≤ n07aVolumeWeight T K γ r m := by
  have hm := materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m)
  have hM := (hT.2.1 _ hm).2.2.2
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hM (neg_le_neg hrt))
    (Real.rpow_pos_of_pos (hT.2.1 _ hm).2.1 γ).le

theorem n07aVolumeWeight_relative_gain
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (γ t r : ℝ) (m : ℕ) :
    (n07aVolumeWeight T K γ t m)⁻¹ *
        T.H (T.sample (K.cell m)) ^ γ * n07aVolumeWeight T K γ r m =
      T.H (T.sample (K.cell m)) ^ γ * T.M (T.sample (K.cell m)) ^ (t - r) := by
  have hm := materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m)
  have hM : 0 < T.M (T.sample (K.cell m)) :=
    zero_lt_one.trans_le (hT.2.1 _ hm).2.2.2
  have hH : 0 < T.H (T.sample (K.cell m)) := (hT.2.1 _ hm).2.1
  simp only [n07aVolumeWeight, mul_inv_rev, Real.rpow_neg hM.le,
    inv_inv, Real.rpow_sub hM]
  have hpow : T.H (T.sample (K.cell m)) ^ γ ≠ 0 := (Real.rpow_pos_of_pos hH γ).ne'
  field_simp

theorem N07aSampleSubpower.volume_gain_absorption
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {e : ℕ → ℝ} (he : N07aSampleSubpower T K e) {γ : ℝ} (hγ : 0 < γ)
    (t r : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ m,
      (n07aVolumeWeight T K γ t m)⁻¹ * T.H (T.sample (K.cell m)) ^ γ *
        n07aVolumeWeight T K γ r m * |e m| ≤ A := by
  obtain ⟨A, hA, hb⟩ := he.weighted_height_absorption hD hT hγ (t - r)
  refine ⟨A, hA, fun m => ?_⟩
  rw [n07aVolumeWeight_relative_gain hD hT]
  exact hb m

end ContinuousFlexibility.Analysis
