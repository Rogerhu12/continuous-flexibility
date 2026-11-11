import ContinuousFlexibility.Analysis.MaterialSampleIndexModels

/-!
# Global comparison with the actual endpoint models

The finitely many samples outside the exact endpoint formulas are covered
by positive constants. The same endpoint coordinate then controls all
three weights at every sample, with one uniform coordinate-index error.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology

theorem exists_one_le_twoSided_mul_bound_of_cofinite
    {f g : ℕ → ℝ} (hf : ∀ m, 0 < f m) (hg : ∀ m, 0 < g m)
    (heq : ∀ᶠ m in cofinite, f m = g m) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ m, f m ≤ K * g m ∧ g m ≤ K * f m := by
  have hfg : ∀ᶠ m in cofinite, f m ≤ 1 * g m := by
    filter_upwards [heq] with m hm
    exact hm.le.trans_eq (one_mul _).symm
  have hgf : ∀ᶠ m in cofinite, g m ≤ 1 * f m := by
    filter_upwards [heq] with m hm
    exact hm.symm.le.trans_eq (one_mul _).symm
  obtain ⟨Kf, _, hKf⟩ := exists_pos_mul_bound_of_cofinite hg hfg
  obtain ⟨Kg, _, hKg⟩ := exists_pos_mul_bound_of_cofinite hf hgf
  let K := max 1 (max Kf Kg)
  refine ⟨K, le_max_left _ _, fun m => ⟨?_, ?_⟩⟩
  · exact (hKf m).trans (mul_le_mul_of_nonneg_right
      ((le_max_left Kf Kg).trans (le_max_right 1 _)) (hg m).le)
  · exact (hKg m).trans (mul_le_mul_of_nonneg_right
      ((le_max_right Kf Kg).trans (le_max_right 1 _)) (hf m).le)

theorem materialSample_global_endpoint_models
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D) :
    ∃ d0 L KH KE KM : ℝ,
      0 < d0 ∧ 0 ≤ L ∧ 1 ≤ KH ∧ 1 ≤ KE ∧ 1 ≤ KM ∧ ∀ m,
      let x := endpointX d0 (endpointDistance D (T.sample m))
      0 ≤ x ∧ |x - (D.cellIndex m : ℝ)| ≤ L ∧
        T.H (T.sample m) ≤ KH * materialH x ∧
        materialH x ≤ KH * T.H (T.sample m) ∧
        T.E0 (T.sample m) ≤ KE * materialE0 x ∧
        materialE0 x ≤ KE * T.E0 (T.sample m) ∧
        T.M (T.sample m) ≤ KM * materialM x ∧
        materialM x ≤ KM * T.M (T.sample m) := by
  obtain ⟨d0, L0, hd0, _, hmodels⟩ := materialSample_eventually_endpoint_models hT hRef
  let x (m : ℕ) := endpointX d0 (endpointDistance D (T.sample m))
  have hRef' := hRef
  obtain ⟨_, hgeom⟩ := hRef'
  have hsample (m : ℕ) : T.sample m ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hgeom.2.1 m
  have hHp (m : ℕ) : 0 < T.H (T.sample m) := (hT.2.1 _ (hsample m)).2.1
  have hEp (m : ℕ) : 0 < T.E0 (T.sample m) := (hT.2.1 _ (hsample m)).2.2.1
  have hMp (m : ℕ) : 0 < T.M (T.sample m) :=
    zero_lt_one.trans_le (hT.2.1 _ (hsample m)).2.2.2
  have hHeq : ∀ᶠ m in cofinite, T.H (T.sample m) = materialH (x m) :=
    hmodels.mono (fun _ hm => hm.1)
  have hEeq : ∀ᶠ m in cofinite, T.E0 (T.sample m) = materialE0 (x m) :=
    hmodels.mono (fun _ hm => hm.2.1)
  have hMeq : ∀ᶠ m in cofinite, T.M (T.sample m) = materialM (x m) :=
    hmodels.mono (fun _ hm => hm.2.2.1)
  obtain ⟨KH, hKH, hH⟩ := exists_one_le_twoSided_mul_bound_of_cofinite hHp
    (fun m => materialH_pos (x m)) hHeq
  obtain ⟨KE, hKE, hE⟩ := exists_one_le_twoSided_mul_bound_of_cofinite hEp
    (fun m => materialE0_pos (x m)) hEeq
  obtain ⟨KM, hKM, hM⟩ := exists_one_le_twoSided_mul_bound_of_cofinite hMp
    (fun m => materialM_pos (x m)) hMeq
  have hdist : ∀ᶠ m in cofinite,
      |x m - (D.cellIndex m : ℝ)| ≤ L0 * (1 : ℝ) := by
    filter_upwards [hmodels] with m hm
    simpa only [mul_one] using hm.2.2.2
  obtain ⟨L, hL, hbound⟩ := exists_pos_mul_bound_of_cofinite
    (fun _ : ℕ => (zero_lt_one : (0 : ℝ) < 1)) hdist
  refine ⟨d0, L, KH, KE, KM, hd0, hL.le, hKH, hKE, hKM, fun m => ?_⟩
  exact ⟨Real.sqrt_nonneg _, by simpa only [mul_one] using hbound m,
    (hH m).1, (hH m).2, (hE m).1, (hE m).2, (hM m).1, (hM m).2⟩

theorem abs_sampleCoordinate_sub_le_of_index_sub_le
    {D : ReferenceData} {x : ℕ → ℝ} {L B : ℝ}
    (hx : ∀ m, |x m - (D.cellIndex m : ℝ)| ≤ L)
    {m n : ℕ} (hmn : |(D.cellIndex m : ℝ) - D.cellIndex n| ≤ B) :
    |x m - x n| ≤ 2 * L + B := by
  have hxn : |(D.cellIndex n : ℝ) - x n| ≤ L := by
    rw [abs_sub_comm]
    exact hx n
  calc
    _ ≤ |x m - (D.cellIndex m : ℝ)| + |(D.cellIndex m : ℝ) - x n| := abs_sub_le _ _ _
    _ ≤ L + (|(D.cellIndex m : ℝ) - D.cellIndex n| +
        |(D.cellIndex n : ℝ) - x n|) := add_le_add (hx m) (abs_sub_le _ _ _)
    _ ≤ L + (B + L) := add_le_add le_rfl (add_le_add hmn hxn)
    _ = _ := by ring

end ContinuousFlexibility.Statements
