import ContinuousFlexibility.Statements.Analysis

/-!
# Sampled material weights and coefficient absorption

The sample points belong to the actual physical interval. The material
envelope bounds every coefficient power, and every positive height power
absorbs that envelope, uniformly over the interval and all its samples.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem materialSample_mem_interval {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (m : ℕ) :
    T.sample m ∈ Ioo D.a D.b := by
  obtain ⟨_, hbounds⟩ := hD
  have hsample : ∀ m, T.sample m ∈ D.cells m := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs, _⟩ := hT
    exact hs
  exact hbounds.2.1.2.2.2.1 m (hsample m)

theorem materialSample_factor_nonneg {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {B : ℝ} (hB : 0 ≤ B) (m : ℕ) :
    0 ≤ B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B := by
  have hp := hT.2.1 _ (materialSample_mem_interval hD hT m)
  exact mul_nonneg (mul_nonneg hB (Real.rpow_nonneg hp.2.1.le _))
    (Real.rpow_nonneg hp.2.2.1.le _)

/-- Every positive material height power absorbs every coefficient power,
uniformly over the whole physical interval. -/
theorem material_height_coefficient_power_bounded
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (A : ℝ) {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ r ∈ Ioo D.a D.b, T.H r ^ β * T.E0 r ^ A ≤ C := by
  obtain ⟨_, hpositive, _, _, _, _, _, _, _, _, _, hE, hH, _⟩ := hT
  obtain ⟨CE, hCE, hEb⟩ := hE A
  obtain ⟨CH, hCH, hHb, _⟩ := hH 1 β hβ
  refine ⟨CE * CH, mul_pos hCE hCH, ?_⟩
  intro r hr
  have hHpos : 0 ≤ T.H r ^ β := Real.rpow_nonneg (hpositive r hr).2.1.le β
  have hbase : T.H r ^ β * T.M r ≤ CH := by
    simpa only [Real.rpow_one] using hHb r hr
  calc
    T.H r ^ β * T.E0 r ^ A ≤ T.H r ^ β * (CE * T.M r) :=
      mul_le_mul_of_nonneg_left (hEb r hr) hHpos
    _ = CE * (T.H r ^ β * T.M r) := by ring
    _ ≤ CE * CH := mul_le_mul_of_nonneg_left hbase hCE.le

/-- The same absorption bound applies to any fixed assignment of physical
sample cells. No relation between coordinates and cell labels is asserted. -/
theorem material_sample_height_coefficient_power_bounded
    {D : ReferenceData} {T : MaterialData} (hD : IsAccumulatingProfile D)
    (hT : IsMaterialData D T) (κ : ℕ → ℕ) (A : ℝ) {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ m, T.H (T.sample (κ m)) ^ β * T.E0 (T.sample (κ m)) ^ A ≤ C := by
  obtain ⟨C, hC, hbound⟩ := material_height_coefficient_power_bounded hT A hβ
  exact ⟨C, hC, fun m => hbound _ (materialSample_mem_interval hD hT (κ m))⟩

end ContinuousFlexibility.Analysis
