import ContinuousFlexibility.Analysis.N08CellLayerTest
import ContinuousFlexibility.Analysis.N08SampleEnvelopeComparison
import ContinuousFlexibility.Analysis.MaterialEndpointDecay

/-!
# Material weights on the actual endpoint band

Every cell meeting the band has a nearby reference index. Existing sample
comparison therefore applies on the whole support of the test, although
the support need not lie in its original cell. The inverse layer width
costs only two powers of the actual endpoint distance.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

def n08CellLayerBand (D : ReferenceData) (A : ℝ) (m : ℕ) : Set ℝ :=
  Analysis.intervalEndpointLayer D.a D.b
    (n08CellLayerInner A (D.cellIndex m)) (n08CellLayerOuter A (D.cellIndex m))

theorem n08CellLayerBand_subset_profileLayer {D : ReferenceData} {A B : ℝ}
    (hA : 0 < A) (hAB : 2 * A ≤ B) (m : ℕ) :
    n08CellLayerBand D A m ⊆ Radial.profileEndpointLayer D B (D.cellIndex m) := by
  intro r hr
  have h2A : 0 < 2 * A := mul_pos (by norm_num) hA
  constructor
  · change (B⁻¹ * Real.exp (-((D.cellIndex m : ℝ) + 1) ^ 2)) / 2 ≤ _
    calc
      _ ≤ ((2 * A)⁻¹ * Real.exp (-((D.cellIndex m : ℝ) + 1) ^ 2)) / 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (inv_anti₀ h2A hAB) (Real.exp_pos _).le) (by norm_num)
      _ = n08CellLayerInner A (D.cellIndex m) / 2 := by
        dsimp only [n08CellLayerInner]
        rw [div_eq_mul_inv]
        ring
      _ ≤ _ := hr.1
  · change Analysis.intervalEndpointDistance D.a D.b r ≤
      2 * (B * Real.exp (-(D.cellIndex m : ℝ) ^ 2))
    exact hr.2.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hAB (Real.exp_pos _).le) (by norm_num))

theorem n08CellLayerBand_index_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {A : ℝ} (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i j r, r ∈ n08CellLayerBand D A i → r ∈ D.cells j →
      |(D.cellIndex i : ℝ) - D.cellIndex j| ≤ B := by
  obtain ⟨C, hC⟩ := hD
  let C' : ℕ → ℝ := fun s => max (C s) (2 * A)
  have hC' : AccumulatingProfileBounds D C' := hC.mono (fun s => le_max_left _ _)
  refine ⟨2 + Real.sqrt |Real.log (2 * C' 0)| + Real.sqrt |Real.log (C' 0)|,
    by positivity, fun i j r hri hrj => ?_⟩
  exact Radial.profileEndpointLayer_index_bound hC'
    (n08CellLayerBand_subset_profileLayer hA (le_max_right _ _) i hri) hrj

theorem n08CellLayerBand_height_bound {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {A γ : ℝ} (hA : 0 < A) (hγ : 0 < γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m r, r ∈ n08CellLayerBand D A m →
      T.H (T.sample m) ^ γ ≤ K * T.H r ^ (γ / 16) := by
  obtain ⟨B, hB, hBb⟩ := n08CellLayerBand_index_bound hD hA
  obtain ⟨K, hK, hKb⟩ := n08_twoSample_point_height_bound hD hT hB hγ
  obtain ⟨C, hC⟩ := hD
  refine ⟨K, hK, fun m r hr => ?_⟩
  have hcore : r ∈ Ioo D.a D.b :=
    Analysis.intervalEndpointLayer_subset_Ioo (n08CellLayerInner_pos hA _) hr
  obtain ⟨j, hrj⟩ := hC.2.1.exists_cell hcore
  exact hKb m j r hrj (hBb m j r hr hrj)

/-- Positive height powers absorb every fixed inverse endpoint-distance
power on both collars; compactness covers the middle. -/
theorem n08_material_height_distance_bound {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {γ : ℝ} (hγ : 0 < γ) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ r ∈ Ioo D.a D.b,
      T.H r ^ γ / endpointDistance D r ^ k ≤ K := by
  obtain ⟨δ, hδ, hnear⟩ := exists_material_endpoint_decay hT hγ zero_lt_one 0 k
  let middle : Set ℝ := Icc (D.a + δ) (D.b - δ)
  have hmiddle : middle ⊆ Ioo D.a D.b := by
    intro r hr
    exact ⟨by linarith only [hr.1, hδ], by linarith only [hr.2, hδ]⟩
  have hd (r : ℝ) (hr : r ∈ Ioo D.a D.b) : 0 < endpointDistance D r :=
    lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)
  have hH : ContinuousOn (fun r => T.H r ^ γ) (Ioo D.a D.b) :=
    (hT.1 T.H (by simp)).continuousOn.rpow_const (fun r hr => Or.inl (hT.2.1 r hr).2.1.ne')
  have hdcont : Continuous (endpointDistance D) :=
    (continuous_id.sub continuous_const).min (continuous_const.sub continuous_id)
  have hc : ContinuousOn (fun r => T.H r ^ γ / endpointDistance D r ^ k) middle :=
    (hH.div (hdcont.pow k).continuousOn (fun r hr => pow_ne_zero _ (hd r hr).ne')).mono hmiddle
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact middle).bddAbove_image hc
  refine ⟨max 1 B, zero_lt_one.trans_le (le_max_left _ _), fun r hr => ?_⟩
  by_cases hn : endpointDistance D r < δ
  · have h := hnear r hr hn
    simp only [Real.rpow_zero, mul_one] at h
    exact h.le.trans (le_max_left _ _)
  · have hdist : δ ≤ min (r - D.a) (D.b - r) := le_of_not_gt hn
    have hrm : r ∈ middle :=
      ⟨by linarith only [hdist.trans (min_le_left _ _)],
        by linarith only [hdist.trans (min_le_right _ _)]⟩
    exact (hB ⟨r, hrm, rfl⟩).trans (le_max_right _ _)

theorem n08CellLayerBand_inverseWidth_distance {D : ReferenceData} {A : ℝ}
    (hA : 0 < A) (m : ℕ) {r : ℝ} (hr : r ∈ n08CellLayerBand D A m) :
    (n08CellLayerInner A (D.cellIndex m))⁻¹ * endpointDistance D r ^ 2 ≤
      32 * A ^ 3 * Real.exp 2 := by
  let n : ℝ := D.cellIndex m
  have hcore : r ∈ Ioo D.a D.b :=
    Analysis.intervalEndpointLayer_subset_Ioo (n08CellLayerInner_pos hA _) hr
  have hd : 0 < endpointDistance D r := lt_min (sub_pos.mpr hcore.1) (sub_pos.mpr hcore.2)
  have hu : endpointDistance D r ≤ 4 * A * Real.exp (-(n ^ 2)) := by
    have h := hr.2
    change endpointDistance D r ≤ 2 * (2 * A * Real.exp (-(n ^ 2))) at h
    linarith only [h]
  have hInv : (n08CellLayerInner A (D.cellIndex m))⁻¹ = 2 * A * Real.exp ((n + 1) ^ 2) := by
    change (Real.exp (-((n + 1) ^ 2)) / (2 * A))⁻¹ = _
    rw [inv_div, Real.exp_neg, div_inv_eq_mul]
  have hE : Real.exp ((n + 1) ^ 2) * Real.exp (-(n ^ 2)) ^ 2 ≤ Real.exp 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    nlinarith only [sq_nonneg (n - 1)]
  rw [hInv]
  calc
    _ ≤ (2 * A * Real.exp ((n + 1) ^ 2)) * (4 * A * Real.exp (-(n ^ 2))) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd.le hu 2) (by positivity)
    _ = (32 * A ^ 3) * (Real.exp ((n + 1) ^ 2) * Real.exp (-(n ^ 2)) ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hE (by positivity)

theorem n08CellLayerBand_inverseWidth_power {D : ReferenceData} {A : ℝ}
    (hA : 0 < A) (m k : ℕ) {r : ℝ} (hr : r ∈ n08CellLayerBand D A m) :
    (n08CellLayerInner A (D.cellIndex m))⁻¹ ^ k ≤
      (32 * A ^ 3 * Real.exp 2) ^ k / endpointDistance D r ^ (2 * k) := by
  have hcore : r ∈ Ioo D.a D.b :=
    Analysis.intervalEndpointLayer_subset_Ioo (n08CellLayerInner_pos hA _) hr
  have hd : 0 < endpointDistance D r := lt_min (sub_pos.mpr hcore.1) (sub_pos.mpr hcore.2)
  apply (le_div_iff₀ (pow_pos hd _)).mpr
  simpa only [mul_pow, pow_mul] using
    pow_le_pow_left₀ (mul_nonneg (inv_nonneg.mpr (n08CellLayerInner_pos hA _).le)
      (sq_nonneg _)) (n08CellLayerBand_inverseWidth_distance hA m hr) k

end ContinuousFlexibility.Statements
