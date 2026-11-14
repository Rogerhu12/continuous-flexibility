module

public import ContinuousFlexibility.Analysis.N08MaterialEnvelopeComparison
public import ContinuousFlexibility.Analysis.N08SamplePointWeights

/-!
# Envelope comparison across a bounded change of control labels

The assigned control label need not locate the actual negative component.
The height comparison is first moved across the bounded label displacement,
then the endpoint envelope comparison transfers every fixed material loss
to the actual physical cell.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

/-- Both cell indices may vary independently. On the compact middle,
the global positive height bound controls every sample at once. -/
theorem n08_twoSample_point_height_bound
    {D : ReferenceData} {T : MaterialData} (hD : IsAccumulatingProfile D)
    (hT : IsMaterialData D T) {B : ℝ} (hB : 0 ≤ B) {γ : ℝ} (hγ : 0 < γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ i j r, r ∈ D.cells j →
      |(D.cellIndex i : ℝ) - D.cellIndex j| ≤ B →
      T.H (T.sample i) ^ γ ≤ K * T.H r ^ (γ / 16) := by
  obtain ⟨δ, K, hδ, hK, hnear⟩ := materialSample_endpoint_weight_bound hT hD hγ 0 hB
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hdecay, _⟩ := hdata
  obtain ⟨H, hH, hHb, _⟩ := hdecay 0 γ hγ
  have hheight (r : ℝ) (hr : r ∈ Ioo D.a D.b) : T.H r ^ γ ≤ H := by
    simpa only [Real.rpow_zero, mul_one] using hHb r hr
  let middle : Set ℝ := Icc (D.a + δ) (D.b - δ)
  have hmiddle : middle ⊆ Ioo D.a D.b := by
    intro r hr
    exact ⟨by linarith only [hr.1, hδ], by linarith only [hr.2, hδ]⟩
  have hc : ContinuousOn (fun r => T.H r ^ (-(γ / 16))) middle :=
    (((hT.1 T.H (by simp)).continuousOn).rpow_const
      (fun r hr => Or.inl (hT.2.1 r hr).2.1.ne')).mono hmiddle
  obtain ⟨A, hA⟩ := (isCompact_Icc : IsCompact middle).bddAbove_image hc
  obtain ⟨C, hC⟩ := hD
  refine ⟨max K (H * max A 1), hK.trans_le (le_max_left _ _), fun i j r hr hj => ?_⟩
  have hrCore : r ∈ Ioo D.a D.b := hC.2.1.2.2.2.1 j hr
  have hp : 0 < T.H r := (hT.2.1 r hrCore).2.1
  have hiCore := materialSample_mem_radialCore hT hC.2.1 i
  have hip : 0 < T.H (T.sample i) := (hT.2.1 _ hiCore).2.1
  by_cases hn : endpointDistance D r < δ
  · have hb : T.H (T.sample i) ^ γ ≤ K * T.H r ^ (γ / 16) := by
      simpa only [Real.rpow_zero, mul_one] using hnear i j r hrCore hr hj hn
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hp.le _))
  · have hd : δ ≤ min (r - D.a) (D.b - r) := le_of_not_gt hn
    have hrm : r ∈ middle :=
      ⟨by linarith only [hd.trans (min_le_left _ _)],
        by linarith only [hd.trans (min_le_right _ _)]⟩
    have hrad : T.H r ^ (-(γ / 16)) ≤ max A 1 :=
      (hA ⟨r, hrm, rfl⟩).trans (le_max_left _ _)
    calc
      T.H (T.sample i) ^ γ =
          (T.H (T.sample i) ^ γ * T.H r ^ (-(γ / 16))) * T.H r ^ (γ / 16) := by
        rw [mul_assoc, ← Real.rpow_add hp, neg_add_cancel, Real.rpow_zero, mul_one]
      _ ≤ (H * max A 1) * T.H r ^ (γ / 16) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (hheight _ hiCore) hrad (Real.rpow_nonneg hp.le _) hH.le)
          (Real.rpow_nonneg hp.le _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hp.le _)

theorem n08_shiftedSample_point_height_bound
    {D : ReferenceData} {T : MaterialData} (hD : IsAccumulatingProfile D)
    (hT : IsMaterialData D T) {σ : ℕ → ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hindex : ∀ m, |(D.cellIndex (σ m) : ℝ) - D.cellIndex m| ≤ B)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m r, r ∈ D.cells m →
      T.H (T.sample (σ m)) ^ γ ≤ K * T.H r ^ (γ / 16) := by
  obtain ⟨δ, K, hδ, hK, hb⟩ := materialSample_endpoint_weight_bound hT hD hγ 0 hB
  obtain ⟨C, hC⟩ := hD
  have hsample (m : ℕ) :=
    (hT.2.1 (T.sample m) (materialSample_mem_radialCore hT hC.2.1 m)).2.1
  apply n08_referenceCell_near_bound_global ⟨C, hC⟩ hT
    (fun m => Real.rpow_nonneg (hsample (σ m)).le γ) hδ hK
  intro m r hr hn
  simpa only [Real.rpow_zero, mul_one] using
    hb (σ m) m r (hC.2.1.2.2.2.1 m hr) hr (hindex m) hn

theorem n08_sample_envelope_transfer
    {D : ReferenceData} {T : MaterialData} (hD : IsAccumulatingProfile D)
    (hT : IsMaterialData D T) (physical label : ℕ → ℕ)
    {B : ℝ} (hB : 0 ≤ B)
    (hindex : ∀ m, |(D.cellIndex (label m) : ℝ) - D.cellIndex m| ≤ B)
    {a b C : ℝ} (ha : 0 < a) (hb : 0 < b) (hC : 0 < C)
    (hcompare : ∀ m, T.H (T.sample (physical m)) ^ a ≤
      C * T.H (T.sample (label m)) ^ b) (A : ℝ) :
    ∃ K N : ℝ, 0 < K ∧ 0 ≤ N ∧ ∀ m,
      T.M (T.sample m) ^ A ≤ K * T.M (T.sample (physical m)) ^ N := by
  obtain ⟨L, hL, hLb⟩ := n08_shiftedSample_point_height_bound hD hT hB hindex hb
  obtain ⟨K, N, hK, hN, hKb⟩ := n08_material_envelope_power_comparison hT ha
    (div_pos hb (by norm_num : (0 : ℝ) < 16)) (mul_pos hC hL) A
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsamp, _⟩ := hdata
  obtain ⟨C0, hC0⟩ := hD
  have hcore (m : ℕ) := materialSample_mem_radialCore hT hC0.2.1 m
  refine ⟨K, N, hK, hN, fun m => ?_⟩
  apply hKb (T.sample (physical m)) (T.sample m) (hcore _) (hcore _)
  exact (hcompare m).trans ((mul_le_mul_of_nonneg_left
    (hLb m (T.sample m) (hsamp m)) hC.le).trans_eq (by ring))

end ContinuousFlexibility.Statements
