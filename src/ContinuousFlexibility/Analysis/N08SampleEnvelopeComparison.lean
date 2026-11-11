import ContinuousFlexibility.Analysis.N08MaterialEnvelopeComparison
import ContinuousFlexibility.Analysis.N08SamplePointWeights

/-!
# Envelope comparison across a bounded change of control labels

The assigned control label need not locate the actual negative component.
The height comparison is first moved across the bounded label displacement,
then the endpoint envelope comparison transfers every fixed material loss
to the actual physical cell.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

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
