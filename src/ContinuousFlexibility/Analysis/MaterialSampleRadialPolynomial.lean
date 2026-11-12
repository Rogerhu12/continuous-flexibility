import ContinuousFlexibility.Analysis.MaterialSampleShift
import ContinuousFlexibility.Analysis.MaterialSampleBounds

/-!
# Radial losses retain a polynomial material envelope

The comparison is uniform over the actual material cells. It stops at
`E0`, rather than replacing that power by the larger `M` envelope. This
keeps the weight required by the canonical primitive estimates visible.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

/-- A fixed discrete radial loss costs a fixed power of the actual sample
weight, uniformly over every cell. -/
theorem materialSample_radialE_power_bound
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ K P : ℝ, 0 < K ∧ 0 ≤ P ∧ ∀ m : ℕ,
      radialE (D.cellIndex m) ^ R ≤ K * T.E0 (T.sample m) ^ P := by
  obtain ⟨d0, L, KH, KE, KM, _, hL, _, hKE, _, hmodels⟩ :=
    materialSample_global_endpoint_models hT hRef
  obtain ⟨K, P, hK, hP, hshift⟩ := materialE0_rpow_oneSided_shift hR hL
  have hKEpos : 0 < KE := zero_lt_one.trans_le hKE
  refine ⟨K * KE ^ P, P, mul_pos hK (Real.rpow_pos_of_pos hKEpos _), hP, ?_⟩
  intro m
  let x := endpointX d0 (endpointDistance D (T.sample m))
  rcases hmodels m with ⟨hx, hdist, _hH, _hH', _hE, hE', _hM, _hM'⟩
  have hn : (D.cellIndex m : ℝ) ≤ x + L := by
    have hd := (abs_le.mp hdist).1
    change -L ≤ x - (D.cellIndex m : ℝ) at hd
    linarith only [hd]
  have hsample := materialSample_mem_interval hRef hT m
  have hEpos : 0 < T.E0 (T.sample m) := (hT.2.1 _ hsample).2.2.1
  have hpower : materialE0 x ^ P ≤ KE ^ P * T.E0 (T.sample m) ^ P := by
    have h := Real.rpow_le_rpow (materialE0_pos x).le hE' hP
    simpa only [Real.mul_rpow hKEpos.le hEpos.le] using h
  calc
    radialE (D.cellIndex m) ^ R ≤ materialE0 (D.cellIndex m : ℝ) ^ R :=
      radialE_rpow_le_materialE0_natCast _ hR
    _ ≤ K * materialE0 x ^ P :=
      hshift (D.cellIndex m : ℝ) x (Nat.cast_nonneg _) hx hn
    _ ≤ K * (KE ^ P * T.E0 (T.sample m) ^ P) :=
      mul_le_mul_of_nonneg_left hpower hK.le
    _ = (K * KE ^ P) * T.E0 (T.sample m) ^ P := by ring

/-- Multiplying an N01 material factor by a fixed radial loss preserves
its height power exactly; only the coefficient exponent increases. -/
theorem materialSample_height_E0_radialE_power_bound
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (γ : ℝ) {B R : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∃ K P : ℝ, 0 < K ∧ 0 ≤ P ∧ ∀ m : ℕ,
      T.H (T.sample m) ^ γ * T.E0 (T.sample m) ^ B *
        radialE (D.cellIndex m) ^ R ≤
          K * T.H (T.sample m) ^ γ * T.E0 (T.sample m) ^ P := by
  obtain ⟨K, P, hK, hP, hbound⟩ := materialSample_radialE_power_bound hT hRef hR
  refine ⟨K, B + P, hK, add_nonneg hB hP, ?_⟩
  intro m
  have hpositive := hT.2.1 _ (materialSample_mem_interval hRef hT m)
  have hfactor : 0 ≤ T.H (T.sample m) ^ γ * T.E0 (T.sample m) ^ B :=
    mul_nonneg (Real.rpow_nonneg hpositive.2.1.le _)
      (Real.rpow_nonneg hpositive.2.2.1.le _)
  calc
    _ ≤ (T.H (T.sample m) ^ γ * T.E0 (T.sample m) ^ B) *
        (K * T.E0 (T.sample m) ^ P) :=
      mul_le_mul_of_nonneg_left (hbound m) hfactor
    _ = _ := by rw [Real.rpow_add hpositive.2.2.1]; ring

end ContinuousFlexibility.Statements
