module

public import ContinuousFlexibility.Analysis.SpacesTraceGeometry
public import ContinuousFlexibility.Scalar.WeightedMaterialScale

/-! # Every inverse endpoint-distance power has subpower material growth -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

theorem n08_materialEll_le_distance {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ r ∈ Ioo D.a D.b, T.ell r ≤ K * endpointDistance D r := by
  obtain ⟨L, hL, hLb⟩ := spaces_material_ell_bounded hT
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hend, _⟩ := hdata
  obtain ⟨d0, δ, _, hδ, _, hleft, hright⟩ := hend
  let K : ℝ := max 1 (L / δ)
  have hK : 1 ≤ K := le_max_left _ _
  have hLK : L ≤ K * δ := (div_le_iff₀ hδ).mp (le_max_right _ _)
  refine ⟨K, hK, fun r hr => ?_⟩
  have hd : 0 < endpointDistance D r := lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)
  have hendBound {d x : ℝ} (hd : 0 < d) (hx : 0 ≤ x) : d / (1 + x) ≤ d := by
    apply (div_le_iff₀ (by linarith : 0 < 1 + x)).mpr
    nlinarith
  by_cases hn : endpointDistance D r < δ
  · have hell : T.ell r ≤ endpointDistance D r := by
      by_cases hside : r - D.a ≤ D.b - r
      · have hd' : endpointDistance D r = r - D.a := min_eq_left hside
        rw [hd'] at hn ⊢
        rw [(hleft r ⟨hr.1, by linarith only [hn]⟩).1]
        exact hendBound (sub_pos.mpr hr.1) (Real.sqrt_nonneg _)
      · have hd' : endpointDistance D r = D.b - r := min_eq_right (le_of_not_ge hside)
        rw [hd'] at hn ⊢
        rw [(hright r ⟨by linarith only [hn], hr.2⟩).1]
        exact hendBound (sub_pos.mpr hr.2) (Real.sqrt_nonneg _)
    exact hell.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hK hd.le)
  · exact (hLb r hr).trans (hLK.trans
      (mul_le_mul_of_nonneg_left (le_of_not_gt hn) (zero_le_one.trans hK)))

theorem n08_distance_inverse_le_E0 {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ r ∈ Ioo D.a D.b,
      (endpointDistance D r)⁻¹ ≤ C * T.E0 r ^ A := by
  obtain ⟨K, hK, hKb⟩ := n08_materialEll_le_distance hT
  obtain ⟨C, A, hC, hA, hCb⟩ := materialEll_inv_le_E0 hT
  refine ⟨K * C, A, mul_nonneg (zero_le_one.trans hK) hC, hA, fun r hr => ?_⟩
  have hd : 0 < endpointDistance D r := lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)
  have hell : 0 < T.ell r := (hT.2.1 r hr).1
  have hi : (endpointDistance D r)⁻¹ ≤ K * (T.ell r)⁻¹ := by
    have h : (1 : ℝ) / endpointDistance D r ≤ K / T.ell r :=
      (div_le_div_iff₀ hd hell).mpr (by simpa only [one_mul] using hKb r hr)
    simpa only [one_div, div_eq_mul_inv, one_mul] using h
  exact hi.trans ((mul_le_mul_of_nonneg_left (hCb r hr) (zero_le_one.trans hK)).trans_eq (by ring))

theorem n08_distance_power_le_subpowerM {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Ioo D.a D.b,
      (endpointDistance D r)⁻¹ ^ k ≤ K * T.M r ^ ε := by
  obtain ⟨C, A, hC, _, hCb⟩ := n08_distance_inverse_le_E0 hT
  obtain ⟨L, hL, hLb⟩ := materialE0_rpow_le_subpowerM hT (A * (k : ℝ)) hε
  refine ⟨C ^ k * L, mul_nonneg (pow_nonneg hC _) hL.le, fun r hr => ?_⟩
  have hd : 0 < endpointDistance D r := lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)
  have hE : 0 < T.E0 r := (hT.2.1 r hr).2.2.1
  calc
    _ ≤ (C * T.E0 r ^ A) ^ k := pow_le_pow_left₀ (inv_nonneg.mpr hd.le) (hCb r hr) k
    _ = C ^ k * T.E0 r ^ (A * (k : ℝ)) := by
      rw [mul_pow, ← Real.rpow_natCast (T.E0 r ^ A), ← Real.rpow_mul hE.le]
    _ ≤ C ^ k * (L * T.M r ^ ε) := mul_le_mul_of_nonneg_left (hLb r hr) (pow_nonneg hC _)
    _ = _ := by ring

end ContinuousFlexibility.Statements
