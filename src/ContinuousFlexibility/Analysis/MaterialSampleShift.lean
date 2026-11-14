module

public import ContinuousFlexibility.Analysis.MaterialSampleGlobalModels
public import ContinuousFlexibility.Analysis.MaterialSampleRadialLoss
public import ContinuousFlexibility.Analysis.MaterialWeightShift

/-!
# Precise sample-weight comparison under bounded index displacement

Height exponents are preserved exactly. A bounded sample-index shift
costs a fixed `E0` power for height weights and an arbitrarily small extra
order for each specified material power.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

theorem materialE0_one_le {x : ℝ} (hx : 0 ≤ x) : 1 ≤ materialE0 x := by
  have hlog : 0 ≤ materialLogFactor x := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ Real.exp 1 + x by linarith only [hx])
    rw [Real.log_exp] at h
    exact zero_le_one.trans h
  apply Real.one_le_exp_iff.mpr
  change 0 ≤ 1 + x ^ (5 / 2 : ℝ) * materialLogFactor x
  positivity

theorem materialE0_rpow_oneSided_shift
    {R L : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L) :
    ∃ K P : ℝ, 0 < K ∧ 0 ≤ P ∧ ∀ x y : ℝ,
      0 ≤ x → 0 ≤ y → x ≤ y + L →
      materialE0 x ^ R ≤ K * materialE0 y ^ P := by
  let c := 1 + L
  let P := R * (c ^ (5 / 2 : ℝ) * (Real.log c + 1))
  have hc : 1 ≤ c := by dsimp only [c]; linarith only [hL]
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hlog : 0 ≤ Real.log c := Real.log_nonneg hc
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hK1 : 1 ≤ materialE0 c ^ R := Real.one_le_rpow (materialE0_one_le hc0) hR
  refine ⟨materialE0 c ^ R, P, Real.rpow_pos_of_pos (materialE0_pos c) _, hP,
    fun x y hx hy hxy => ?_⟩
  by_cases hy1 : 1 ≤ y
  · have hscale : x ≤ c * y := by
      have h := mul_le_mul_of_nonneg_left hy1 hL
      dsimp only [c]
      nlinarith only [hxy, h]
    have hb := materialE0_rpow_scale_bound hc hy hx hscale hR
    exact hb.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hK1
        (Real.rpow_nonneg (materialE0_pos y).le P))
  · have hxc : x ≤ c := by dsimp only [c]; linarith only [hxy, le_of_not_ge hy1]
    have hb := materialE0_rpow_scale_bound (C := (1 : ℝ)) (by norm_num)
      hc0 hx (by simpa only [one_mul] using hxc) hR
    have hb' : materialE0 x ^ R ≤ materialE0 c ^ R := by
      simpa only [Real.one_rpow, Real.log_one, zero_add, mul_one] using hb
    exact hb'.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (Real.one_le_rpow (materialE0_one_le hy) hP)
        (Real.rpow_nonneg (materialE0_pos c).le R))

theorem materialH_E0_rpow_bounded_shift
    (γ : ℝ) {R L : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ x y : ℝ,
      0 ≤ x → 0 ≤ y → |x - y| ≤ L →
      materialH x ^ γ * materialE0 x ^ R ≤
        K * materialH y ^ γ * materialE0 y ^ A := by
  obtain ⟨A, hA, hH⟩ := materialH_rpow_bounded_shift γ hL
  obtain ⟨K, P, hK, hP, hE⟩ := materialE0_rpow_oneSided_shift hR hL
  refine ⟨K, A + P, hK, add_nonneg hA hP, fun x y hx hy hxy => ?_⟩
  have hxyL : x ≤ y + L := by linarith only [(abs_le.mp hxy).2]
  calc
    _ ≤ (materialH y ^ γ * materialE0 y ^ A) * (K * materialE0 y ^ P) :=
      mul_le_mul (hH x y hx hy hxy) (hE x y hx hy hxyL)
        (Real.rpow_nonneg (materialE0_pos x).le R)
        (mul_nonneg (Real.rpow_nonneg (materialH_pos y).le γ)
          (Real.rpow_nonneg (materialE0_pos y).le A))
    _ = _ := by rw [Real.rpow_add (materialE0_pos y)]; ring

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

theorem materialSample_H_E0_rpow_of_index_sub_bound
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (γ : ℝ) {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ m n : ℕ,
      |(D.cellIndex m : ℝ) - D.cellIndex n| ≤ B →
      T.H (T.sample m) ^ γ * T.E0 (T.sample m) ^ R ≤
        K * T.H (T.sample n) ^ γ * T.E0 (T.sample n) ^ A := by
  obtain ⟨d0, L, KH, KE, KM, _, hL, hKH, hKE, _, hmodel⟩ :=
    materialSample_global_endpoint_models hT hRef
  let x (m : ℕ) := endpointX d0 (endpointDistance D (T.sample m))
  have hKH0 : 0 < KH := zero_lt_one.trans_le hKH
  have hKE0 : 0 < KE := zero_lt_one.trans_le hKE
  have hRef' := hRef
  obtain ⟨_, hgeom⟩ := hRef'
  have hpos (m : ℕ) := hT.2.1 _ (materialSample_mem_radialCore hT hgeom.2.1 m)
  obtain ⟨K, A, hK, hA, hshift⟩ := materialH_E0_rpow_bounded_shift γ hR
    (show 0 ≤ 2 * L + B by positivity)
  let KF := KH ^ |γ| * KE ^ R
  let KG := KH ^ |γ| * KE ^ A
  have hKF : 0 < KF := mul_pos (Real.rpow_pos_of_pos hKH0 _) (Real.rpow_pos_of_pos hKE0 _)
  have hKG : 0 < KG := mul_pos (Real.rpow_pos_of_pos hKH0 _) (Real.rpow_pos_of_pos hKE0 _)
  refine ⟨KF * K * KG, A, mul_pos (mul_pos hKF hK) hKG, hA, fun m n hmn => ?_⟩
  rcases hmodel m with ⟨hxm, hdm, hHm, hHm', hEm, hEm', hMm, hMm'⟩
  rcases hmodel n with ⟨hxn, hdn, hHn, hHn', hEn, hEn', hMn, hMn'⟩
  have hdist : |x m - x n| ≤ 2 * L + B :=
    abs_sampleCoordinate_sub_le_of_index_sub_le (fun k => (hmodel k).2.1) hmn
  have hHmγ := rpow_le_mul_rpow_of_twoSided (hpos m).2.1 (materialH_pos (x m))
    hKH0 hHm hHm' γ
  have hEmR := Real.rpow_le_rpow (hpos m).2.2.1.le hEm hR
  rw [Real.mul_rpow hKE0.le (materialE0_pos (x m)).le] at hEmR
  have hHnγ := rpow_le_mul_rpow_of_twoSided (materialH_pos (x n)) (hpos n).2.1
    hKH0 hHn' hHn γ
  have hEnA := Real.rpow_le_rpow (materialE0_pos (x n)).le hEn' hA
  rw [Real.mul_rpow hKE0.le (hpos n).2.2.1.le] at hEnA
  have hfirst : T.H (T.sample m) ^ γ * T.E0 (T.sample m) ^ R ≤
      KF * (materialH (x m) ^ γ * materialE0 (x m) ^ R) := by
    have h := mul_le_mul hHmγ hEmR (Real.rpow_nonneg (hpos m).2.2.1.le R)
      (mul_nonneg (Real.rpow_nonneg hKH0.le _) (Real.rpow_nonneg (materialH_pos (x m)).le γ))
    exact h.trans_eq (by dsimp only [KF]; ring)
  have hlast : materialH (x n) ^ γ * materialE0 (x n) ^ A ≤
      KG * (T.H (T.sample n) ^ γ * T.E0 (T.sample n) ^ A) := by
    have h := mul_le_mul hHnγ hEnA (Real.rpow_nonneg (materialE0_pos (x n)).le A)
      (mul_nonneg (Real.rpow_nonneg hKH0.le _) (Real.rpow_nonneg (hpos n).2.1.le γ))
    exact h.trans_eq (by dsimp only [KG]; ring)
  calc
    _ ≤ KF * (materialH (x m) ^ γ * materialE0 (x m) ^ R) := hfirst
    _ ≤ KF * (K * (materialH (x n) ^ γ * materialE0 (x n) ^ A)) :=
      mul_le_mul_of_nonneg_left (by simpa only [mul_assoc] using hshift (x m) (x n) hxm hxn hdist) hKF.le
    _ ≤ KF * (K * (KG * (T.H (T.sample n) ^ γ * T.E0 (T.sample n) ^ A))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlast hK.le) hKF.le
    _ = _ := by ring

theorem materialSample_M_rpow_of_index_sub_bound
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    {p σ B : ℝ} (hp : 0 ≤ p) (hσ : 0 < σ) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ m n : ℕ,
      |(D.cellIndex m : ℝ) - D.cellIndex n| ≤ B →
      T.M (T.sample m) ^ p ≤ K * T.M (T.sample n) ^ (p + σ) := by
  obtain ⟨d0, L, KH, KE, KM, _, hL, _, _, hKM, hmodel⟩ :=
    materialSample_global_endpoint_models hT hRef
  let x (m : ℕ) := endpointX d0 (endpointDistance D (T.sample m))
  have hKM0 : 0 < KM := zero_lt_one.trans_le hKM
  have hRef' := hRef
  obtain ⟨_, hgeom⟩ := hRef'
  have hpos (m : ℕ) : 0 < T.M (T.sample m) := zero_lt_one.trans_le
    (hT.2.1 _ (materialSample_mem_radialCore hT hgeom.2.1 m)).2.2.2
  obtain ⟨K, hK, hshift⟩ := materialM_rpow_bounded_shift hp hσ
    (show 0 ≤ 2 * L + B by positivity)
  refine ⟨KM ^ p * K * KM ^ (p + σ),
    mul_pos (mul_pos (Real.rpow_pos_of_pos hKM0 _) hK) (Real.rpow_pos_of_pos hKM0 _),
    fun m n hmn => ?_⟩
  have hdist : |x m - x n| ≤ 2 * L + B :=
    abs_sampleCoordinate_sub_le_of_index_sub_le (fun k => (hmodel k).2.1) hmn
  have hfirst := Real.rpow_le_rpow (hpos m).le (hmodel m).2.2.2.2.2.2.1 hp
  rw [Real.mul_rpow hKM0.le (materialM_pos (x m)).le] at hfirst
  have hlast := Real.rpow_le_rpow (materialM_pos (x n)).le
    (hmodel n).2.2.2.2.2.2.2 (add_nonneg hp hσ.le)
  rw [Real.mul_rpow hKM0.le (hpos n).le] at hlast
  calc
    _ ≤ KM ^ p * materialM (x m) ^ p := hfirst
    _ ≤ KM ^ p * (K * materialM (x n) ^ (p + σ)) :=
      mul_le_mul_of_nonneg_left (hshift (x m) (x n) (hmodel m).1 (hmodel n).1 hdist)
        (Real.rpow_nonneg hKM0.le _)
    _ ≤ KM ^ p * (K * (KM ^ (p + σ) * T.M (T.sample n) ^ (p + σ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlast hK.le)
        (Real.rpow_nonneg hKM0.le _)
    _ = _ := by ring

end ContinuousFlexibility.Statements
