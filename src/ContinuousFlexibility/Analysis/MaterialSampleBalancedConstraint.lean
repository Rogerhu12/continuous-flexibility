module

public import ContinuousFlexibility.Analysis.MaterialBalancedConstraint
public import ContinuousFlexibility.Analysis.MaterialSampleShift

/-!
# Fixed-order comparison of actual samples from a balanced constraint

Global comparison with the endpoint formulas transfers the scalar
balanced-height estimate to actual material samples. The return label
may first be changed by a uniformly bounded cell-index displacement.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

/-- The two fixed auxiliary losses each cost one material order. The
already present material exponent is retained without alteration. -/
theorem materialSample_radialE_E0_M_rpow_absorb
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    {R : ℝ} (hR : 0 ≤ R) (A N : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ j : ℕ,
      radialE (D.cellIndex j) ^ R * T.E0 (T.sample j) ^ A * T.M (T.sample j) ^ N ≤
        K * T.M (T.sample j) ^ (N + 2) := by
  obtain ⟨KR, hKR, hradial⟩ := materialSample_radialE_rpow_le_M_of_index_bound
    hT hRef (by norm_num : (0 : ℝ) < 1) hR
  have hdata := hT
  rcases hdata with ⟨_, hpos, _, _, _, _, _, _, _, _, _, hE, _, _, _, _, _, _⟩
  obtain ⟨KE, hKE, hEbound⟩ := hE A
  obtain ⟨_, hgeom⟩ := hRef
  refine ⟨KR * KE, mul_pos hKR hKE, fun j => ?_⟩
  have hsample := materialSample_mem_radialCore hT hgeom.2.1 j
  have hEj : 0 < T.E0 (T.sample j) := (hpos _ hsample).2.2.1
  have hMj : 0 < T.M (T.sample j) := zero_lt_one.trans_le (hpos _ hsample).2.2.2
  have hRj := hradial j (D.cellIndex j)
    (by linarith : (D.cellIndex j : ℝ) ≤ 1 * ((D.cellIndex j : ℝ) + 1))
  have hEjbound := hEbound _ hsample
  have hprod := mul_le_mul hRj hEjbound (Real.rpow_nonneg hEj.le A)
    (mul_nonneg hKR.le hMj.le)
  calc
    _ ≤ ((KR * T.M (T.sample j)) * (KE * T.M (T.sample j))) *
        T.M (T.sample j) ^ N :=
      mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg hMj.le N)
    _ = _ := by rw [Real.rpow_add hMj N 2, Real.rpow_two]; ring

theorem materialSample_M_rpow_of_balanced_height_constraint
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    {β A N K p σ : ℝ} (hβ : 0 < β) (hK : 0 < K)
    (hp : 0 ≤ p) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n : ℕ,
      1 ≤ K * T.H (T.sample m) ^ β * T.E0 (T.sample m) ^ A *
        T.H (T.sample n) ^ (-β) * T.M (T.sample n) ^ N →
      T.M (T.sample m) ^ p ≤ C * T.M (T.sample n) ^ (p + σ) := by
  obtain ⟨d0, L, KH, KE, KM, _, _, hKH, hKE, hKM, hmodel⟩ :=
    materialSample_global_endpoint_models hT hRef
  let x (m : ℕ) := endpointX d0 (endpointDistance D (T.sample m))
  have hKH0 : 0 < KH := zero_lt_one.trans_le hKH
  have hKE0 : 0 < KE := zero_lt_one.trans_le hKE
  have hKM0 : 0 < KM := zero_lt_one.trans_le hKM
  have hRef' := hRef
  obtain ⟨_, hgeom⟩ := hRef'
  have hpos (m : ℕ) := hT.2.1 _ (materialSample_mem_radialCore hT hgeom.2.1 m)
  let K0 := K * KH ^ |β| * KE ^ |A| * KH ^ |-β| * KM ^ |N|
  have hK0 : 0 < K0 := by dsimp only [K0]; positivity
  obtain ⟨C, hC, hbalanced⟩ :=
    materialM_rpow_le_of_balanced_height_constraint (A := A) (N := N) hβ hK0 hp hσ
  refine ⟨KM ^ p * C * KM ^ (p + σ),
    mul_pos (mul_pos (Real.rpow_pos_of_pos hKM0 _) hC) (Real.rpow_pos_of_pos hKM0 _),
    fun m n hraw => ?_⟩
  rcases hmodel m with ⟨hxm, hdm, hHm, hHm', hEm, hEm', hMm, hMm'⟩
  rcases hmodel n with ⟨hxn, hdn, hHn, hHn', hEn, hEn', hMn, hMn'⟩
  have hHa := rpow_le_mul_rpow_of_twoSided (hpos m).2.1 (materialH_pos (x m))
    hKH0 hHm hHm' β
  have hEa := rpow_le_mul_rpow_of_twoSided (hpos m).2.2.1 (materialE0_pos (x m))
    hKE0 hEm hEm' A
  have hHb := rpow_le_mul_rpow_of_twoSided (hpos n).2.1 (materialH_pos (x n))
    hKH0 hHn hHn' (-β)
  have hMb := rpow_le_mul_rpow_of_twoSided
    (zero_lt_one.trans_le (hpos n).2.2.2) (materialM_pos (x n)) hKM0 hMn hMn' N
  have hAB := mul_le_mul hHa hEa
    (Real.rpow_nonneg (hpos m).2.2.1.le A)
    (mul_nonneg (Real.rpow_nonneg hKH0.le _) (Real.rpow_nonneg (materialH_pos (x m)).le β))
  have hCD := mul_le_mul hHb hMb
    (Real.rpow_nonneg (zero_le_one.trans (hpos n).2.2.2) N)
    (mul_nonneg (Real.rpow_nonneg hKH0.le _) (Real.rpow_nonneg (materialH_pos (x n)).le (-β)))
  have hproduct := mul_le_mul hAB hCD
    (mul_nonneg (Real.rpow_nonneg (hpos n).2.1.le (-β))
      (Real.rpow_nonneg (zero_le_one.trans (hpos n).2.2.2) N))
    (mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hKH0.le _) (Real.rpow_nonneg (materialH_pos (x m)).le β))
      (mul_nonneg (Real.rpow_nonneg hKE0.le _) (Real.rpow_nonneg (materialE0_pos (x m)).le A)))
  have hraw' : 1 ≤ K0 * materialH (x m) ^ β * materialE0 (x m) ^ A *
      materialH (x n) ^ (-β) * materialM (x n) ^ N := by
    calc
      _ ≤ K * T.H (T.sample m) ^ β * T.E0 (T.sample m) ^ A *
          T.H (T.sample n) ^ (-β) * T.M (T.sample n) ^ N := hraw
      _ = K * ((T.H (T.sample m) ^ β * T.E0 (T.sample m) ^ A) *
          (T.H (T.sample n) ^ (-β) * T.M (T.sample n) ^ N)) := by ring
      _ ≤ K * (((KH ^ |β| * materialH (x m) ^ β) *
          (KE ^ |A| * materialE0 (x m) ^ A)) *
          ((KH ^ |-β| * materialH (x n) ^ (-β)) *
          (KM ^ |N| * materialM (x n) ^ N))) :=
        mul_le_mul_of_nonneg_left hproduct hK.le
      _ = _ := by dsimp only [K0]; ring
  have hfirst := Real.rpow_le_rpow (zero_le_one.trans (hpos m).2.2.2) hMm hp
  rw [Real.mul_rpow hKM0.le (materialM_pos (x m)).le] at hfirst
  have hlast := Real.rpow_le_rpow (materialM_pos (x n)).le hMn' (add_nonneg hp hσ.le)
  rw [Real.mul_rpow hKM0.le (zero_le_one.trans (hpos n).2.2.2)] at hlast
  calc
    _ ≤ KM ^ p * materialM (x m) ^ p := hfirst
    _ ≤ KM ^ p * (C * materialM (x n) ^ (p + σ)) :=
      mul_le_mul_of_nonneg_left (hbalanced (x m) (x n) hxm hxn hraw')
        (Real.rpow_nonneg hKM0.le _)
    _ ≤ KM ^ p * (C * (KM ^ (p + σ) * T.M (T.sample n) ^ (p + σ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlast hC.le)
        (Real.rpow_nonneg hKM0.le _)
    _ = _ := by ring

/-- Changing the output label by a bounded index amount still costs only
the prescribed fixed extra order. In particular one may take `σ = 1`. -/
theorem materialSample_M_rpow_of_reindexed_balanced_height_constraint
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (label : ℕ → ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hlabel : ∀ m, |(D.cellIndex (label m) : ℝ) - D.cellIndex m| ≤ B)
    {β A N K p σ : ℝ} (hβ : 0 < β) (hK : 0 < K)
    (hp : 0 ≤ p) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n : ℕ,
      1 ≤ K * T.H (T.sample (label m)) ^ β * T.E0 (T.sample (label m)) ^ A *
        T.H (T.sample n) ^ (-β) * T.M (T.sample n) ^ N →
      T.M (T.sample m) ^ p ≤ C * T.M (T.sample n) ^ (p + σ) := by
  have hhalf : 0 < σ / 2 := by linarith only [hσ]
  obtain ⟨K1, hK1, hshift⟩ := materialSample_M_rpow_of_index_sub_bound hT hRef hp hhalf hB
  obtain ⟨K2, hK2, hbalanced⟩ := materialSample_M_rpow_of_balanced_height_constraint
    hT hRef (A := A) (N := N) hβ hK (add_nonneg hp hhalf.le) hhalf
  refine ⟨K1 * K2, mul_pos hK1 hK2, fun m n hraw => ?_⟩
  have hs := hshift m (label m) (by simpa only [abs_sub_comm] using hlabel m)
  have hb := hbalanced (label m) n hraw
  have horder : p + σ / 2 + σ / 2 = p + σ := by ring
  rw [horder] at hb
  exact hs.trans ((mul_le_mul_of_nonneg_left hb hK1.le).trans_eq (by ring))

end ContinuousFlexibility.Statements
