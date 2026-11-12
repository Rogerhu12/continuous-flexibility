import ContinuousFlexibility.Analysis.MaterialSampleBalancedConstraint

/-!
# Full weighted sample comparison with a fixed loss

The balanced height constraint first controls the inverse height weight.
Its auxiliary endpoint loss costs a fixed number of material orders.
The remaining order-dependent factor then uses the balanced material
comparison with one extra order, so the final loss is independent of
the requested differentiability order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

theorem materialSample_E0_rpow_le_M
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D) (A : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ,
      T.E0 (T.sample m) ^ A ≤ K * T.M (T.sample m) := by
  have hdata := hT
  rcases hdata with ⟨_, _, _, _, _, _, _, _, _, _, _, hE, _, _, _, _, _, _⟩
  obtain ⟨K, hK, hbound⟩ := hE A
  obtain ⟨_, hgeom⟩ := hRef
  exact ⟨K, hK, fun m => hbound _ (materialSample_mem_radialCore hT hgeom.2.1 m)⟩

/-- A bounded change of the sample index costs two material orders for
the full weight, uniformly in its material exponent. -/
theorem materialSample_H_M_rpow_of_index_sub_bound
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (γ : ℝ) {p B : ℝ} (hp : 0 ≤ p) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ m n : ℕ,
      |(D.cellIndex m : ℝ) - D.cellIndex n| ≤ B →
      T.H (T.sample m) ^ γ * T.M (T.sample m) ^ p ≤
        K * T.H (T.sample n) ^ γ * T.M (T.sample n) ^ (p + 2) := by
  obtain ⟨KH, A, hKH, _, hheight⟩ :=
    materialSample_H_E0_rpow_of_index_sub_bound hT hRef γ (le_refl (0 : ℝ)) hB
  obtain ⟨KE, hKE, hendpoint⟩ := materialSample_E0_rpow_le_M hT hRef A
  obtain ⟨KM, hKM, hmaterial⟩ := materialSample_M_rpow_of_index_sub_bound
    hT hRef hp (by norm_num : (0 : ℝ) < 1) hB
  obtain ⟨_, hgeom⟩ := hRef
  have hpos (m : ℕ) := hT.2.1 _ (materialSample_mem_radialCore hT hgeom.2.1 m)
  refine ⟨KH * KE * KM, mul_pos (mul_pos hKH hKE) hKM, fun m n hmn => ?_⟩
  have hH : T.H (T.sample m) ^ γ ≤
      KH * T.H (T.sample n) ^ γ * T.E0 (T.sample n) ^ A := by
    simpa only [Real.rpow_zero, mul_one] using hheight m n hmn
  have hH' : T.H (T.sample m) ^ γ ≤
      KH * T.H (T.sample n) ^ γ * (KE * T.M (T.sample n)) :=
    hH.trans (mul_le_mul_of_nonneg_left (hendpoint n)
      (mul_nonneg hKH.le (Real.rpow_nonneg (hpos n).2.1.le γ)))
  have hM := hmaterial m n hmn
  have hMn : 0 < T.M (T.sample n) := zero_lt_one.trans_le (hpos n).2.2.2
  calc
    _ ≤ (KH * T.H (T.sample n) ^ γ * (KE * T.M (T.sample n))) *
        (KM * T.M (T.sample n) ^ (p + 1)) :=
      mul_le_mul hH' hM
        (Real.rpow_nonneg (zero_le_one.trans (hpos m).2.2.2) p)
        (mul_nonneg (mul_nonneg hKH.le (Real.rpow_nonneg (hpos n).2.1.le γ))
          (mul_nonneg hKE.le hMn.le))
    _ = _ := by
      rw [show p + 2 = (p + 1) + 1 by ring,
        Real.rpow_add hMn (p + 1) 1, Real.rpow_one]
      ring

/-- The inverse height weight is controlled with a fixed material
exponent determined by the original balanced constraint. -/
theorem materialSample_H_neg_rpow_of_reindexed_balanced_height_constraint
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (label : ℕ → ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hlabel : ∀ m, |(D.cellIndex (label m) : ℝ) - D.cellIndex m| ≤ B)
    {β A N K : ℝ} (hβ : 0 < β) (hK : 0 < K) :
    ∃ CH : ℝ, 0 < CH ∧ ∀ m n : ℕ,
      1 ≤ K * T.H (T.sample (label m)) ^ β * T.E0 (T.sample (label m)) ^ A *
        T.H (T.sample n) ^ (-β) * T.M (T.sample n) ^ N →
      T.H (T.sample m) ^ (-β) ≤
        CH * T.H (T.sample n) ^ (-β) * T.M (T.sample n) ^ (N + 2) := by
  obtain ⟨KH, P, hKH, _, hheight⟩ :=
    materialSample_H_E0_rpow_of_index_sub_bound hT hRef (-β)
      (le_refl (0 : ℝ)) hB
  obtain ⟨KE, hKE, hendpoint⟩ := materialSample_E0_rpow_le_M hT hRef (A + P)
  obtain ⟨KM, hKM, hmaterial⟩ := materialSample_M_rpow_of_balanced_height_constraint
    hT hRef (A := A) (N := N) hβ hK (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) < 1)
  obtain ⟨_, hgeom⟩ := hRef
  have hpos (m : ℕ) := hT.2.1 _ (materialSample_mem_radialCore hT hgeom.2.1 m)
  refine ⟨KH * K * KE * KM, mul_pos (mul_pos (mul_pos hKH hK) hKE) hKM,
    fun m n hraw => ?_⟩
  let Q : ℝ := T.H (T.sample n) ^ (-β) * T.M (T.sample n) ^ N
  have hQ : 0 ≤ Q := mul_nonneg (Real.rpow_nonneg (hpos n).2.1.le _)
    (Real.rpow_nonneg (zero_le_one.trans (hpos n).2.2.2) _)
  have hHc : 0 < T.H (T.sample (label m)) := (hpos (label m)).2.1
  have hEc : 0 < T.E0 (T.sample (label m)) := (hpos (label m)).2.2.1
  have hMn : 0 < T.M (T.sample n) := zero_lt_one.trans_le (hpos n).2.2.2
  have hcancel : T.H (T.sample (label m)) ^ (-β) *
      T.H (T.sample (label m)) ^ β = 1 := by
    rw [← Real.rpow_add hHc, neg_add_cancel, Real.rpow_zero]
  have hinverse : T.H (T.sample (label m)) ^ (-β) ≤
      K * T.E0 (T.sample (label m)) ^ A * Q := by
    calc
      _ = T.H (T.sample (label m)) ^ (-β) * 1 := (mul_one _).symm
      _ ≤ T.H (T.sample (label m)) ^ (-β) *
          (K * T.H (T.sample (label m)) ^ β * T.E0 (T.sample (label m)) ^ A *
            T.H (T.sample n) ^ (-β) * T.M (T.sample n) ^ N) :=
        mul_le_mul_of_nonneg_left hraw (Real.rpow_nonneg hHc.le _)
      _ = (T.H (T.sample (label m)) ^ (-β) * T.H (T.sample (label m)) ^ β) *
          (K * T.E0 (T.sample (label m)) ^ A * Q) := by dsimp only [Q]; ring
      _ = _ := by rw [hcancel, one_mul]
  have hshift : T.H (T.sample m) ^ (-β) ≤
      KH * T.H (T.sample (label m)) ^ (-β) * T.E0 (T.sample (label m)) ^ P := by
    simpa only [Real.rpow_zero, mul_one] using hheight m (label m)
      (by simpa only [abs_sub_comm] using hlabel m)
  have hM : T.M (T.sample (label m)) ≤ KM * T.M (T.sample n) ^ (2 : ℝ) := by
    simpa only [Real.rpow_one, one_add_one_eq_two] using hmaterial (label m) n hraw
  calc
    _ ≤ KH * T.H (T.sample (label m)) ^ (-β) * T.E0 (T.sample (label m)) ^ P := hshift
    _ ≤ KH * (K * T.E0 (T.sample (label m)) ^ A * Q) *
        T.E0 (T.sample (label m)) ^ P :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinverse hKH.le)
        (Real.rpow_nonneg hEc.le _)
    _ = (KH * K) * T.E0 (T.sample (label m)) ^ (A + P) * Q := by
      rw [Real.rpow_add hEc]; ring
    _ ≤ (KH * K) * (KE * T.M (T.sample (label m))) * Q :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hendpoint (label m)) (mul_pos hKH hK).le) hQ
    _ ≤ (KH * K) * (KE * (KM * T.M (T.sample n) ^ (2 : ℝ))) * Q :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM hKE.le)
          (mul_pos hKH hK).le) hQ
    _ = _ := by dsimp only [Q]; rw [Real.rpow_add hMn]; ring

/-- One loss is chosen before the differentiability order. In particular,
the height weight and the material grading are transferred together. -/
theorem materialSample_H_M_pow_of_reindexed_balanced_height_constraint
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (label : ℕ → ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hlabel : ∀ m, |(D.cellIndex (label m) : ℝ) - D.cellIndex m| ≤ B)
    {β A N K : ℝ} (hβ : 0 < β) (hK : 0 < K) :
    ∃ loss : ℕ, ∀ s : ℕ, ∃ Cs : ℝ, 0 < Cs ∧ ∀ m n : ℕ,
      1 ≤ K * T.H (T.sample (label m)) ^ β * T.E0 (T.sample (label m)) ^ A *
        T.H (T.sample n) ^ (-β) * T.M (T.sample n) ^ N →
      T.H (T.sample m) ^ (-β) * T.M (T.sample m) ^ s ≤
        Cs * T.H (T.sample n) ^ (-β) * T.M (T.sample n) ^ (s + loss) := by
  obtain ⟨CH, hCH, hheight⟩ :=
    materialSample_H_neg_rpow_of_reindexed_balanced_height_constraint
      hT hRef label hB hlabel (A := A) (N := N) hβ hK
  obtain ⟨loss, hloss⟩ := exists_nat_ge (N + 3)
  have hRef' := hRef
  obtain ⟨_, hgeom⟩ := hRef'
  have hpos (m : ℕ) := hT.2.1 _ (materialSample_mem_radialCore hT hgeom.2.1 m)
  refine ⟨loss, fun s => ?_⟩
  obtain ⟨CM, hCM, hmaterial⟩ :=
    materialSample_M_rpow_of_reindexed_balanced_height_constraint
      hT hRef label hB hlabel (A := A) (N := N) hβ hK (Nat.cast_nonneg s)
        (by norm_num : (0 : ℝ) < 1)
  refine ⟨CH * CM, mul_pos hCH hCM, fun m n hraw => ?_⟩
  have hMn : 0 < T.M (T.sample n) := zero_lt_one.trans_le (hpos n).2.2.2
  have hprod := mul_le_mul (hheight m n hraw) (hmaterial m n hraw)
    (Real.rpow_nonneg (zero_le_one.trans (hpos m).2.2.2) (s : ℝ))
    (mul_nonneg (mul_nonneg hCH.le (Real.rpow_nonneg (hpos n).2.1.le _))
      (Real.rpow_nonneg hMn.le _))
  have hcombined : T.H (T.sample m) ^ (-β) * T.M (T.sample m) ^ (s : ℝ) ≤
      (CH * CM) * T.H (T.sample n) ^ (-β) *
        T.M (T.sample n) ^ ((N + 2) + ((s : ℝ) + 1)) := by
    exact hprod.trans_eq (by rw [Real.rpow_add hMn (N + 2) ((s : ℝ) + 1)]; ring)
  have horder : (N + 2) + ((s : ℝ) + 1) ≤ ((s + loss : ℕ) : ℝ) := by
    push_cast
    linarith only [hloss]
  have hfinal := hcombined.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (hpos n).2.2.2 horder)
      (mul_nonneg (mul_pos hCH hCM).le (Real.rpow_nonneg (hpos n).2.1.le _)))
  simpa only [Real.rpow_natCast] using hfinal

end ContinuousFlexibility.Statements
