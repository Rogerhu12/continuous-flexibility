import ContinuousFlexibility.Analysis.N08SampleEnvelopeComparison
import ContinuousFlexibility.Scalar.WeightedReferenceCoefficients

/-!
# Removing the coefficient losses from the physical-label height comparison

The reference return margin costs a discrete radial coefficient, while the
N01 mixed flow estimate costs an envelope at its original label. One extra
positive physical height power and half of the label height power absorb
both costs. The resulting exponents are still strictly positive.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

variable {D : ReferenceData} {T : MaterialData}

theorem n08_material_height_E0_bound (hT : IsMaterialData D T)
    {γ : ℝ} (hγ : 0 < γ) (A : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ r ∈ Ioo D.a D.b, T.H r ^ γ * T.E0 r ^ A ≤ K := by
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hE, hdecay, _⟩ := hdata
  obtain ⟨B, hB, hBb⟩ := hE A
  obtain ⟨C, hC, hCb, _⟩ := hdecay 1 γ hγ
  refine ⟨B * C, mul_pos hB hC, fun r hr => ?_⟩
  have hp : 0 ≤ T.H r ^ γ := Real.rpow_nonneg (hT.2.1 r hr).2.1.le _
  have hc : T.H r ^ γ * T.M r ≤ C := by simpa only [Real.rpow_one] using hCb r hr
  calc
    _ ≤ T.H r ^ γ * (B * T.M r) := mul_le_mul_of_nonneg_left (hBb r hr) hp
    _ = B * (T.H r ^ γ * T.M r) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hc hB.le

theorem n08_sample_height_radialE_bound (hD : IsAccumulatingProfile D)
    (hT : IsMaterialData D T) {γ A : ℝ} (hγ : 0 < γ) (hA : 0 ≤ A) :
    ∃ K : ℝ, 0 < K ∧ ∀ m,
      T.H (T.sample m) ^ γ * radialE (D.cellIndex m) ^ A ≤ K := by
  obtain ⟨B, hB, hBb⟩ := referenceCellCoefficient_le_materialM hD hT hA
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hdecay, _, _, hsamp, _⟩ := hdata
  obtain ⟨C, hC, hCb, _⟩ := hdecay 1 γ hγ
  obtain ⟨C0, hC0⟩ := hD
  refine ⟨B * C, mul_pos hB hC, fun m => ?_⟩
  have hm := materialSample_mem_radialCore hT hC0.2.1 m
  have hp : 0 ≤ T.H (T.sample m) ^ γ := Real.rpow_nonneg (hT.2.1 _ hm).2.1.le _
  have hc : T.H (T.sample m) ^ γ * T.M (T.sample m) ≤ C := by
    simpa only [Real.rpow_one] using hCb _ hm
  calc
    _ ≤ T.H (T.sample m) ^ γ * (B * T.M (T.sample m)) :=
      mul_le_mul_of_nonneg_left (hBb m _ (hsamp m)) hp
    _ = B * (T.H (T.sample m) ^ γ * T.M (T.sample m)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hc hB.le

theorem n08_physical_label_height_comparison (hD : IsAccumulatingProfile D)
    (hT : IsMaterialData D T) (physical label : ℕ → ℕ)
    {a b A B C : ℝ} (hb : 0 < b) (hA : 0 ≤ A) (hC : 0 < C)
    (hcompare : ∀ m, T.H (T.sample (physical m)) ^ a ≤
      C * T.H (T.sample (label m)) ^ b * T.E0 (T.sample (label m)) ^ B *
        radialE (D.cellIndex (physical m)) ^ A) :
    ∃ K : ℝ, 0 < K ∧ ∀ m,
      T.H (T.sample (physical m)) ^ (a + 1) ≤ K * T.H (T.sample (label m)) ^ (b / 2) := by
  obtain ⟨P, hP, hPb⟩ := n08_sample_height_radialE_bound hD hT (by norm_num : (0 : ℝ) < 1) hA
  obtain ⟨L, hL, hLb⟩ := n08_material_height_E0_bound hT (half_pos hb) B
  obtain ⟨C0, hC0⟩ := hD
  have hcore (m : ℕ) := materialSample_mem_radialCore hT hC0.2.1 m
  refine ⟨C * P * L, mul_pos (mul_pos hC hP) hL, fun m => ?_⟩
  let p := T.H (T.sample (physical m))
  let q := T.H (T.sample (label m))
  let e := T.E0 (T.sample (label m)) ^ B
  let r := radialE (D.cellIndex (physical m)) ^ A
  have hp : 0 < p := (hT.2.1 _ (hcore _)).2.1
  have hq : 0 < q := (hT.2.1 _ (hcore _)).2.1
  have he : 0 ≤ e := Real.rpow_nonneg (hT.2.1 _ (hcore _)).2.2.1.le _
  have hr : 0 ≤ r := Real.rpow_nonneg (Real.exp_pos _).le _
  have hqhalf : 0 ≤ q ^ (b / 2) := Real.rpow_nonneg hq.le _
  have hpr : p * r ≤ P := by simpa only [Real.rpow_one] using hPb (physical m)
  have hqe : q ^ (b / 2) * e ≤ L := hLb _ (hcore _)
  have hqsplit : q ^ b = q ^ (b / 2) * q ^ (b / 2) := by
    rw [← Real.rpow_add hq]
    congr 1
    ring
  change p ^ (a + 1) ≤ (C * P * L) * q ^ (b / 2)
  calc
    _ = p * p ^ a := by rw [Real.rpow_add hp, Real.rpow_one]; ring
    _ ≤ p * (C * q ^ b * e * r) := mul_le_mul_of_nonneg_left (hcompare m) hp.le
    _ = C * q ^ (b / 2) * ((p * r) * (q ^ (b / 2) * e)) := by rw [hqsplit]; ring
    _ ≤ C * q ^ (b / 2) * (P * L) := mul_le_mul_of_nonneg_left
      (mul_le_mul hpr hqe (mul_nonneg hqhalf he) hP.le) (mul_nonneg hC.le hqhalf)
    _ = _ := by ring

end ContinuousFlexibility.Statements
