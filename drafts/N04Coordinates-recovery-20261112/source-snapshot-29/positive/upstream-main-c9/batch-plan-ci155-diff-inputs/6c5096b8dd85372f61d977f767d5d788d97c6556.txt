import ContinuousFlexibility.Analysis.N01cWeightAbsorption

/-!
# Exact small material weights in products

The material specification already controls every E0 power by M and
bounds H^gamma times every M power when gamma is positive. Their
combination bounds the exact H^gamma E0^A weight on the whole annulus.
Products retain one complete H^gamma factor, with no loss of its exponent.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

/-- A bounded nonnegative weight in a nonempty product retains one copy
of itself. The remaining copies contribute only to the constant. -/
theorem nonempty_weight_power_le {W B : ℝ} (hW : 0 ≤ W) (hWB : W ≤ B)
    {n : ℕ} (hn : 0 < n) :
    W ^ n ≤ B ^ (n - 1) * W := by
  cases n with
  | zero => omega
  | succ n =>
    simp only [Nat.succ_sub_one, pow_succ]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hW hWB n) hW

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

/-- The exact material weight, including any real E0 exponent, is
uniformly bounded on the actual physical annulus. -/
theorem materialHeight_E0_weight_bounded
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {γ : ℝ} (hγ : 0 < γ) (A : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ r ∈ Ioo D.a D.b,
      T.H r ^ γ * T.E0 r ^ A ≤ B := by
  obtain ⟨_, hpos, _, _, _, _, _, _, _, _, _, hE, hHM, _⟩ := hT
  obtain ⟨CE, hCE, hEbound⟩ := hE A
  obtain ⟨CH, hCH, hHbound, _, _⟩ := hHM 1 γ hγ
  refine ⟨CE * CH, mul_pos hCE hCH, fun r hr => ?_⟩
  have hH : 0 ≤ T.H r ^ γ := Real.rpow_nonneg (hpos r hr).2.1.le γ
  have hh : T.H r ^ γ * T.M r ≤ CH := by
    simpa only [Real.rpow_one] using hHbound r hr
  calc
    T.H r ^ γ * T.E0 r ^ A ≤ T.H r ^ γ * (CE * T.M r) :=
      mul_le_mul_of_nonneg_left (hEbound r hr) hH
    _ = CE * (T.H r ^ γ * T.M r) := by ring
    _ ≤ CE * CH := mul_le_mul_of_nonneg_left hh hCE.le

/-- Every positive number of actual small-weight factors keeps one exact
height weight. The constant may depend on the number of factors. -/
theorem materialHeight_E0_weight_power_bound
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {γ : ℝ} (hγ : 0 < γ) (A : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 0 < n → ∀ r ∈ Ioo D.a D.b,
      (T.H r ^ γ * T.E0 r ^ A) ^ n ≤
        B ^ (n - 1) * (T.H r ^ γ * T.E0 r ^ A) := by
  obtain ⟨B, hB, hbound⟩ := materialHeight_E0_weight_bounded hT hγ A
  refine ⟨B, hB, fun n hn r hr => ?_⟩
  have hpos := hT.2.1 r hr
  exact nonempty_weight_power_le
    (mul_nonneg (Real.rpow_nonneg hpos.2.1.le γ)
      (Real.rpow_nonneg hpos.2.2.1.le A)) (hbound r hr) hn

/-- One low-order smallness choice controls the weighted scalar size
uniformly over every physical point. No high-order norm occurs here. -/
theorem exists_uniform_materialWeight_smallness
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {γ : ℝ} (hγ : 0 < γ) (A : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ Ioo D.a D.b, ∀ t : ℝ, |t| ≤ ε →
      |t| * T.H r ^ γ * T.E0 r ^ A ≤ η := by
  obtain ⟨B, hB, hbound⟩ := materialHeight_E0_weight_bounded hT hγ A
  refine ⟨η / B, div_pos hη hB, fun r hr t ht => ?_⟩
  have hpos := hT.2.1 r hr
  have hweight : 0 ≤ T.H r ^ γ * T.E0 r ^ A :=
    mul_nonneg (Real.rpow_nonneg hpos.2.1.le γ)
      (Real.rpow_nonneg hpos.2.2.1.le A)
  calc
    |t| * T.H r ^ γ * T.E0 r ^ A = |t| * (T.H r ^ γ * T.E0 r ^ A) :=
      mul_assoc _ _ _
    _ ≤ (η / B) * B :=
      mul_le_mul ht (hbound r hr) hweight (div_pos hη hB).le
    _ = η := div_mul_cancel₀ η hB.ne'

end ContinuousFlexibility.Statements
