import ContinuousFlexibility.Radial.WeightKernelBounds

/-!
# Summability of the relative-operator block kernel

Section 8 obtains a block bound with two material factors and one decaying
output factor. The exponent absorption has already been proved in
`WeightKernelBounds`. Here it gives a common row and column bound, including
the explicit linear dependence on the size of the perturbation.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

/-- The positive majorant for a block of the relative operator. -/
def n06SourceKernel (c β ε : ℝ) (k m : ℕ) : ℝ :=
  Real.exp (c * logM k + c * logM m - β * radialS k -
    ε * |radialS k - radialS m|)

theorem n06SourceKernel_nonneg (c β ε : ℝ) (k m : ℕ) :
    0 ≤ n06SourceKernel c β ε k m :=
  (Real.exp_pos _).le

/-- Output decay absorbs both material factors before the Schur test. -/
theorem n06SourceKernel_sums (c β ε : ℝ) (hc : 0 ≤ c)
    (hβ : 0 < β) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      (∀ k : ℕ, Summable (n06SourceKernel c β ε k) ∧
        ∑' m : ℕ, n06SourceKernel c β ε k m ≤ C) ∧
      (∀ m : ℕ, Summable (fun k => n06SourceKernel c β ε k m) ∧
        ∑' k : ℕ, n06SourceKernel c β ε k m ≤ C) := by
  obtain ⟨A, hA⟩ := source_weight_absorb c β ε hc hβ hε
  have hη : 0 < ε / 2 := by positivity
  let B : ℝ := 1 + 2 / (Real.exp (ε / 2 * (2 / 3)) - 1)
  have hE : 0 < Real.exp (ε / 2 * (2 / 3)) - 1 := by
    have h := Real.exp_lt_exp.mpr (show 0 < ε / 2 * (2 / 3) by positivity)
    rw [Real.exp_zero] at h
    linarith
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hle : ∀ k m, n06SourceKernel c β ε k m ≤
      Real.exp A * Real.exp (-(ε / 2 * |radialS k - radialS m|)) := by
    intro k m
    rw [n06SourceKernel, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := hA k m
    have hdecay : 0 ≤ β / 2 * radialS k :=
      mul_nonneg (by positivity) (radialS_nonneg k)
    linarith
  refine ⟨Real.exp A * B, mul_pos (Real.exp_pos A) hB, ?_, ?_⟩
  · intro k
    obtain ⟨hs, hb⟩ := radialS_row_sum hη k
    have hsm := hs.mul_left (Real.exp A)
    have hs' : Summable (n06SourceKernel c β ε k) :=
      Summable.of_nonneg_of_le (n06SourceKernel_nonneg c β ε k) (hle k) hsm
    refine ⟨hs', ?_⟩
    calc
      ∑' m, n06SourceKernel c β ε k m ≤
          ∑' m, Real.exp A * Real.exp (-(ε / 2 * |radialS k - radialS m|)) :=
        hs'.tsum_le_tsum (hle k) hsm
      _ = Real.exp A * ∑' m, Real.exp (-(ε / 2 * |radialS k - radialS m|)) :=
        tsum_mul_left
      _ ≤ Real.exp A * B :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos A).le
  · intro m
    obtain ⟨hs, hb⟩ := radialS_col_sum hη m
    have hsm := hs.mul_left (Real.exp A)
    have hs' : Summable (fun k => n06SourceKernel c β ε k m) :=
      Summable.of_nonneg_of_le (fun k => n06SourceKernel_nonneg c β ε k m)
        (fun k => hle k m) hsm
    refine ⟨hs', ?_⟩
    calc
      ∑' k, n06SourceKernel c β ε k m ≤
          ∑' k, Real.exp A * Real.exp (-(ε / 2 * |radialS k - radialS m|)) :=
        hs'.tsum_le_tsum (fun k => hle k m) hsm
      _ = Real.exp A * ∑' k, Real.exp (-(ε / 2 * |radialS k - radialS m|)) :=
        tsum_mul_left
      _ ≤ Real.exp A * B :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos A).le

/-- The same constant bounds every nonnegative scalar multiple of the kernel. -/
theorem n06SourceKernel_scaled_sums (c β ε : ℝ) (hc : 0 ≤ c)
    (hβ : 0 < β) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, 0 ≤ θ →
      (∀ k : ℕ, Summable (fun m => θ * n06SourceKernel c β ε k m) ∧
        ∑' m : ℕ, θ * n06SourceKernel c β ε k m ≤ θ * C) ∧
      (∀ m : ℕ, Summable (fun k => θ * n06SourceKernel c β ε k m) ∧
        ∑' k : ℕ, θ * n06SourceKernel c β ε k m ≤ θ * C) := by
  obtain ⟨C, hC, hrow, hcol⟩ := n06SourceKernel_sums c β ε hc hβ hε
  refine ⟨C, hC, ?_⟩
  intro θ hθ
  constructor
  · intro k
    refine ⟨(hrow k).1.mul_left θ, ?_⟩
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (hrow k).2 hθ
  · intro m
    refine ⟨(hcol m).1.mul_left θ, ?_⟩
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (hcol m).2 hθ

/-- The relative block estimate gives a linear, rather than square-root,
dependence on the perturbation size after taking the Schur norm bound. -/
theorem n06SourceKernel_operator_bound {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (c β ε : ℝ) (hc : 0 ≤ c) (hβ : 0 < β) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, 0 ≤ θ → ∀ T : E →L[ℝ] F,
      ∀ p : ℕ → E → ℝ, ∀ n : ℕ → F → ℝ,
      (∀ m x, 0 ≤ p m x) → (∀ k y, 0 ≤ n k y) →
      (∀ x, Summable (fun m => p m x ^ 2) ∧ ∑' m, p m x ^ 2 ≤ ‖x‖ ^ 2) →
      (∀ y, Summable (fun k => n k y ^ 2) ∧ ∑' k, n k y ^ 2 ≤ ‖y‖ ^ 2) →
      (∀ x y, |inner ℝ y (T x)| ≤
        ∑' q : ℕ × ℕ, (θ * n06SourceKernel c β ε q.1 q.2) * n q.1 y * p q.2 x) →
      ‖T‖ ≤ C * θ := by
  obtain ⟨C, hC, hsums⟩ := n06SourceKernel_scaled_sums c β ε hc hβ hε
  refine ⟨C, hC, ?_⟩
  intro θ hθ T p n hp0 hn0 hp hn hT
  obtain ⟨hrow, hcol⟩ := hsums θ hθ
  have hθC : 0 ≤ θ * C := mul_nonneg hθ hC.le
  have h := schur_operator_bound T p n
    (fun k m => θ * n06SourceKernel c β ε k m)
    hθC hθC (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)
    (fun k m => mul_nonneg hθ (n06SourceKernel_nonneg c β ε k m))
    hrow hcol hp0 hn0
    (fun x => ⟨(hp x).1, by simpa only [one_mul] using (hp x).2⟩)
    (fun y => ⟨(hn y).1, by simpa only [one_mul] using (hn y).2⟩) hT
  have heq : (θ * C) * (θ * C) * 1 * 1 = (θ * C) ^ 2 := by ring
  rw [heq, Real.sqrt_sq hθC] at h
  simpa only [mul_comm C θ] using h

end ContinuousFlexibility.Radial

