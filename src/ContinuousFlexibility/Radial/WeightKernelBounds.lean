module

public import ContinuousFlexibility.Radial.ScaleSlowVariation
public import ContinuousFlexibility.Radial.WeightedSchurTest

/-!
# Weight absorption and kernel sums for the block Schur estimates

Scalar (exponent-level) facts used in the two-weight Schur arguments of Sections 6 and 8:
coefficient weights `exp (c * logM)` or `exp (c * q)` are absorbed by a fraction of the
attenuation `exp (-ε |S_k - S_m|)`, and the resulting kernels have uniformly bounded row and
column sums.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real
open ContinuousFlexibility.Statements

/-! ### Basic facts -/

theorem radialS_zero : radialS 0 = 0 := by
  simp [radialS]

theorem radialS_nonneg (m : ℕ) : 0 ≤ radialS m := by
  unfold radialS
  positivity

theorem radialS_gap (m : ℕ) : (2 / 3 : ℝ) ≤ radialS (m + 1) - radialS m := by
  have h := cubic_gap_ge m
  unfold radialS
  push_cast
  exact h

theorem logM_ge_one (m : ℕ) : 1 ≤ logM m := by
  unfold logM
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have := mul_nonneg (Real.rpow_nonneg hm (5 / 2 : ℝ)) (sq_nonneg (log (Real.exp 1 + m)))
  linarith

/-! ### Row and column sums -/

theorem radialS_row_sum {η : ℝ} (hη : 0 < η) (k : ℕ) :
    Summable (fun m : ℕ => Real.exp (-(η * |radialS k - radialS m|))) ∧
      ∑' m : ℕ, Real.exp (-(η * |radialS k - radialS m|)) ≤
        1 + 2 / (Real.exp (η * (2 / 3)) - 1) :=
  exp_row_sum_le (S := radialS) (by norm_num) hη radialS_gap k

theorem radialS_col_sum {η : ℝ} (hη : 0 < η) (m : ℕ) :
    Summable (fun k : ℕ => Real.exp (-(η * |radialS k - radialS m|))) ∧
      ∑' k : ℕ, Real.exp (-(η * |radialS k - radialS m|)) ≤
        1 + 2 / (Real.exp (η * (2 / 3)) - 1) := by
  have e : ∀ k : ℕ, |radialS k - radialS m| = |radialS m - radialS k| :=
    fun k => abs_sub_comm _ _
  simp_rw [e]
  exact radialS_row_sum hη m

/-! ### Comparison with the attenuation exponent -/

theorem logM_le_radialS (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ k : ℕ, logM k ≤ ε * radialS k + C := by
  obtain ⟨C, hC⟩ := logM_sub_le ε hε
  refine ⟨C + logM 0, fun k => ?_⟩
  have h := hC k 0
  rw [radialS_zero, sub_zero, abs_of_nonneg (radialS_nonneg k)] at h
  have := le_abs_self (logM k - logM 0)
  linarith

theorem radialQ_le_radialS (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ k : ℕ, radialQ k ≤ ε * radialS k + C := by
  obtain ⟨C, hC⟩ := radialQ_sub_le ε hε
  refine ⟨C + radialQ 0, fun k => ?_⟩
  have h := hC k 0
  rw [radialS_zero, sub_zero, abs_of_nonneg (radialS_nonneg k)] at h
  have := le_abs_self (radialQ k - radialQ 0)
  linarith

/-! ### Absorption of a fixed multiple of a slowly varying exponent -/

theorem mul_div_succ_le {a e : ℝ} (ha : 0 ≤ a) (he : 0 ≤ e) : a * (e / (a + 1)) ≤ e := by
  have h1 : 0 < a + 1 := by linarith
  rw [← mul_div_assoc, div_le_iff₀ h1]
  nlinarith

theorem absorb_diff (f : ℕ → ℝ)
    (hf : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ k m : ℕ, |f k - f m| ≤ ε * |radialS k - radialS m| + C)
    (u e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, ∀ k m : ℕ, u * (f m - f k) ≤ e * |radialS k - radialS m| + C := by
  have hb : 0 ≤ |u| := abs_nonneg u
  obtain ⟨C, hC⟩ := hf (e / (|u| + 1)) (by positivity)
  refine ⟨|u| * C, fun k m => ?_⟩
  have h1 : u * (f m - f k) ≤ |u| * |f k - f m| := by
    calc u * (f m - f k) ≤ |u * (f m - f k)| := le_abs_self _
      _ = |u| * |f m - f k| := abs_mul _ _
      _ = |u| * |f k - f m| := by rw [abs_sub_comm (f m)]
  have h2 := mul_le_mul_of_nonneg_left (hC k m) hb
  have h3 := mul_le_mul_of_nonneg_right (mul_div_succ_le hb he.le)
    (abs_nonneg (radialS k - radialS m))
  nlinarith

theorem absorb_logM (u e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, ∀ k m : ℕ, u * (logM m - logM k) ≤ e * |radialS k - radialS m| + C :=
  absorb_diff logM logM_sub_le u e he

theorem absorb_radialQ (u e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, ∀ k m : ℕ, u * (radialQ m - radialQ k) ≤ e * |radialS k - radialS m| + C :=
  absorb_diff radialQ radialQ_sub_le u e he

/-! ### Off-diagonal weight absorption (Section 8) -/

theorem offdiag_weight_absorb (t L ε : ℝ) (hL : 2 ≤ L) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ k m : ℕ,
      (t - L + 1) * logM k + (1 - t) * logM m - ε * |radialS k - radialS m| ≤
        C - ε / 2 * |radialS k - radialS m| := by
  obtain ⟨C, hC⟩ := absorb_logM (1 - t) (ε / 2) (by positivity)
  refine ⟨C, fun k m => ?_⟩
  have h1 := hC k m
  have h2 := mul_nonneg (sub_nonneg.mpr hL) (zero_le_one.trans (logM_ge_one k))
  nlinarith

/-! ### Decaying-source absorption (Section 8) -/

theorem source_weight_absorb (c β ε : ℝ) (hc : 0 ≤ c) (hβ : 0 < β) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ k m : ℕ,
      c * logM k + c * logM m - β * radialS k - ε * |radialS k - radialS m| ≤
        C - β / 2 * radialS k - ε / 2 * |radialS k - radialS m| := by
  obtain ⟨C₁, hC₁⟩ := absorb_logM c (ε / 2) (by positivity)
  obtain ⟨C₂, hC₂⟩ := logM_le_radialS (β / 4 / (c + 1)) (by positivity)
  refine ⟨C₁ + 2 * c * C₂, fun k m => ?_⟩
  have h1 := hC₁ k m
  have h2 := mul_le_mul_of_nonneg_left (hC₂ k) (show 0 ≤ 2 * c by linarith)
  have h3 := mul_le_mul_of_nonneg_right (mul_div_succ_le hc (show 0 ≤ β / 4 by positivity))
    (radialS_nonneg k)
  nlinarith

/-! ### The outer block exponent (Section 6) -/

theorem outer_block_exponent (M₀ M₁ a d₁ γ γp : ℝ) (hγ : 0 < γ) (hγγp : γ ≤ γp) (hγp : γp < 1)
    (hM : max M₀ (2 * a + d₁) < M₁) :
    ∃ C : ℝ, ∀ k m : ℕ,
      -(M₁ - 2 * a - d₁) * radialQ k + (a - M₀) * (radialQ m - radialQ k) -
          |radialS k - radialS m| + γ * (radialS k - radialS m) ≤
        C - (1 - γp) / 2 * |radialS k - radialS m| := by
  obtain ⟨C, hC⟩ := absorb_radialQ (a - M₀) ((1 - γp) / 2) (by linarith)
  refine ⟨C, fun k m => ?_⟩
  have h1 := hC k m
  have hM2 : 2 * a + d₁ < M₁ := lt_of_le_of_lt (le_max_right _ _) hM
  have h2 := mul_nonneg (show 0 ≤ M₁ - 2 * a - d₁ by linarith) (radialQ_nonneg k)
  have hD := abs_nonneg (radialS k - radialS m)
  have h3 : γ * (radialS k - radialS m) ≤ γ * |radialS k - radialS m| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) hγ.le
  have h4 := mul_le_mul_of_nonneg_right hγγp hD
  nlinarith

/-! ### Exponentiated kernels for the Schur test -/

theorem weight_kernel_sums (t L ε : ℝ) (hL : 2 ≤ L) (hε : 0 < ε) :
    ∃ C' : ℝ, 0 < C' ∧
      (∀ k : ℕ,
        Summable (fun m : ℕ => Real.exp ((t - L + 1) * logM k + (1 - t) * logM m -
          ε * |radialS k - radialS m|)) ∧
        ∑' m : ℕ, Real.exp ((t - L + 1) * logM k + (1 - t) * logM m -
          ε * |radialS k - radialS m|) ≤ C') ∧
      (∀ m : ℕ,
        Summable (fun k : ℕ => Real.exp ((t - L + 1) * logM k + (1 - t) * logM m -
          ε * |radialS k - radialS m|)) ∧
        ∑' k : ℕ, Real.exp ((t - L + 1) * logM k + (1 - t) * logM m -
          ε * |radialS k - radialS m|) ≤ C') := by
  obtain ⟨C, hC⟩ := offdiag_weight_absorb t L ε hL hε
  have hη : 0 < ε / 2 := by positivity
  set B : ℝ := 1 + 2 / (Real.exp (ε / 2 * (2 / 3)) - 1) with hB
  have hE : 0 < Real.exp (ε / 2 * (2 / 3)) - 1 := by
    have := Real.exp_lt_exp.2 (show 0 < ε / 2 * (2 / 3) by positivity)
    rw [Real.exp_zero] at this
    linarith
  have hBpos : 0 < B := by rw [hB]; positivity
  have hle : ∀ k m : ℕ, Real.exp ((t - L + 1) * logM k + (1 - t) * logM m -
      ε * |radialS k - radialS m|) ≤
        Real.exp C * Real.exp (-(ε / 2 * |radialS k - radialS m|)) := by
    intro k m
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have := hC k m
    linarith
  refine ⟨Real.exp C * B, mul_pos (Real.exp_pos _) hBpos, fun k => ?_, fun m => ?_⟩
  · obtain ⟨hs, hb⟩ := radialS_row_sum hη k
    have hsm := hs.mul_left (Real.exp C)
    have hs' : Summable (fun m : ℕ => Real.exp ((t - L + 1) * logM k + (1 - t) * logM m -
        ε * |radialS k - radialS m|)) :=
      Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun m => hle k m) hsm
    refine ⟨hs', ?_⟩
    calc _ ≤ ∑' m : ℕ, Real.exp C * Real.exp (-(ε / 2 * |radialS k - radialS m|)) :=
          Summable.tsum_le_tsum (fun m => hle k m) hs' hsm
      _ = Real.exp C * ∑' m : ℕ, Real.exp (-(ε / 2 * |radialS k - radialS m|)) :=
          tsum_mul_left
      _ ≤ Real.exp C * B :=
          mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
  · obtain ⟨hs, hb⟩ := radialS_col_sum hη m
    have hsm := hs.mul_left (Real.exp C)
    have hs' : Summable (fun k : ℕ => Real.exp ((t - L + 1) * logM k + (1 - t) * logM m -
        ε * |radialS k - radialS m|)) :=
      Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun k => hle k m) hsm
    refine ⟨hs', ?_⟩
    calc _ ≤ ∑' k : ℕ, Real.exp C * Real.exp (-(ε / 2 * |radialS k - radialS m|)) :=
          Summable.tsum_le_tsum (fun k => hle k m) hs' hsm
      _ = Real.exp C * ∑' k : ℕ, Real.exp (-(ε / 2 * |radialS k - radialS m|)) :=
          tsum_mul_left
      _ ≤ Real.exp C * B :=
          mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le

end ContinuousFlexibility.Radial
