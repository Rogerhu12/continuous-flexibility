import ContinuousFlexibility.Radial.TailFundamentalGreenKernel
import ContinuousFlexibility.Radial.TailActualSolutionNodes
import ContinuousFlexibility.Radial.TailNodeProducts

/-!
# Localized bounds for the actual fundamental Green kernel

The four products of neighboring endpoint values control the product of
two physical Poisson interpolants. Shifting the left endpoint consumes one
decay factor. On the same edge, the conserved discrete Wronskian supplies
the single product whose node order is reversed.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open scoped BigOperators
open ContinuousFlexibility.Statements

theorem tailGreen_prod_Ico_succ_le {r : ℕ → ℝ}
    (hr₀ : ∀ k, 0 ≤ r k) (hr₁ : ∀ k, r k ≤ 1) {m n : ℕ} (hmn : m ≤ n) :
    (∏ k ∈ Finset.Ico m (n + 1), r k) ≤ ∏ k ∈ Finset.Ico m n, r k := by
  rw [Finset.prod_Ico_succ_top hmn]
  exact (mul_le_mul_of_nonneg_left (hr₁ n)
    (Finset.prod_nonneg fun k _ => hr₀ k)).trans_eq (mul_one _)

theorem tailGreen_shifted_node_product_bound {w u g r H : ℕ → ℝ}
    (hr₀ : ∀ k, 0 ≤ r k)
    (hΓ : ∀ m n, m ≤ n → |w m * u n| ≤ g m * ∏ k ∈ Finset.Ico m n, r k)
    (hshift : ∀ m, g (m + 1) ≤ H m * r m) {m n : ℕ} (hmn : m < n) :
    |w (m + 1) * u n| ≤ H m * ∏ k ∈ Finset.Ico m n, r k := by
  calc
    |w (m + 1) * u n| ≤ g (m + 1) * ∏ k ∈ Finset.Ico (m + 1) n, r k :=
      hΓ (m + 1) n (Nat.succ_le_of_lt hmn)
    _ ≤ (H m * r m) * ∏ k ∈ Finset.Ico (m + 1) n, r k :=
      mul_le_mul_of_nonneg_right (hshift m) (Finset.prod_nonneg fun k _ => hr₀ k)
    _ = H m * ∏ k ∈ Finset.Ico m n, r k := by
      rw [Finset.prod_eq_prod_Ico_succ_bot hmn]
      ring

theorem tailGreen_reverse_node_product_bound {w₀ w₁ u₀ u₁ c L g r H : ℝ}
    (hc : 0 < c) (hcL : 1 / c ≤ L) (hg : 0 ≤ g) (hr : r ≤ 1)
    (hΓ : |w₀ * u₁| ≤ g * r) (hbudget : L + g ≤ H)
    (hcross : c * (u₀ * w₁ - u₁ * w₀) = 1) : |w₁ * u₀| ≤ H := by
  have heq : w₁ * u₀ = 1 / c + w₀ * u₁ := by
    apply (mul_left_cancel₀ hc.ne')
    field_simp [hc.ne']
    nlinarith only [hcross]
  calc
    |w₁ * u₀| = |1 / c + w₀ * u₁| := congrArg abs heq
    _ ≤ |1 / c| + |w₀ * u₁| := abs_add _ _
    _ = 1 / c + |w₀ * u₁| := by rw [abs_of_pos (one_div_pos.mpr hc)]
    _ ≤ L + g * r := add_le_add hcL hΓ
    _ ≤ L + g := add_le_add_left ((mul_le_mul_of_nonneg_left hr hg).trans_eq (mul_one _)) L
    _ ≤ H := hbudget

/-- All four corner products have one common bound, including the
diagonal block where one corner reverses the node order. -/
theorem tailGreen_four_node_product_bounds {w u g r H : ℕ → ℝ}
    (hg : ∀ k, 0 ≤ g k) (hH : ∀ k, 0 ≤ H k)
    (hr₀ : ∀ k, 0 ≤ r k) (hr₁ : ∀ k, r k ≤ 1)
    (hΓ : ∀ m n, m ≤ n → |w m * u n| ≤ g m * ∏ k ∈ Finset.Ico m n, r k)
    (hbase : ∀ m, g m ≤ H m) (hshift : ∀ m, g (m + 1) ≤ H m * r m)
    (hreverse : ∀ m, |w (m + 1) * u m| ≤ H m)
    {m n : ℕ} (hmn : m ≤ n) :
    |w m * u n| ≤ H m * ∏ k ∈ Finset.Ico m n, r k ∧
    |w m * u (n + 1)| ≤ H m * ∏ k ∈ Finset.Ico m n, r k ∧
    |w (m + 1) * u n| ≤ H m * ∏ k ∈ Finset.Ico m n, r k ∧
    |w (m + 1) * u (n + 1)| ≤ H m * ∏ k ∈ Finset.Ico m n, r k := by
  have hp := tailGreen_prod_Ico_succ_le hr₀ hr₁ hmn
  refine ⟨(hΓ m n hmn).trans
    (mul_le_mul_of_nonneg_right (hbase m) (Finset.prod_nonneg fun k _ => hr₀ k)), ?_, ?_, ?_⟩
  · calc
      |w m * u (n + 1)| ≤ g m * ∏ k ∈ Finset.Ico m (n + 1), r k :=
        hΓ m (n + 1) (hmn.trans (Nat.le_succ n))
      _ ≤ g m * ∏ k ∈ Finset.Ico m n, r k := mul_le_mul_of_nonneg_left hp (hg m)
      _ ≤ H m * ∏ k ∈ Finset.Ico m n, r k :=
        mul_le_mul_of_nonneg_right (hbase m) (Finset.prod_nonneg fun k _ => hr₀ k)
  · rcases lt_or_eq_of_le hmn with hlt | rfl
    · exact tailGreen_shifted_node_product_bound hr₀ hΓ hshift hlt
    · simpa using hreverse m
  · exact (tailGreen_shifted_node_product_bound hr₀ hΓ hshift
      (hmn.trans_lt (Nat.lt_succ_self n))).trans
      (mul_le_mul_of_nonneg_left hp (hH m))

/-- Two Poisson interpolation coefficients bounded by two amplify a
common four-corner product bound by at most sixteen. -/
theorem tailGreen_two_interpolants_product_le
    {a₀ a₁ b₀ b₁ α₀ α₁ β₀ β₁ H : ℝ}
    (hα₀ : |α₀| ≤ 2) (hα₁ : |α₁| ≤ 2)
    (hβ₀ : |β₀| ≤ 2) (hβ₁ : |β₁| ≤ 2)
    (h₀₀ : |a₀ * b₀| ≤ H) (h₀₁ : |a₀ * b₁| ≤ H)
    (h₁₀ : |a₁ * b₀| ≤ H) (h₁₁ : |a₁ * b₁| ≤ H) :
    |(a₀ * α₀ + a₁ * α₁) * (b₀ * β₀ + b₁ * β₁)| ≤ 16 * H := by
  have ha : |a₀ * α₀ + a₁ * α₁| ≤ 2 * (|a₀| + |a₁|) := by
    calc
      _ ≤ |a₀ * α₀| + |a₁ * α₁| := abs_add _ _
      _ ≤ |a₀| * 2 + |a₁| * 2 := by
        simpa only [abs_mul] using add_le_add
          (mul_le_mul_of_nonneg_left hα₀ (abs_nonneg a₀))
          (mul_le_mul_of_nonneg_left hα₁ (abs_nonneg a₁))
      _ = _ := by ring
  have hb : |b₀ * β₀ + b₁ * β₁| ≤ 2 * (|b₀| + |b₁|) := by
    calc
      _ ≤ |b₀ * β₀| + |b₁ * β₁| := abs_add _ _
      _ ≤ |b₀| * 2 + |b₁| * 2 := by
        simpa only [abs_mul] using add_le_add
          (mul_le_mul_of_nonneg_left hβ₀ (abs_nonneg b₀))
          (mul_le_mul_of_nonneg_left hβ₁ (abs_nonneg b₁))
      _ = _ := by ring
  rw [abs_mul]
  apply (mul_le_mul ha hb (abs_nonneg _)
    (mul_nonneg (by norm_num) (add_nonneg (abs_nonneg _) (abs_nonneg _)))).trans
  rw [abs_mul] at h₀₀ h₀₁ h₁₀ h₁₁
  nlinarith only [h₀₀, h₀₁, h₁₀, h₁₁]

end ContinuousFlexibility.Radial
