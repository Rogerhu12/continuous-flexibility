module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Fixed-power growth of scalar power jets

If a positive scalar lies between two fixed powers of a component
weight, every derivative of a fixed real power has a bound by another
fixed power. This applies in particular to the reciprocal and square
root in the actual characteristic speed on an optical collar.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

theorem rpow_polynomial_bound_of_interval
    {lam A P Q : ℝ} (hlam : 0 < lam) (hA : 0 ≤ A) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (r : ℝ) :
    ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧ ∀ E x : ℝ, 1 ≤ E →
      lam * E ^ (-P) ≤ x → x ≤ A * E ^ Q → x ^ r ≤ C * E ^ R := by
  by_cases hr : 0 ≤ r
  · refine ⟨A ^ r, Q * r, Real.rpow_nonneg hA _, mul_nonneg hQ hr,
      fun E x hE hlo hhi => ?_⟩
    have hE₀ : 0 < E := zero_lt_one.trans_le hE
    have hx : 0 < x := (mul_pos hlam (Real.rpow_pos_of_pos hE₀ _)).trans_le hlo
    calc
      x ^ r ≤ (A * E ^ Q) ^ r := Real.rpow_le_rpow hx.le hhi hr
      _ = A ^ r * E ^ (Q * r) := by
        rw [Real.mul_rpow hA (Real.rpow_nonneg hE₀.le _), ← Real.rpow_mul hE₀.le]
  · have hr' : r ≤ 0 := (lt_of_not_ge hr).le
    refine ⟨lam ^ r, (-P) * r, Real.rpow_nonneg hlam.le _,
      mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hP) hr',
      fun E x hE hlo _ => ?_⟩
    have hE₀ : 0 < E := zero_lt_one.trans_le hE
    calc
      x ^ r ≤ (lam * E ^ (-P)) ^ r :=
        Real.rpow_le_rpow_of_nonpos (mul_pos hlam (Real.rpow_pos_of_pos hE₀ _)) hlo hr'
      _ = lam ^ r * E ^ ((-P) * r) := by
        rw [Real.mul_rpow hlam.le (Real.rpow_nonneg hE₀.le _), ← Real.rpow_mul hE₀.le]

theorem iteratedDeriv_rpow_polynomial_bound
    {lam A P Q : ℝ} (hlam : 0 < lam) (hA : 0 ≤ A) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (r : ℝ) (n : ℕ) :
    ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧ ∀ E x : ℝ, 1 ≤ E →
      lam * E ^ (-P) ≤ x → x ≤ A * E ^ Q →
      |iteratedDeriv n (fun t : ℝ => t ^ r) x| ≤ C * E ^ R := by
  obtain ⟨C, R, hC, hR, hb⟩ := rpow_polynomial_bound_of_interval hlam hA hP hQ (r - n)
  refine ⟨|(descPochhammer ℝ n).eval r| * C, R,
    mul_nonneg (abs_nonneg _) hC, hR, fun E x hE hlo hhi => ?_⟩
  have hE₀ : 0 < E := zero_lt_one.trans_le hE
  have hx : 0 < x := (mul_pos hlam (Real.rpow_pos_of_pos hE₀ _)).trans_le hlo
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hx.le _)]
  exact (mul_le_mul_of_nonneg_left (hb E x hE hlo hhi) (abs_nonneg _)).trans_eq
    (mul_assoc _ _ _).symm

theorem iteratedDeriv_sqrt_polynomial_bound
    {lam A P Q : ℝ} (hlam : 0 < lam) (hA : 0 ≤ A) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (n : ℕ) :
    ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧ ∀ E x : ℝ, 1 ≤ E →
      lam * E ^ (-P) ≤ x → x ≤ A * E ^ Q →
      |iteratedDeriv n Real.sqrt x| ≤ C * E ^ R := by
  have heq : Real.sqrt = fun t : ℝ => t ^ (1 / 2 : ℝ) := funext Real.sqrt_eq_rpow
  rw [heq]
  exact iteratedDeriv_rpow_polynomial_bound hlam hA hP hQ (1 / 2 : ℝ) n

theorem iteratedDeriv_inv_polynomial_bound
    {lam A P Q : ℝ} (hlam : 0 < lam) (hA : 0 ≤ A) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (n : ℕ) :
    ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧ ∀ E x : ℝ, 1 ≤ E →
      lam * E ^ (-P) ≤ x → x ≤ A * E ^ Q →
      |iteratedDeriv n (fun t : ℝ => t⁻¹) x| ≤ C * E ^ R := by
  have heq : (fun t : ℝ => t⁻¹) = fun t => t ^ (-1 : ℝ) := by
    funext t
    exact (Real.rpow_neg_one t).symm
  rw [heq]
  exact iteratedDeriv_rpow_polynomial_bound hlam hA hP hQ (-1 : ℝ) n

end ContinuousFlexibility.Analysis
