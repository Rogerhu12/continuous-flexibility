import ContinuousFlexibility.Analysis.FiniteTaylorPolynomial
import ContinuousFlexibility.Analysis.RootTaylorPolynomial
import ContinuousFlexibility.Statements.Nonlinear

/-!
# Bounds for the polynomial part of the root substitution

The even root substitution of a finite Taylor polynomial is, on the positive
halfspace, the finite sum of the polynomial extensions of its homogeneous
terms.  Their coefficient norms are controlled by the input jets at the
Taylor center.  This argument does not assume that the input function itself
is smooth, since only its specified finite list of jets is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

/-- The shifted even substitution of a finite Taylor polynomial is the
sum of the polynomial extensions of its homogeneous coefficients. -/
theorem rootEven_finiteTaylorPolynomial_add_eq
    (n : ℕ) (G : ℝ × ℝ × ℝ → ℝ) (x₀ θ₀ : ℝ) (h : ℝ × ℝ)
    (hx : 0 ≤ x₀ + h.1) :
    Statements.rootEven (finiteTaylorPolynomial n G (x₀, 0, θ₀)) ((x₀, θ₀) + h) =
      ∑ k ∈ Finset.range (n + 1),
        rootTaylorPolynomial ((k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k G (x₀, 0, θ₀)) x₀ h := by
  simp only [Statements.rootEven, finiteTaylorPolynomial, Prod.fst_add, Prod.snd_add,
    Prod.mk_sub_mk, add_sub_cancel_left, sub_zero]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  rw [rootTaylorPolynomial_eq_average _ x₀ h hx]
  simp only [smul_apply]

/-- Uniformly on positive base points in the unit interval, the order-`n`
jet of the even substitution of the Taylor polynomial is controlled by
the input jets through order `n` at the Taylor center. -/
theorem exists_rootEven_finiteTaylor_jet_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (G : ℝ × ℝ × ℝ → ℝ) (x₀ θ₀ M : ℝ),
      0 < x₀ → x₀ ≤ 1 →
      (∀ k ≤ n, ‖iteratedFDeriv ℝ k G (x₀, 0, θ₀)‖ ≤ M) →
      ‖iteratedFDeriv ℝ n
        (Statements.rootEven (finiteTaylorPolynomial n G (x₀, 0, θ₀))) (x₀, θ₀)‖ ≤ C * M := by
  classical
  choose C hCpos hC using fun k : ℕ => exists_rootTaylorPolynomial_jet_bound (n := k) n
  have hsum : 0 ≤ ∑ k ∈ Finset.range (n + 1), C k :=
    Finset.sum_nonneg (fun k _ => (hCpos k).le)
  refine ⟨1 + ∑ k ∈ Finset.range (n + 1), C k, by linarith, ?_⟩
  intro G x₀ θ₀ M hx₀ hx₁ hG
  let A : (k : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ × ℝ × ℝ) ℝ :=
    fun k => (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k G (x₀, 0, θ₀)
  let J : ℝ × ℝ → ℝ :=
    fun h => ∑ k ∈ Finset.range (n + 1), rootTaylorPolynomial (A k) x₀ h
  have hM : 0 ≤ M :=
    (norm_nonneg (iteratedFDeriv ℝ 0 G (x₀, 0, θ₀))).trans (hG 0 (Nat.zero_le n))
  have hA (k : ℕ) (hk : k ≤ n) : ‖A k‖ ≤ M := by
    have hfac : (1 : ℝ) ≤ (k.factorial : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos k))
    calc
      ‖A k‖ = (k.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ k G (x₀, 0, θ₀)‖ := by
        rw [A, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
      _ ≤ 1 * ‖iteratedFDeriv ℝ k G (x₀, 0, θ₀)‖ :=
        mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hfac) (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ k G (x₀, 0, θ₀)‖ := one_mul _
      _ ≤ M := hG k hk
  have heq :
      (fun h : ℝ × ℝ =>
        Statements.rootEven (finiteTaylorPolynomial n G (x₀, 0, θ₀)) ((x₀, θ₀) + h))
      =ᶠ[𝓝 (0 : ℝ × ℝ)] J := by
    have hpos : {h : ℝ × ℝ | 0 < x₀ + h.1} ∈ 𝓝 (0 : ℝ × ℝ) :=
      (isOpen_lt continuous_const (continuous_const.add continuous_fst)).mem_nhds
        (by simpa using hx₀)
    filter_upwards [hpos] with h hh
    exact rootEven_finiteTaylorPolynomial_add_eq n G x₀ θ₀ h hh.le
  have hjet :
      iteratedFDeriv ℝ n
        (Statements.rootEven (finiteTaylorPolynomial n G (x₀, 0, θ₀))) (x₀, θ₀) =
      iteratedFDeriv ℝ n J 0 := by
    have h := (heq.iteratedFDeriv ℝ n).self_of_nhds
    simpa only [iteratedFDeriv_comp_add_left, add_zero] using h
  rw [hjet]
  dsimp only [J]
  rw [iteratedFDeriv_fun_sum_apply (fun k _ =>
    ((contDiff_rootTaylorPolynomial (A k) x₀).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt)]
  calc
    ‖∑ k ∈ Finset.range (n + 1),
        iteratedFDeriv ℝ n (rootTaylorPolynomial (A k) x₀) 0‖ ≤
        ∑ k ∈ Finset.range (n + 1),
          ‖iteratedFDeriv ℝ n (rootTaylorPolynomial (A k) x₀) 0‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), C k * M := by
      apply Finset.sum_le_sum
      intro k hk
      exact (hC k (A k) x₀ ⟨hx₀.le, hx₁⟩).trans
        (mul_le_mul_of_nonneg_left (hA k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
          (hCpos k).le)
    _ = (∑ k ∈ Finset.range (n + 1), C k) * M := (Finset.sum_mul ..).symm
    _ ≤ (1 + ∑ k ∈ Finset.range (n + 1), C k) * M :=
      mul_le_mul_of_nonneg_right (by linarith) hM

end ContinuousFlexibility.Analysis
