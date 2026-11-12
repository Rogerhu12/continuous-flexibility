import ContinuousFlexibility.Analysis.OneHighCompositionJets
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Fixed polynomial bounds for the actual logarithm jets

The coefficient is chosen before the numerical envelope and the field.
The positive value, its reciprocal, and the finite positive-order jets
are the only inputs. The zeroth logarithm is included without assuming
a bound on a real angular lift or on any constructed coordinate field.
This is a new reconstruction after the workspace reset.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Real
open scoped BigOperators ContDiff

private theorem log_successor_jet_norm (j : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ (j + 1) Real.log x‖ =
      (j.factorial : ℝ) * |x⁻¹| ^ (j + 1) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_succ',
    Real.deriv_log', iteratedDeriv_eq_iterate, iter_deriv_inv]
  have he : (-1 - (j : ℤ)) = -((j + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [he, zpow_neg, zpow_natCast, ← inv_pow]
  simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_neg, abs_one,
    one_pow, one_mul, abs_of_nonneg (Nat.cast_nonneg j.factorial)]

private theorem log_positive_jet_bound {H x : ℝ} (hx : 0 < x)
    (hInv : x⁻¹ ≤ H) {k : ℕ} (hk : 1 ≤ k) :
    ‖iteratedFDeriv ℝ k Real.log x‖ ≤
      ((k - 1).factorial : ℝ) * H ^ k := by
  have he : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hn := log_successor_jet_norm (k - 1) x
  rw [he, abs_of_pos (inv_pos.mpr hx)] at hn
  rw [hn]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (inv_nonneg.mpr hx.le) hInv k) (Nat.cast_nonneg _)

private theorem log_value_bound {H x : ℝ} (hx : 0 < x)
    (hVal : x ≤ H) (hInv : x⁻¹ ≤ H) : |Real.log x| ≤ H := by
  have hp := Real.log_le_sub_one_of_pos hx
  have hm := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at hm
  exact abs_le.mpr ⟨by linarith only [hm, hInv], by linarith only [hp, hVal]⟩

private def logJetCoefficient (k : ℕ) : ℝ :=
  ∑ π : OrderedFinpartition k, ((π.length - 1).factorial : ℝ)

private theorem logJetCoefficient_nonneg (k : ℕ) : 0 ≤ logJetCoefficient k :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- All constants precede the numerical envelope, the point, and the
actual field. The exponent is displayed uniformly through order `N`. -/
theorem exists_log_finiteJet_polynomial_envelope
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {H : ℝ}, 1 ≤ H → ∀ (f : E → ℝ) (x : E),
      ContDiffAt ℝ ∞ f x → 0 < f x → f x ≤ H → (f x)⁻¹ ≤ H →
      (∀ k, 1 ≤ k → k ≤ N → ‖iteratedFDeriv ℝ k f x‖ ≤ H) →
      ∀ k, k ≤ N →
        ‖iteratedFDeriv ℝ k (fun y => Real.log (f y)) x‖ ≤ C * H ^ (2 * N + 1) := by
  classical
  let C : ℝ := 1 + ∑ j ∈ Finset.range (N + 1), logJetCoefficient j
  have hC : 1 ≤ C := by
    have hp : 0 ≤ ∑ j ∈ Finset.range (N + 1), logJetCoefficient j :=
      Finset.sum_nonneg fun j _ => logJetCoefficient_nonneg j
    dsimp only [C]
    linarith only [hp]
  refine ⟨C, hC, ?_⟩
  intro H hH f x hf hx hVal hInv hraw k hk
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hpow0 : 0 ≤ H ^ (2 * N + 1) := pow_nonneg hH0 _
  by_cases hk0 : k = 0
  · subst k
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    calc
      |Real.log (f x)| ≤ H := log_value_bound hx hVal hInv
      _ ≤ H ^ (2 * N + 1) := by
        simpa only [pow_one] using pow_le_pow_right₀ hH (by omega : 1 ≤ 2 * N + 1)
      _ ≤ C * H ^ (2 * N + 1) :=
        le_mul_of_one_le_left hpow0 hC
  have hpositive : 0 < k := Nat.pos_of_ne_zero hk0
  have hcomp := norm_iteratedFDeriv_comp_le_partition_sum
    (Real.contDiffAt_log.mpr hx.ne') hf k
  have hterm (π : OrderedFinpartition k) :
      ‖iteratedFDeriv ℝ π.length Real.log (f x)‖ *
          ∏ j, ‖iteratedFDeriv ℝ (π.partSize j) f x‖ ≤
        ((π.length - 1).factorial : ℝ) * H ^ (2 * N + 1) := by
    have hout := log_positive_jet_bound hx hInv (π.length_pos hpositive)
    have hprod : (∏ j, ‖iteratedFDeriv ℝ (π.partSize j) f x‖) ≤ H ^ π.length := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun j _ => hraw (π.partSize j) (π.partSize_pos j)
            ((π.partSize_le j).trans hk)))
    calc
      _ ≤ (((π.length - 1).factorial : ℝ) * H ^ π.length) * H ^ π.length :=
        mul_le_mul hout hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hH0 _))
      _ = ((π.length - 1).factorial : ℝ) * H ^ (2 * π.length) := by
        rw [mul_assoc, ← pow_add]
        congr 2
        omega
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hH (by have hp := π.length_le; omega)) (Nat.cast_nonneg _)
  have hcoeff : logJetCoefficient k ≤ C := by
    have hm : k ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    exact (Finset.single_le_sum (fun j _ => logJetCoefficient_nonneg j) hm).trans
      (le_add_of_nonneg_left zero_le_one)
  calc
    _ ≤ ∑ π : OrderedFinpartition k,
        ‖iteratedFDeriv ℝ π.length Real.log (f x)‖ *
          ∏ j, ‖iteratedFDeriv ℝ (π.partSize j) f x‖ := hcomp
    _ ≤ ∑ π : OrderedFinpartition k,
        ((π.length - 1).factorial : ℝ) * H ^ (2 * N + 1) :=
      Finset.sum_le_sum fun π _ => hterm π
    _ = logJetCoefficient k * H ^ (2 * N + 1) := by
      rw [← Finset.sum_mul]
      rfl
    _ ≤ C * H ^ (2 * N + 1) := mul_le_mul_of_nonneg_right hcoeff hpow0

end ContinuousFlexibility.Analysis
