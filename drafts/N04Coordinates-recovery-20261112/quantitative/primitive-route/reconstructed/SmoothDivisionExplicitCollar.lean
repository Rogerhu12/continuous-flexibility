import ContinuousFlexibility.Analysis.SmoothDivisionBounds
import Mathlib.Analysis.Calculus.MeanValue

/-!
# An explicit collar from the actual first jet of a divided factor

The harmonic radius has an exact inverse cost. Its derivative bound is
derived from the true simple-zero division integral when that input is
available; no final positive-collar estimate is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

def simpleZeroExplicitCollarRadius (ρ κ M : ℝ) : ℝ :=
  (ρ⁻¹ + 2 * (M + 1) * κ⁻¹)⁻¹

theorem simpleZeroExplicitCollarRadius_bounds
    {ρ κ M : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ) (hM : 0 ≤ M) :
    0 < simpleZeroExplicitCollarRadius ρ κ M ∧
      simpleZeroExplicitCollarRadius ρ κ M ≤ ρ ∧
      simpleZeroExplicitCollarRadius ρ κ M * M ≤ κ / 2 ∧
      (simpleZeroExplicitCollarRadius ρ κ M)⁻¹ = ρ⁻¹ + 2 * (M + 1) * κ⁻¹ := by
  have hterm : 0 < 2 * (M + 1) * κ⁻¹ := by positivity
  have hden : 0 < ρ⁻¹ + 2 * (M + 1) * κ⁻¹ := add_pos (inv_pos.mpr hρ) hterm
  let δ := simpleZeroExplicitCollarRadius ρ κ M
  have hδ : 0 < δ := inv_pos.mpr hden
  have hδρ : δ ≤ ρ :=
    (inv_anti₀ (inv_pos.mpr hρ) (le_add_of_nonneg_right hterm.le)).trans_eq (inv_inv ρ)
  have hδκ : δ ≤ κ / (2 * (M + 1)) := by
    have hi := inv_anti₀ hterm (le_add_of_nonneg_left (inv_nonneg.mpr hρ.le))
    have he : (2 * (M + 1) * κ⁻¹)⁻¹ = κ / (2 * (M + 1)) := by
      rw [mul_inv_rev, inv_inv, div_eq_mul_inv]
    exact hi.trans_eq he
  have hδM : δ * M ≤ κ / 2 := by
    have he := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (M + 1))).mp hδκ
    nlinarith only [he, hδ.le]
  refine ⟨hδ, hδρ, hδM, ?_⟩
  change (ρ⁻¹ + 2 * (M + 1) * κ⁻¹)⁻¹⁻¹ = _
  exact inv_inv _

/-- A bound on the actual first derivative fixes a positive collar with
the displayed inverse width, before any higher order is requested. -/
theorem explicit_positive_collar_of_deriv_bound
    {g : ℝ → ℝ} {ρ κ M : ℝ}
    (hρ : 0 < ρ) (hκ : 0 < κ) (hM : 0 ≤ M) (hg0 : κ ≤ g 0)
    (hg : ∀ t ∈ Icc (0 : ℝ) ρ, DifferentiableAt ℝ g t)
    (hbound : ∀ t ∈ Icc (0 : ℝ) ρ, |deriv g t| ≤ M) :
    ∀ t ∈ Icc (0 : ℝ) (simpleZeroExplicitCollarRadius ρ κ M),
      κ / 2 ≤ g t ∧ g t ≤ g 0 + κ / 2 := by
  obtain ⟨hδ, hδρ, hδM, hinv⟩ := simpleZeroExplicitCollarRadius_bounds hρ hκ hM
  intro t ht
  have htρ : t ∈ Icc (0 : ℝ) ρ := ⟨ht.1, ht.2.trans hδρ⟩
  have he : |g t - g 0| ≤ M * t := by
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] using
      (convex_Icc (0 : ℝ) ρ).norm_image_sub_le_of_norm_deriv_le hg
        (fun x hx => by simpa only [Real.norm_eq_abs] using hbound x hx)
        (left_mem_Icc.mpr hρ.le) htρ
  have hMt : M * t ≤ κ / 2 :=
    (mul_le_mul_of_nonneg_left ht.2 hM).trans
      (by simpa only [mul_comm] using hδM)
  have habs := abs_le.mp (he.trans hMt)
  constructor <;> linarith only [habs.1, habs.2, hg0]

/-- The second derivative of the undivided function bounds the first
derivative of the same S05 factor, uniformly as the collar shrinks. -/
theorem smoothDivision_explicit_positive_collar
    {f g : ℝ → ℝ} {ρ κ M : ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfactor : ∀ t, f t = t * g t)
    (hρ : 0 < ρ) (hκ : 0 < κ) (hM : 0 ≤ M) (hg0 : κ ≤ g 0)
    (hbound : ∀ t ∈ Icc (0 : ℝ) ρ, |iteratedDeriv 2 f t| ≤ M) :
    ∀ t ∈ Icc (0 : ℝ) (simpleZeroExplicitCollarRadius ρ κ M),
      κ / 2 ≤ g t ∧ g t ≤ g 0 + κ / 2 := by
  apply explicit_positive_collar_of_deriv_bound hρ hκ hM hg0
    (fun t _ => hg.differentiable (by simp) t)
  intro t ht
  simpa only [iteratedDeriv_one] using
    norm_iteratedDeriv_smoothDivisionFactor_le hf hg hfactor 1 hM ht hbound

/-- The exact inverse width remains polynomial when the three genuine
numerical inputs have polynomial bounds in a normalized material weight.
-/
theorem simpleZeroExplicitCollarRadius_inverse_polynomial
    {ρ κ M E Kρ Kκ KM a b c : ℝ}
    (hE : 1 ≤ E) (hKρ : 0 ≤ Kρ) (hKκ : 0 ≤ Kκ) (hKM : 0 ≤ KM)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hρ : ρ⁻¹ ≤ Kρ * E ^ a) (hκ : κ⁻¹ ≤ Kκ * E ^ b)
    (hκpos : 0 < κ) (hM : 0 ≤ M) (hMb : M ≤ KM * E ^ c) :
    (simpleZeroExplicitCollarRadius ρ κ M)⁻¹ ≤
      (Kρ + 2 * (KM + 1) * Kκ) * E ^ (a + b + c) := by
  have hEp : 0 < E := zero_lt_one.trans_le hE
  have hMc : M + 1 ≤ (KM + 1) * E ^ c := by
    have he := Real.one_le_rpow hE hc
    nlinarith only [hMb, he]
  have hprod : (M + 1) * κ⁻¹ ≤ (KM + 1) * Kκ * E ^ (b + c) := by
    calc
      _ ≤ ((KM + 1) * E ^ c) * (Kκ * E ^ b) :=
        mul_le_mul hMc hκ (inv_nonneg.mpr hκpos.le) (by positivity)
      _ = _ := by rw [Real.rpow_add hEp]; ring
  have hraiseA : E ^ a ≤ E ^ (a + b + c) :=
    Real.rpow_le_rpow_of_exponent_le hE (by linarith only [hb, hc])
  have hraiseBC : E ^ (b + c) ≤ E ^ (a + b + c) :=
    Real.rpow_le_rpow_of_exponent_le hE (by linarith only [ha])
  have hfirst := hρ.trans (mul_le_mul_of_nonneg_left hraiseA hKρ)
  have hsecond := hprod.trans
    (mul_le_mul_of_nonneg_left hraiseBC (by positivity : 0 ≤ (KM + 1) * Kκ))
  change (ρ⁻¹ + 2 * (M + 1) * κ⁻¹)⁻¹⁻¹ ≤ _
  rw [inv_inv]
  nlinarith only [hfirst, hsecond]

end ContinuousFlexibility.Analysis
