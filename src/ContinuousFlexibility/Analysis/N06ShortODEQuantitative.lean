module

public import ContinuousFlexibility.Analysis.N06ShortODELocal

/-!
# An explicit short radius for the endpoint ODE estimate

The radius is chosen from the actual relative second-derivative bound and
the reciprocal-mass weight.  This converts the local endpoint theorem to
one polynomial lower bound, without an independently assumed collar.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff

private theorem n06_short_radius_estimates
    {K E : ℝ} (hK : 0 ≤ K) (hE : 1 ≤ E) :
    0 < (4 * (1 + K) * E)⁻¹ ∧
      (4 * (1 + K) * E)⁻¹ ≤ 1 ∧
      (4 * (1 + K) * E)⁻¹ ≤ (1 / 2 : ℝ) * E⁻¹ ∧
      K * ((4 * (1 + K) * E)⁻¹) ^ 2 ≤ (1 / 4 : ℝ) := by
  let d : ℝ := 4 * (1 + K) * E
  have hEpos : 0 < E := zero_lt_one.trans_le hE
  have hd : 0 < d := mul_pos (mul_pos (by norm_num) (by linarith)) hEpos
  have hd4 : 4 ≤ d := by
    dsimp only [d]
    nlinarith only [hE, mul_nonneg hK hEpos.le]
  have hdE : 2 * E ≤ d := by
    dsimp only [d]
    nlinarith only [hEpos, mul_nonneg hK hEpos.le]
  have hdK : 4 * K ≤ d := by
    dsimp only [d]
    nlinarith only [hE, mul_nonneg hK (sub_nonneg.mpr hE)]
  have hinv : 0 < d⁻¹ := inv_pos.mpr hd
  have hinv1 : d⁻¹ ≤ 1 := (inv_le_one₀ hd).mpr (by linarith only [hd4])
  have hinvE : d⁻¹ ≤ (1 / 2 : ℝ) * E⁻¹ := by
    calc
      d⁻¹ ≤ (2 * E)⁻¹ := inv_anti₀ (mul_pos (by norm_num) hEpos) hdE
      _ = (1 / 2 : ℝ) * E⁻¹ := by
        field_simp [hEpos.ne']
  have hKinv : K * d⁻¹ ≤ (1 / 4 : ℝ) := by
    have he := mul_le_mul_of_nonneg_right hdK hinv.le
    rw [mul_inv_cancel₀ hd.ne'] at he
    linarith only [he]
  refine ⟨hinv, hinv1, hinvE, ?_⟩
  calc
    K * (d⁻¹) ^ 2 = (K * d⁻¹) * d⁻¹ := by ring
    _ ≤ (1 / 4 : ℝ) * 1 :=
      mul_le_mul hKinv hinv1 hinv.le (by norm_num)
    _ = (1 / 4 : ℝ) := mul_one _

/-- A relative ODE bound, the true reciprocal mass, and the elementary
interior upper bound give a polynomial lower bound at the root. -/
theorem n06_positive_closed_endpoint_polynomial_lower
    {W : ℝ → ℝ} {R K B Q E : ℝ}
    (hB : 0 < B) (hQ : 0 < Q) (hE : 1 ≤ E) (hK : 0 ≤ K)
    (hR : (1 / 2 : ℝ) * E⁻¹ ≤ R)
    (hW : ∀ x ∈ Icc (0 : ℝ) R, ContDiffAt ℝ 2 W x)
    (hpos : ∀ x ∈ Icc (0 : ℝ) R, 0 < W x)
    (hdd : ∀ x ∈ Icc (0 : ℝ) R, |deriv (deriv W) x| ≤ K * W x)
    (hupper : ∀ x ∈ Icc (0 : ℝ) R, 0 < x → W x ≤ B * (1 + x⁻¹))
    (hmass : ∀ t : ℝ, 0 ≤ t → t ≤ R →
      (∫ x in (0 : ℝ)..t, (W x)⁻¹ ^ 2) ≤ Q * E) :
    (64 * B * Q * (1 + K) ^ 2 * E ^ 3)⁻¹ ≤ W 0 := by
  let ℓ : ℝ := (4 * (1 + K) * E)⁻¹
  obtain ⟨hℓ, hℓ1, hℓE, hsmall⟩ := n06_short_radius_estimates hK hE
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hℓR : ℓ ≤ R := hℓE.trans hR
  have hsub : Icc (0 : ℝ) ℓ ⊆ Icc (0 : ℝ) R :=
    fun _ hx => ⟨hx.1, hx.2.trans hℓR⟩
  have hEpos : 0 < E := zero_lt_one.trans_le hE
  have hKone : 0 < 1 + K := by linarith only [hK]
  have hend : W ℓ ≤ 2 * B / ℓ := by
    apply (hupper ℓ ⟨hℓ.le, hℓR⟩ hℓ).trans
    apply (le_div_iff₀ hℓ).mpr
    calc
      B * (1 + ℓ⁻¹) * ℓ = B * ℓ + B := by
        calc
          B * (1 + ℓ⁻¹) * ℓ = B * (ℓ + ℓ⁻¹ * ℓ) := by ring
          _ = B * (ℓ + 1) := by rw [inv_mul_cancel₀ hℓne]
          _ = B * ℓ + B := by ring
      _ ≤ 2 * B := by
        have he := mul_le_mul_of_nonneg_left hℓ1 hB.le
        linarith only [he]
  have hlower := n06_positive_closed_endpoint_lower
    (fun x hx => hW x (hsub hx)) (fun x hx => hpos x (hsub hx))
    hℓ hK hsmall (fun x hx => hdd x (hsub hx))
    (div_pos (mul_pos (by norm_num) hB) hℓ) (mul_pos hQ hEpos)
    hend (hmass ℓ hℓ.le hℓR)
  calc
    (64 * B * Q * (1 + K) ^ 2 * E ^ 3)⁻¹ =
        ℓ / (2 * (2 * B / ℓ) * (Q * E)) := by
      dsimp only [ℓ]
      field_simp [hB.ne', hQ.ne', hEpos.ne', hKone.ne']
      <;> ring
    _ ≤ W 0 := hlower

end ContinuousFlexibility.Analysis
