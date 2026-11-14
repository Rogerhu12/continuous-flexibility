module

public import ContinuousFlexibility.Statements.Radial
public import ContinuousFlexibility.Radial.WeightKernelBounds

/-!
# Scalar scales for good points near the right endpoint

The lower endpoint-distance estimate forces every cell meeting a thin right
band to have large physical index.  The cubic output weight then dominates
the fixed coefficient weight uniformly on that band.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Real

theorem n01a_gaussian_lt {δ N : ℝ} (hδ : 0 < δ)
    (hN : 1 + |Real.log δ| ≤ N) : Real.exp (-N ^ 2) < δ := by
  have hN1 : 1 ≤ N := by linarith [abs_nonneg (Real.log δ)]
  have hN2 : N ≤ N ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hN1) (zero_le_one.trans hN1)]
  calc
    Real.exp (-N ^ 2) < Real.exp (Real.log δ) := by
      apply Real.exp_lt_exp.mpr
      linarith [neg_abs_le (Real.log δ)]
    _ = δ := Real.exp_log hδ

theorem n01a_right_band_mem_core {D : ReferenceData} {p N r : ℝ}
    (hp : p ∈ radialCore D) (hN : 1 + |Real.log (D.b - p)| ≤ N)
    (hr : r ∈ Icc (D.b - Real.exp (-N ^ 2))
      (D.b - (1 / 2 : ℝ) * Real.exp (-N ^ 2))) :
    r ∈ radialCore D ∧ p ≤ r := by
  have he := n01a_gaussian_lt (sub_pos.mpr hp.2) hN
  have hepos := Real.exp_pos (-N ^ 2)
  exact ⟨⟨by linarith [hp.1, hr.1], by linarith [hr.2]⟩,
    by linarith [hr.1]⟩

/-- The harmless `+1` in the profile distance estimate costs only a fixed
threshold in the real band depth. -/
theorem n01a_index_ge_half_depth {C N n : ℝ} (hC : 0 < C) (hn : 0 ≤ n)
    (hN : 4 * (|Real.log C| + 2) ≤ N)
    (h : C⁻¹ * Real.exp (-(n + 1) ^ 2) ≤ Real.exp (-N ^ 2)) :
    N / 2 ≤ n := by
  have hlog := Real.log_le_log
    (mul_pos (inv_pos.mpr hC) (Real.exp_pos (-(n + 1) ^ 2))) h
  rw [Real.log_mul (inv_pos.mpr hC).ne' (Real.exp_pos _).ne',
    Real.log_inv, Real.log_exp, Real.log_exp] at hlog
  have hsq : N ^ 2 ≤ (n + 1) ^ 2 + Real.log C := by linarith
  have hN8 : 8 ≤ N := by linarith [abs_nonneg (Real.log C)]
  have hlogN : Real.log C ≤ N / 4 - 2 := by
    linarith [le_abs_self (Real.log C)]
  by_contra hnot
  have hnlt : n < N / 2 := lt_of_not_ge hnot
  have hpow : (n + 1) ^ 2 ≤ (N / 2 + 1) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hN2 : 4 * N ≤ N ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ N - 4 by linarith)
      (show 0 ≤ N by linarith)]
  nlinarith

theorem n01a_cell_index_ge_half_depth {D : ReferenceData} {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C) {N : ℝ}
    (hN : 4 * (|Real.log (C 0)| + 2) ≤ N) {m : ℕ} {r : ℝ}
    (hm : r ∈ D.cells m) (hr : D.b - Real.exp (-N ^ 2) ≤ r) :
    N / 2 ≤ (D.cellIndex m : ℝ) := by
  apply n01a_index_ge_half_depth (hD.2.2.1 0) (Nat.cast_nonneg _) hN
  exact ((hD.2.2.2.2.2.2.1 m r hm).1.trans (min_le_right _ _)).trans
    (by linarith)

/-- A fixed positive cubic output weight absorbs the actual coefficient
weight at every index at least half the real band depth. -/
theorem n01a_output_weight_on_deep_cells {γ : ℝ} (hγ : 0 < γ) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℝ) (n : ℕ), 0 ≤ N → N / 2 ≤ (n : ℝ) →
      1 ≤ (C * Real.exp (-(γ / 12) * N ^ 3)) *
        Real.exp (-2 * M * radialQ n + 2 * γ * radialS n) := by
  obtain ⟨A, hA⟩ := Radial.absorb_radialQ (2 * M) γ hγ
  refine ⟨Real.exp A, Real.exp_pos A, fun N n hN hn => ?_⟩
  have hQ0 : radialQ 0 = 0 := by
    simp only [radialQ, Nat.cast_zero,
      Real.zero_rpow (by norm_num : (5 / 2 : ℝ) ≠ 0), zero_mul]
  have hq := hA 0 n
  simp only [hQ0, sub_zero, Radial.radialS_zero, zero_sub, abs_neg,
    abs_of_nonneg (Radial.radialS_nonneg n)] at hq
  have hpow := pow_le_pow_left₀ (show 0 ≤ N / 2 by positivity) hn 3
  have hs : N ^ 3 / 12 ≤ radialS n := by
    unfold radialS
    nlinarith only [hpow]
  have hγs := mul_le_mul_of_nonneg_left hs hγ.le
  have he : Real.exp ((γ / 12) * N ^ 3) ≤
      Real.exp A * Real.exp (-2 * M * radialQ n + 2 * γ * radialS n) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hq, hγs]
  calc
    1 = Real.exp ((γ / 12) * N ^ 3) * Real.exp (-(γ / 12) * N ^ 3) := by
      rw [← Real.exp_add]
      rw [show (γ / 12) * N ^ 3 + -(γ / 12) * N ^ 3 = 0 by ring, Real.exp_zero]
    _ ≤ (Real.exp A * Real.exp (-2 * M * radialQ n + 2 * γ * radialS n)) *
        Real.exp (-(γ / 12) * N ^ 3) :=
      mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = _ := by ring

theorem n01a_gaussian_loss_absorbed {c N : ℝ} (hc : 0 < c)
    (hN : 2 / c ≤ N) :
    Real.exp (N ^ 2 - c * N ^ 3) ≤ Real.exp (-(c / 2) * N ^ 3) := by
  have hcN : 2 ≤ N * c := (div_le_iff₀ hc).mp hN
  have h := mul_le_mul_of_nonneg_right hcN (sq_nonneg N)
  apply Real.exp_le_exp.mpr
  nlinarith only [h]

end ContinuousFlexibility.Statements
