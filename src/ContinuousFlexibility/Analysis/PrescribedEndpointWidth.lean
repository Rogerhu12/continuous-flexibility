import ContinuousFlexibility.Analysis.RadialTaylorSlopeBounds

/-!
# A displayed collar width from finite numerical data

Every width is a finite minimum of positive rational expressions.  In
particular no compactness or choice operation can make it arbitrarily
smaller than its geometric and finite-jet inputs.  The same width is used
for an entire indexed family once those inputs have been bounded.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

def prescribedEndpointWidth (n : ℕ) (span ρ κ M Mslope m : ℝ) : ℝ :=
  min (1 / 2) (min (span / 4) (min (ρ / 2)
    (min (κ / (4 * ((n + 1 : ℕ) : ℝ) * (M + 1)))
      (m / (8 * (Mslope + 1))))))

theorem prescribedEndpointWidth_margins
    (n : ℕ) {span ρ κ M Mslope m : ℝ}
    (hspan : 0 < span) (hρ : 0 < ρ) (hκ : 0 < κ)
    (hM : 0 ≤ M) (hMslope : 0 ≤ Mslope) (hm : 0 < m) :
    let δ := prescribedEndpointWidth n span ρ κ M Mslope m;
    0 < δ ∧ δ < ρ ∧ δ ≤ 1 ∧ 2 * δ < span ∧
      ((n + 1 : ℕ) : ℝ) * M * δ ≤ κ / 2 ∧
      2 * Mslope * δ ≤ m / 2 := by
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  have hN : 0 < N := by
    change (0 : ℝ) < ((n + 1 : ℕ) : ℝ)
    exact_mod_cast Nat.succ_pos n
  have hden : 0 < 4 * N * (M + 1) := by positivity
  have hmassden : 0 < 8 * (Mslope + 1) := by positivity
  let δ := prescribedEndpointWidth n span ρ κ M Mslope m
  have hδ : 0 < δ := by
    dsimp only [δ, prescribedEndpointWidth]
    exact lt_min (by norm_num) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (div_pos hκ hden) (div_pos hm hmassden))))
  have hhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hspanle : δ ≤ span / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hρle : δ ≤ ρ / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hκle : δ ≤ κ / (4 * N * (M + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hmle : δ ≤ m / (8 * (Mslope + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hκprod : δ * (4 * N * (M + 1)) ≤ κ := (le_div_iff₀ hden).mp hκle
  have hmprod : δ * (8 * (Mslope + 1)) ≤ m := (le_div_iff₀ hmassden).mp hmle
  have hNM : N * M * δ ≤ N * (M + 1) * δ :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith : M ≤ M + 1) hN.le) hδ.le
  have hMδ : Mslope * δ ≤ (Mslope + 1) * δ :=
    mul_le_mul_of_nonneg_right (by linarith : Mslope ≤ Mslope + 1) hδ.le
  change 0 < δ ∧ δ < ρ ∧ δ ≤ 1 ∧ 2 * δ < span ∧
    N * M * δ ≤ κ / 2 ∧ 2 * Mslope * δ ≤ m / 2
  refine ⟨hδ, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [hρle, hρ]
  · linarith only [hhalf]
  · linarith only [hspanle, hspan]
  · nlinarith only [hκprod, hNM, hκ]
  · nlinarith only [hmprod, hMδ, hm]

end ContinuousFlexibility.Analysis
