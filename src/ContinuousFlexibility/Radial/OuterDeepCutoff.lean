module

public import ContinuousFlexibility.Radial.OuterEndpointDistances

/-!
# One deep cutoff for all frequencies below the transition threshold

The actual entrance distance is of order `A_(n+1)`. Its logarithmic length
therefore satisfies the R07 density-comparison condition simultaneously
for every `2 ≤ j < q_n`, once `n` is large enough. The cutoff is chosen
before the frequency, and both initial resistance conventions are retained.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology
open ContinuousFlexibility.Statements

/-- On a positive annulus, logarithmic tail length is bounded by physical
distance divided by the fixed inner radius. -/
theorem outer_log_tail_length_le_distance {D : ReferenceData}
    (hD : RadialProfileGeometry D) (right : Bool) {r : ℝ} (hr : r ∈ radialCore D) :
    tailPhysicalLog right (tailPhysicalEndpoint D right) - tailPhysicalLog right r ≤
      (if right then D.b - r else r - D.a) / D.a := by
  have hrp : 0 < r := hD.1.trans hr.1
  have hbp : 0 < D.b := hD.1.trans hD.2.1
  cases right with
  | false =>
      change -log D.a - -log r ≤ (r - D.a) / D.a
      have hb := log_le_sub_one_of_pos (div_pos hrp hD.1)
      rw [log_div hrp.ne' hD.1.ne'] at hb
      have he : r / D.a - 1 = (r - D.a) / D.a := by
        field_simp [hD.1.ne'] <;> ring
      rw [he] at hb
      linarith only [hb]
  | true =>
      change log D.b - log r ≤ (D.b - r) / D.a
      calc
        log D.b - log r = log (D.b / r) := (log_div hbp.ne' hrp.ne').symm
        _ ≤ D.b / r - 1 := log_le_sub_one_of_pos (div_pos hbp hrp)
        _ = (D.b - r) / r := by field_simp [hrp.ne'] <;> ring
        _ ≤ _ := div_le_div_of_nonneg_left (sub_nonneg.mpr hr.2.le) hD.1 hr.1.le

/-- The actual R07 density-comparison window is uniform over all frequencies
below the moving upper cutoff. In particular it covers the new initial band. -/
theorem morseTransition_eventually_deepTail_close {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    {Cstar : ℝ} (hCstar : 0 < Cstar) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 2 ≤ j →
      (j : ℝ) < radialFrequencyThreshold M Cstar n → ∀ (right : Bool) (η K : ℝ),
        (r07DeepTailData M D right j (n + 1) η K).endpoint -
          (r07DeepTailData M D right j (n + 1) η K).entrance ≤
            (2 * (j : ℝ) ^ 2)⁻¹ := by
  let L : ℝ := (3 * C 0 * (1 + (9 : ℝ) ^ 12)) / D.a
  let κ : ℝ := sqrt (log 4)
  have hC : 0 < C 0 := h.constants_pos 0
  have ha : 0 < D.a := h.geometry.1
  have hL : 0 < L := by dsimp only [L]; positivity
  have hκ : 0 < κ := sqrt_pos.mpr (log_pos (by norm_num))
  have hε : 0 < κ / (2 * L) := by positivity
  filter_upwards [morseTransition_eventually_deep_of_upper M hCstar
      (fun k hk => h.d_eq k hk) hε,
    morseOuterDeepEntrance_eventually_distance_le h, eventually_ge_atTop M.index]
    with n hsmall hdist hn
  intro j hj hupper right η K
  have hn' : M.index ≤ n + 1 := hn.trans (Nat.le_succ n)
  have hpar := h.retained_data right (n + 1) hn'
  have hA : 0 < morseChainA M (n + 1) :=
    (mul_pos (by norm_num : (0 : ℝ) < 4) hpar.1).trans hpar.2.1
  have hroot : κ ≤ sqrt (log (morseChainA M (n + 1) / morseChainB M (n + 1))) :=
    sqrt_le_sqrt (morseTransition_log_ratio_lower M (n + 1) (h.d_eq (n + 1) hn'))
  have hJA : (j : ℝ) ^ 2 * morseChainA M (n + 1) < (2 * L)⁻¹ := by
    apply (mul_lt_mul_iff_left₀ hκ).mp
    calc
      ((j : ℝ) ^ 2 * morseChainA M (n + 1)) * κ ≤
          (j : ℝ) ^ 2 * morseChainA M (n + 1) *
            sqrt (log (morseChainA M (n + 1) / morseChainB M (n + 1))) :=
        mul_le_mul_of_nonneg_left hroot (mul_nonneg (sq_nonneg _) hA.le)
      _ < κ / (2 * L) := hsmall j hn hupper (n + 1) (Nat.lt_succ_self n)
      _ = (2 * L)⁻¹ * κ := by ring
  have hlen :
      tailPhysicalLog right (tailPhysicalEndpoint D right) -
          tailPhysicalLog right (morseOuterDeepEntrance M right n) ≤
        L * morseChainA M (n + 1) := by
    calc
      _ ≤ (if right then D.b - morseOuterDeepEntrance M right n
          else morseOuterDeepEntrance M right n - D.a) / D.a :=
        outer_log_tail_length_le_distance h.geometry right
          (morseOuterDeepEntrance_mem_core h right n hn)
      _ ≤ ((3 * C 0 * (1 + (9 : ℝ) ^ 12)) * morseChainA M (n + 1)) / D.a :=
        div_le_div_of_nonneg_right (hdist right) ha.le
      _ = _ := by dsimp only [L]; ring
  have hjR : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hjp : 0 < (j : ℝ) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hjR
  have hJ : 0 < 2 * (j : ℝ) ^ 2 := by positivity
  rw [← morsePhysicalDeepTail_eq_r07 h right j n hn η K]
  change tailPhysicalLog right (tailPhysicalEndpoint D right) -
      tailPhysicalLog right (morseOuterDeepEntrance M right n) ≤ (2 * (j : ℝ) ^ 2)⁻¹
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hJ).mpr
  calc
    _ ≤ (L * morseChainA M (n + 1)) * (2 * (j : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hlen hJ.le
    _ = ((j : ℝ) ^ 2 * morseChainA M (n + 1)) * (2 * L) := by ring
    _ ≤ (2 * L)⁻¹ * (2 * L) := mul_le_mul_of_nonneg_right hJA.le (by positivity)
    _ = 1 := inv_mul_cancel₀ (mul_pos (by norm_num) hL).ne'

end ContinuousFlexibility.Radial
