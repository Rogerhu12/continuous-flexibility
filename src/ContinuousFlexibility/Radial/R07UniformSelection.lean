import ContinuousFlexibility.Radial.R07BandSelection
import ContinuousFlexibility.Radial.R07JoinSmallness
import ContinuousFlexibility.Radial.MorseChainGeometry

/-!
# A height tolerance and join threshold before the chain is chosen

The count majorant sums over every natural index. Its tolerance therefore
depends only on the band constant, not on the starting index or the radius
placement. The physical radius also cancels from the join-transfer action,
because the construction prescribes the join width as a fraction of that
radius. These two observations allow the starting index to be chosen after
the tolerance and before the actual Morse chain is constructed.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped ENNReal Topology

/-- A tolerance fixed before the Morse geometry and its starting index. -/
def r07UniformTolerance (C : ℝ) : ℝ :=
  min (1 / 48) (1 / (768 * ((∑' n, heightBandMajorant C n) + 1)))

theorem r07UniformTolerance_pos {C : ℝ} (hC : 0 ≤ C) : 0 < r07UniformTolerance C := by
  have hS : 0 ≤ ∑' n, heightBandMajorant C n := tsum_nonneg (heightBandMajorant_nonneg hC)
  unfold r07UniformTolerance
  exact lt_min (by norm_num) (by positivity)

theorem r07UniformTolerance_le (C : ℝ) : r07UniformTolerance C ≤ 1 / 48 := min_le_left _ _

/-- The band-count estimate retains its numerical majorant instead of
choosing a chain-dependent existential tolerance. -/
theorem r07_band_weighted_sum_le (T : Statements.MorseChainData) {C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hd : ∀ n, T.index ≤ n → T.d n = morseChainInteger n) :
    ∑' p : R07BandFrequency T C,
      ENNReal.ofReal (192 * (c * exp (-(p.1.1 : ℝ) ^ 2))) ≤
        ENNReal.ofReal (192 * c * (∑' n, heightBandMajorant C n)) := by
  let a : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (192 * (c * exp (-(n : ℝ) ^ 2)))
  let N : ℕ → ℕ := fun n => ⌈Statements.radialFrequencyThreshold T C n⌉₊
  let F : ℕ × ℕ → ℝ≥0∞ := fun q => if T.index ≤ q.1 ∧ q.2 < N q.1 then a q.1 else 0
  have hstep :
      ∑' p : R07BandFrequency T C, ENNReal.ofReal (192 * (c * exp (-(p.1.1 : ℝ) ^ 2))) =
        ∑' p : R07BandFrequency T C, F p.1 := by
    refine tsum_congr (fun p => ?_)
    obtain ⟨_, _, hidx, _, hlt⟩ := p.2
    have hN : p.1.2 < N p.1.1 := Nat.lt_ceil.mpr hlt
    simp only [F, a, hidx, hN, and_self, ite_true]
  have hrow : ∀ n, ∑' j, F (n, j) ≤ ENNReal.ofReal (192 * c * heightBandMajorant C n) := by
    intro n
    by_cases hn : T.index ≤ n
    · have hsum : ∑' j, F (n, j) = ∑ j ∈ Finset.range (N n), a n := by
        rw [tsum_eq_sum (s := Finset.range (N n))]
        · refine Finset.sum_congr rfl (fun j hj => ?_)
          have hj' : j < N n := Finset.mem_range.mp hj
          simp only [F, hn, hj', and_self, ite_true]
        · intro j hj
          have hj' : ¬j < N n := fun h => hj (Finset.mem_range.mpr h)
          simp only [F, hj', and_false, ite_false]
      rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have ht0 : 0 ≤ Statements.radialFrequencyThreshold T C n := by
        have hQ : 0 ≤ Statements.radialQ n := (sq_nonneg _).trans (radial_nat_sq_le_Q n)
        unfold Statements.radialFrequencyThreshold
        positivity
      have hNle : (N n : ℝ) ≤ Statements.radialFrequencyThreshold T C n + 1 :=
        (Nat.ceil_lt_add_one ht0).le
      have ht := radialFrequencyThreshold_le_exp T hC n (hd n hn)
      have he : exp ((n : ℝ) ^ 2 / 2) * exp (-(n : ℝ) ^ 2) = exp (-(n : ℝ) ^ 2 / 2) := by
        rw [← exp_add]
        ring_nf
      have he0 : 0 ≤ exp (-(n : ℝ) ^ 2) := (exp_pos _).le
      have hNe : (N n : ℝ) * exp (-(n : ℝ) ^ 2) ≤ heightBandMajorant C n := by
        calc
          _ ≤ (2 * C * Statements.radialQ n * exp ((n : ℝ) ^ 2 / 2) + 1) * exp (-(n : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right (by linarith) he0
          _ = 2 * C * Statements.radialQ n *
              (exp ((n : ℝ) ^ 2 / 2) * exp (-(n : ℝ) ^ 2)) + exp (-(n : ℝ) ^ 2) := by ring
          _ = _ := by rw [he]; rfl
      calc
        _ = 192 * c * ((N n : ℝ) * exp (-(n : ℝ) ^ 2)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hNe (by positivity)
    · have hzero : ∀ j, F (n, j) = 0 := fun j => by simp only [F, hn, false_and, ite_false]
      simp only [hzero, tsum_zero]
      exact zero_le
  have hsumm := (heightBandMajorant_summable C).mul_left (192 * c)
  calc
    _ = _ := hstep
    _ ≤ ∑' q, F q := ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective F
    _ = ∑' n, ∑' j, F (n, j) := ENNReal.tsum_prod'
    _ ≤ ∑' n, ENNReal.ofReal (192 * c * heightBandMajorant C n) := ENNReal.tsum_le_tsum hrow
    _ = ENNReal.ofReal (∑' n, 192 * c * heightBandMajorant C n) :=
      (ENNReal.ofReal_tsum_of_nonneg
        (fun n => mul_nonneg (by positivity) (heightBandMajorant_nonneg hC n)) hsumm).symm
    _ = _ := by rw [tsum_mul_left]

/-- The same fixed tolerance pays for the conditions at both endpoints
of every canonical chain, whatever its starting index. -/
theorem r07UniformTolerance_two_endpoint_budget (T : Statements.MorseChainData) {C : ℝ}
    (hC : 0 ≤ C) (hd : ∀ n, T.index ≤ n → T.d n = morseChainInteger n) :
    ∑' k : R07MatchingCondition T C,
      ENNReal.ofReal (192 * (r07UniformTolerance C * exp (-(k.2.1.1 : ℝ) ^ 2))) < 1 := by
  let c := r07UniformTolerance C
  let S := ∑' n, heightBandMajorant C n
  have hc : 0 < c := r07UniformTolerance_pos hC
  have hS : 0 ≤ S := tsum_nonneg (heightBandMajorant_nonneg hC)
  have hsmall : c * (768 * (S + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hb := r07_band_weighted_sum_le T hC hc.le hd
  have hnonneg : 0 ≤ 192 * c * S := by positivity
  change (∑' k : Bool × R07BandFrequency T C,
    ENNReal.ofReal (192 * (c * exp (-(k.2.1.1 : ℝ) ^ 2)))) < 1
  rw [ENNReal.tsum_prod', tsum_fintype, Fintype.sum_bool]
  calc
    _ ≤ ENNReal.ofReal (192 * c * S) + ENNReal.ofReal (192 * c * S) := add_le_add hb hb
    _ = ENNReal.ofReal (384 * c * S) := by
      rw [← ENNReal.ofReal_add hnonneg hnonneg]
      congr 1
      ring
    _ < 1 := by
      rw [ENNReal.ofReal_lt_one]
      nlinarith only [hsmall, mul_nonneg hc.le hS, hc]

/-- Exact cancellation of the radius in a connector whose width is a
prescribed fraction of its left endpoint. -/
theorem r07_join_action_cancel_radius {J contrast r₀ r₁ fraction : ℝ}
    (hr₀ : 0 < r₀) (hfraction : 0 ≤ fraction)
    (hwidth : r₁ - r₀ = r₀ * fraction) :
    2 * J * contrast / r₀ * |r₁ - r₀| = 2 * J * contrast * fraction := by
  rw [hwidth, abs_of_nonneg (mul_nonneg hr₀.le hfraction)]
  field_simp [hr₀.ne']

/-- The actual geometric join has a dimensionless action bound, so no
radius-placement constant enters the subsequent starting-index choice. -/
theorem r07_geometry_join_action_le {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (k : ℕ) {J contrast : ℝ}
    (hJ : 0 ≤ J) (hcontrast : 0 ≤ contrast)
    (hr₀ : 0 < T.joinLeft side (T.index + k)) :
    2 * J * contrast / T.joinLeft side (T.index + k) *
        |T.joinRight side (T.index + k) - T.joinLeft side (T.index + k)| ≤
      2 * J * contrast * ((1 / 100 : ℝ) * Statements.morseChainA T (T.index + k) ^ 12) := by
  let A := fun j => Statements.morseChainA T (T.index + j)
  have hA (j : ℕ) : 0 < A j := by
    have hb := (morseChainA_exp_bounds T (T.index + j) (G.d_exact _)).1
    exact (by positivity : (0 : ℝ) < exp (-((T.index + j : ℕ) : ℝ) ^ 2) / 3).trans_le hb
  have hfrac : 0 ≤ morseChainJoinFraction A (1 / 100) k := by
    unfold morseChainJoinFraction
    positivity
  rw [r07_join_action_cancel_radius hr₀ hfrac (G.join_width side k)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold morseChainJoinFraction
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (le_min (hA k).le (hA (k + 1)).le) (min_le_left _ _) 12) (by norm_num)

/-- A single index threshold works for every subsequent geometric
construction, since its transfer action is dimensionless. -/
theorem exists_r07_uniform_join_start {C c : ℝ} (hC : 0 < C) (hc : 0 < c) :
    ∃ N : ℕ, 100 ≤ N ∧ ∀ (T : Statements.MorseChainData),
      (∀ n, T.index ≤ n → T.d n = morseChainInteger n) →
      N ≤ T.index → ∀ n j, T.index < n → Statements.radialFrequencyBand T C n j →
      ∀ contrast fraction : ℝ, 0 ≤ contrast → contrast ≤ exp (6 * (n : ℝ) ^ 2) →
      0 ≤ fraction → fraction ≤ (1 / 100 : ℝ) * Statements.morseChainA T (n - 1) ^ 12 →
        2 * (j : ℝ) ^ 2 * contrast * fraction < c * exp (-(n : ℝ) ^ 2) / 12 := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (r07JoinEnvelope_eventually_small (1 / 100) C 1 hc)
  refine ⟨max N₀ 100, le_max_right _ _, ?_⟩
  intro T hd hstart n j hn hband contrast fraction hcontrast₀ hcontrast hfraction₀ hfraction
  have hn100 : 100 ≤ n := (le_max_right N₀ 100).trans (hstart.trans hn.le)
  have hbound := r07_join_action_le T hC (by norm_num : (0 : ℝ) ≤ 1 / 100)
    (by norm_num : (0 : ℝ) < 1) hd (by omega : 24 ≤ n) hn hband
    hcontrast₀ hcontrast hfraction₀ hfraction
  simp only [div_one] at hbound
  exact hbound.trans_lt (hN₀ n ((le_max_left N₀ 100).trans (hstart.trans hn.le)))

end ContinuousFlexibility.Radial
