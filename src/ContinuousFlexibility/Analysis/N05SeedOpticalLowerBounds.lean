module

public import ContinuousFlexibility.Analysis.N05SeedOpticalLowerTransport

/-!
# A fixed actual-cell power for the retained optical lower constant

The original Morse coefficient costs at most an exponential in the square
of its model index. The proved physical index window converts that loss
to the twelfth power of the actual carrier envelope.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements.MorseChainRealization

open Real
open ContinuousFlexibility.Radial

theorem n05_seed_optical_inverse_bound
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (n : ℕ) (hn : T.index ≤ n) :
    (1372 * D.b ^ 3 * morseChainA T n ^ 3) / morseChainB T n ≤
      (1372 * D.b ^ 3 * (3 : ℝ) ^ 12) * exp (6 * (n : ℝ) ^ 2) := by
  have hd1 : 1 ≤ (T.d n : ℝ) :=
    (one_le_exp_iff.mpr (sq_nonneg (n : ℝ))).trans (h.1 n hn).1
  have hdp : 0 < (T.d n : ℝ) := zero_lt_one.trans_le hd1
  have hB : 0 < morseChainB T n := (h.retained_data false n hn).1
  have hA := (morseChainA_inv_bounds T n hd1).2
  have hb : 0 < D.b := h.geometry.1.trans h.geometry.2.1
  have hquot : morseChainA T n ^ 3 / morseChainB T n ≤
      (9 : ℝ) ^ 3 * (T.d n : ℝ) ^ 6 := by
    apply (div_le_iff₀ hB).mpr
    calc
      morseChainA T n ^ 3 ≤ (9 * (T.d n : ℝ)⁻¹) ^ 3 :=
        pow_le_pow_left₀ (sq_nonneg _) hA 3
      _ = (9 : ℝ) ^ 3 * (T.d n : ℝ) ^ 6 * morseChainB T n := by
        rw [morseChainB_inv_pow T n hdp.le]
        field_simp [hdp.ne']
        <;> ring
  have hdUpper : (T.d n : ℝ) ≤ 3 * exp ((n : ℝ) ^ 2) := by
    rw [h.d_eq n hn]
    have hd := (morseChainInteger_lt n).le
    have he := one_le_exp_iff.mpr (sq_nonneg (n : ℝ))
    linarith only [hd, he]
  have hdPow : (T.d n : ℝ) ^ 6 ≤
      (3 : ℝ) ^ 6 * exp (6 * (n : ℝ) ^ 2) := by
    calc
      (T.d n : ℝ) ^ 6 ≤ (3 * exp ((n : ℝ) ^ 2)) ^ 6 :=
        pow_le_pow_left₀ hdp.le hdUpper 6
      _ = (3 : ℝ) ^ 6 * exp (6 * (n : ℝ) ^ 2) := by
        rw [mul_pow, ← exp_nat_mul, Nat.cast_ofNat]
  calc
    (1372 * D.b ^ 3 * morseChainA T n ^ 3) / morseChainB T n =
        (1372 * D.b ^ 3) * (morseChainA T n ^ 3 / morseChainB T n) := by ring
    _ ≤ (1372 * D.b ^ 3) * ((9 : ℝ) ^ 3 * (T.d n : ℝ) ^ 6) :=
      mul_le_mul_of_nonneg_left hquot (by positivity)
    _ ≤ (1372 * D.b ^ 3) * ((9 : ℝ) ^ 3 *
        ((3 : ℝ) ^ 6 * exp (6 * (n : ℝ) ^ 2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdPow (by positivity))
        (by positivity)
    _ = (1372 * D.b ^ 3 * (3 : ℝ) ^ 12) * exp (6 * (n : ℝ) ^ 2) := by ring

end ContinuousFlexibility.Statements.MorseChainRealization

namespace ContinuousFlexibility.Radial.SeedReferenceConstruction

open Set Real
open ContinuousFlexibility.Statements

variable {q : ℝ} (P : SeedReferenceConstruction q)

/-- The reciprocal of the actual scaled optical lower constant is bounded
on every possible carrier, with constants chosen before the component. -/
theorem n05_tail_optical_coefficient_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (side : Bool) (n j : ℕ),
      P.selected.chain.index ≤ n →
      Icc (P.n05ModelLeft side n) (P.n05ModelRight side n) ⊆
        radialTailInterval (P.selected.family P.selected.sigma) side
          (P.selected.entry side P.selected.chain.index) →
      (Ioo (P.n05TailScale side * P.n05ModelLeft side n)
        (P.n05TailScale side * P.n05ModelRight side n) ∩ P.reference.cells j).Nonempty →
      (P.n05TailScale side) ^ 3 *
          ((1372 * (P.selected.family P.selected.sigma).b ^ 3 *
            morseChainA P.selected.chain n ^ 3) / morseChainB P.selected.chain n) ≤
        B * radialE (P.reference.cellIndex j) ^ (12 : ℝ) := by
  obtain ⟨N, hN⟩ := P.n05_tail_model_index_le_actual
  let B₀ : ℝ := 1372 * (P.selected.family P.selected.sigma).b ^ 3 * (3 : ℝ) ^ 12
  let B : ℝ := P.glued.radiusR ^ 3 * B₀ * exp (12 * (N : ℝ) ^ 2)
  have hb : 0 < (P.selected.family P.selected.sigma).b :=
    P.realization.geometry.1.trans P.realization.geometry.2.1
  have hRR : 0 < P.glued.radiusR := P.glued.radiusL_pos.trans_le P.glued.radius_order
  have hB₀ : 0 < B₀ := by dsimp only [B₀]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B, hB, fun side n j hn hclosed hmeeting => ?_⟩
  obtain ⟨y, hyI, hyj⟩ := hmeeting
  let scale : ℝ := P.n05TailScale side
  let r : ℝ := y / scale
  have hs : 0 < scale := P.n05TailScale_pos side
  have hr : r ∈ Ioo (P.n05ModelLeft side n) (P.n05ModelRight side n) := by
    constructor
    · apply (lt_div_iff₀ hs).mpr
      simpa only [mul_comm] using hyI.1
    · apply (div_lt_iff₀ hs).mpr
      simpa only [mul_comm] using hyI.2
  have hxr : P.n05TailScale side * r = y := by
    change scale * (y / scale) = y
    field_simp [hs.ne']
  obtain ⟨k, hk, hrk⟩ := P.n05_model_cover side hn hr
  have hrj : P.n05TailScale side * r ∈ P.reference.cells j := by
    simpa only [hxr] using hyj
  have hindex : n ≤ P.reference.cellIndex j + N := by
    simpa only [hk] using hN side k j r (hclosed (Ioo_subset_Icc_self hr)) hrk hrj
  have hindexR : (n : ℝ) ≤ (P.reference.cellIndex j : ℝ) + N := by
    exact_mod_cast hindex
  have hsq : (n : ℝ) ^ 2 ≤ 2 * (P.reference.cellIndex j : ℝ) ^ 2 + 2 * (N : ℝ) ^ 2 := by
    have hs := pow_le_pow_left₀ (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hindexR 2
    nlinarith only [hs, sq_nonneg ((P.reference.cellIndex j : ℝ) - N)]
  have hq := radial_nat_sq_le_Q (P.reference.cellIndex j)
  have hexp : exp (6 * (n : ℝ) ^ 2) ≤
      exp (12 * (N : ℝ) ^ 2) * radialE (P.reference.cellIndex j) ^ (12 : ℝ) := by
    calc
      exp (6 * (n : ℝ) ^ 2) ≤
          exp (12 * (N : ℝ) ^ 2 + 12 * radialQ (P.reference.cellIndex j)) :=
        exp_le_exp.mpr (by linarith only [hsq, hq])
      _ = exp (12 * (N : ℝ) ^ 2) * radialE (P.reference.cellIndex j) ^ (12 : ℝ) := by
        rw [exp_add, radialE, ← exp_mul]
        congr 2
        ring
  have hquot := P.realization.n05_seed_optical_inverse_bound n hn
  have hscale : (P.n05TailScale side) ^ 3 ≤ P.glued.radiusR ^ 3 :=
    pow_le_pow_left₀ (P.n05TailScale_pos side).le (P.n05TailScale_le side) 3
  calc
    (P.n05TailScale side) ^ 3 *
        ((1372 * (P.selected.family P.selected.sigma).b ^ 3 *
          morseChainA P.selected.chain n ^ 3) / morseChainB P.selected.chain n) ≤
        (P.n05TailScale side) ^ 3 * (B₀ * exp (6 * (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hquot (by positivity)
    _ ≤ P.glued.radiusR ^ 3 *
        (B₀ * (exp (12 * (N : ℝ) ^ 2) *
          radialE (P.reference.cellIndex j) ^ (12 : ℝ))) :=
      mul_le_mul hscale (mul_le_mul_of_nonneg_left hexp hB₀.le)
        (by positivity) (by positivity)
    _ = B * radialE (P.reference.cellIndex j) ^ (12 : ℝ) := by
      dsimp only [B]
      ring

end ContinuousFlexibility.Radial.SeedReferenceConstruction
