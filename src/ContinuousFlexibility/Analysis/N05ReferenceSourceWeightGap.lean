import ContinuousFlexibility.Analysis.N05ReferenceWeightComparisons
import ContinuousFlexibility.Analysis.N05MaterialWeights

/-!
# A strict endpoint gap absorbs the actual source weights

A bounded reference-index window changes the physical reference weight by
a fixed coefficient power. The actual sample endpoint weight then leaves
the strictly positive exponent twice the endpoint gap. The prescribed
material envelope absorbs every remaining fixed material power.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

theorem n05_radialS_index_window {B : ℝ} (hB : 0 ≤ B) (i n : ℕ)
    (hwindow : |(i : ℝ) - (n : ℝ)| ≤ B) :
    |radialS i - radialS n| ≤ 6 * B * (B ^ 2 + 1) * (radialQ n + 1) := by
  have h := n05_materialH_log_shift (Nat.cast_nonneg i) hB n hwindow
  have he : Real.log (materialH (i : ℝ)) = -radialS i := by
    rw [materialH, Real.log_exp, radialS]
    ring
  rw [he, show -radialS i + radialS n = -(radialS i - radialS n) by ring,
    abs_neg] at h
  exact h

/-- The source exponential at a nearby cell has a uniformly controlled
coefficient loss at the piece's prescribed reference index. -/
theorem n05_referenceSourceWeight_index_window {B γw : ℝ}
    (hB : 0 ≤ B) (hγw : 0 ≤ γw) (M : ℝ) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ i n : ℕ,
      |(i : ℝ) - (n : ℝ)| ≤ B →
        Real.exp (2 * M * radialQ i + 2 * γw * radialS i) ≤
          C * radialE n ^ A * Real.exp (2 * γw * radialS n) := by
  obtain ⟨L, hL⟩ := Radial.radialQ_sub_le 1 zero_lt_one
  let P : ℝ := 6 * B * (B ^ 2 + 1)
  let Q : ℝ := P + |L| + 1
  let A : ℝ := 2 * |M| * Q + 2 * γw * P
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨Real.exp A, A, Real.exp_pos _, hA, fun i n hwindow => ?_⟩
  have hs : |radialS i - radialS n| ≤ P * (radialQ n + 1) :=
    n05_radialS_index_window hB i n hwindow
  have hdiff : radialQ i - radialQ n ≤ P * (radialQ n + 1) + |L| := by
    calc
      _ ≤ |radialQ i - radialQ n| := le_abs_self _
      _ ≤ |radialS i - radialS n| + L := by simpa only [one_mul] using hL i n
      _ ≤ P * (radialQ n + 1) + |L| := add_le_add hs (le_abs_self L)
  have hn : 0 ≤ radialQ n := Radial.radialQ_nonneg n
  have hi : 0 ≤ radialQ i := Radial.radialQ_nonneg i
  have hqbound : radialQ i ≤ Q * (radialQ n + 1) := by
    dsimp only [Q]
    nlinarith only [hdiff, mul_nonneg (abs_nonneg L) hn]
  have hsbound : radialS i ≤ radialS n + P * (radialQ n + 1) := by
    have hd := (le_abs_self (radialS i - radialS n)).trans hs
    linarith only [hd]
  have hm : 2 * M * radialQ i ≤ 2 * |M| * radialQ i :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_abs_self M) (by norm_num)) hi
  have hexp : 2 * M * radialQ i + 2 * γw * radialS i ≤
      A * (radialQ n + 1) + 2 * γw * radialS n := by
    have hmq := mul_le_mul_of_nonneg_left hqbound (by positivity : 0 ≤ 2 * |M|)
    have hsg := mul_le_mul_of_nonneg_left hsbound (by positivity : 0 ≤ 2 * γw)
    dsimp only [A]
    nlinarith only [hm, hmq, hsg]
  calc
    _ ≤ Real.exp (A * (radialQ n + 1) + 2 * γw * radialS n) :=
      Real.exp_le_exp.mpr hexp
    _ = _ := by
      rw [radialE, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

/-- The actual sample weights absorb every fixed source coefficient loss
whenever the physical reference exponent is strictly below the canonical
endpoint exponent. -/
theorem n05_referenceSourceWeight_sample_gap_bound
    {D : ReferenceData} {T : MaterialData} (hD : IsAccumulatingProfile D)
    (hT : IsMaterialData D T) {B γw γ A : ℝ}
    (hB : 0 ≤ B) (hγw : 0 ≤ γw) (hgap : γw < γ) (hA : 0 ≤ A)
    (t M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j i : ℕ,
      |(i : ℝ) - (D.cellIndex j : ℝ)| ≤ B →
        Real.exp (2 * M * radialQ i + 2 * γw * radialS i) *
          radialE (D.cellIndex j) ^ A *
          (T.M (T.sample j) ^ (-t) * T.H (T.sample j) ^ γ) ^ 2 ≤ C := by
  obtain ⟨C0, A0, hC0, hA0, hindex⟩ :=
    n05_referenceSourceWeight_index_window hB hγw M
  obtain ⟨CH, hCH, hHcompare⟩ :=
    n05_materialH_reference_exponential_comparison hD hT (-(2 * γw))
  obtain ⟨CE, hCE, hcoefficient⟩ :=
    referenceCellCoefficient_le_materialM hD hT (add_nonneg hA hA0)
  obtain ⟨CM, hCM, henvelope⟩ :=
    n05_materialWeight_bound hT (show 0 < 2 * (γ - γw) by linarith) (2 * t - 2)
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsample, _, _⟩ := hdata
  refine ⟨C0 * CH * CE * CM, by positivity, fun j i hij => ?_⟩
  let Ms : ℝ := T.M (T.sample j)
  let Hs : ℝ := T.H (T.sample j)
  let E : ℝ := radialE (D.cellIndex j)
  have hr : T.sample j ∈ radialCore D :=
    hD.choose_spec.2.1.2.2.2.1 j (hsample j)
  have hMs : 0 < Ms := zero_lt_one.trans_le (hT.2.1 _ hr).2.2.2
  have hHs : 0 < Hs := (hT.2.1 _ hr).2.1
  have hE : 0 < E := Real.exp_pos _
  have hH : Real.exp (2 * γw * radialS (D.cellIndex j)) ≤
      CH * Ms * Hs ^ (-(2 * γw)) := by
    simpa only [neg_neg] using (hHcompare j (T.sample j) (hsample j)).2
  have hEbound : E ^ (A + A0) ≤ CE * Ms :=
    hcoefficient j (T.sample j) (hsample j)
  have hMpow : Ms ^ 2 * (Ms ^ (-t)) ^ 2 = Ms ^ (2 - 2 * t) := by
    rw [← Real.rpow_two, ← Real.rpow_mul_natCast hMs.le, ← Real.rpow_add hMs]
    congr 1
    ring
  have hHpow : Hs ^ (-(2 * γw)) * (Hs ^ γ) ^ 2 =
      Hs ^ (2 * (γ - γw)) := by
    rw [← Real.rpow_mul_natCast hHs.le, ← Real.rpow_add hHs]
    congr 1
    ring
  have henv : Ms ^ (2 - 2 * t) * Hs ^ (2 * (γ - γw)) ≤ CM := by
    rw [show 2 - 2 * t = -(2 * t - 2) by ring]
    exact henvelope (T.sample j) hr
  change Real.exp (2 * M * radialQ i + 2 * γw * radialS i) *
    E ^ A * (Ms ^ (-t) * Hs ^ γ) ^ 2 ≤ _
  calc
    _ ≤ (C0 * E ^ A0 * Real.exp (2 * γw * radialS (D.cellIndex j))) *
        E ^ A * (Ms ^ (-t) * Hs ^ γ) ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hindex i (D.cellIndex j) hij)
          (Real.rpow_nonneg hE.le A)) (sq_nonneg _)
    _ ≤ (C0 * E ^ A0 * (CH * Ms * Hs ^ (-(2 * γw)))) *
        E ^ A * (Ms ^ (-t) * Hs ^ γ) ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hH (by positivity))
          (Real.rpow_nonneg hE.le A)) (sq_nonneg _)
    _ = (C0 * CH * E ^ (A + A0)) *
        ((Ms * Hs ^ (-(2 * γw))) * (Ms ^ (-t) * Hs ^ γ) ^ 2) := by
      rw [Real.rpow_add hE]
      ring
    _ ≤ (C0 * CH * (CE * Ms)) *
        ((Ms * Hs ^ (-(2 * γw))) * (Ms ^ (-t) * Hs ^ γ) ^ 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hEbound (by positivity)) (by positivity)
    _ = (C0 * CH * CE) *
        ((Ms ^ 2 * (Ms ^ (-t)) ^ 2) * (Hs ^ (-(2 * γw)) * (Hs ^ γ) ^ 2)) := by
      ring
    _ = (C0 * CH * CE) * (Ms ^ (2 - 2 * t) * Hs ^ (2 * (γ - γw))) := by
      rw [hMpow, hHpow]
    _ ≤ (C0 * CH * CE) * CM :=
      mul_le_mul_of_nonneg_left henv (by positivity)

end ContinuousFlexibility.Statements
