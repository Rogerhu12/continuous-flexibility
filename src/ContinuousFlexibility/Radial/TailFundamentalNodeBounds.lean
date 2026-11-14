module

public import ContinuousFlexibility.Radial.TailActualNodeCoefficients
public import ContinuousFlexibility.Radial.TailNaturalNodeBounds

/-!
# Bounds for the node values of the fundamental Green kernel

The natural solution contracts both absolute values and mass-weighted
absolute values. The unit Wronskian then gives a contracting affine
recurrence for the diagonal products of the two fundamental solutions.
This yields the Green product bound without assuming a node operator
representation for the differential resolvent.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

theorem tailNaturalDecay_le_quarter {T : DeepTailData} (hT : DeepTailHypotheses T)
    (hK : 32 ≤ T.K) (n : ℕ) :
    8 / (T.Λ * tailMass T (n + 1) * tailResistance T n) ≤ (1 / 4 : ℝ) := by
  apply (div_le_iff₀ (mul_pos (mul_pos hT.2.2.1 (tailMass_pos hT (n + 1)))
    (tailResistance_pos hT n))).mpr
  linarith only [hK, (hT.2.2.2.2.2.2.2.2.2.2 n).2.2.2.2.1]

theorem tailNaturalNode_abs_contractions {T : DeepTailData} (hT : DeepTailHypotheses T)
    (hK : 32 ≤ T.K) {a : ℕ → ℝ}
    (hstep : ∀ n, |a (n + 1)| ≤
      8 / (T.Λ * tailMass T (n + 1) * tailResistance T n) * |a n|) (n : ℕ) :
    |a (n + 1)| ≤ (1 / 4 : ℝ) * |a n| ∧
      tailMass T (n + 1) * |a (n + 1)| ≤ (1 / 4 : ℝ) * (tailMass T n * |a n|) := by
  constructor
  · exact (hstep n).trans (mul_le_mul_of_nonneg_right
      (tailNaturalDecay_le_quarter hT hK n) (abs_nonneg _))
  · have hmass := tailNode_decay_mass_factor (K := 32) hT.2.2.1 (by norm_num)
      (tailMass_pos hT (n + 1)) (tailResistance_pos hT n)
      (hK.trans (hT.2.2.2.2.2.2.2.2.2.2 n).2.2.2.1)
    calc
      tailMass T (n + 1) * |a (n + 1)| ≤ tailMass T (n + 1) *
          ((8 / (T.Λ * tailMass T (n + 1) * tailResistance T n)) * |a n|) :=
        mul_le_mul_of_nonneg_left (hstep n) (tailMass_pos hT (n + 1)).le
      _ = (tailMass T (n + 1) *
          (8 / (T.Λ * tailMass T (n + 1) * tailResistance T n))) * |a n| := by ring
      _ ≤ ((8 / 32 : ℝ) * tailMass T n) * |a n| :=
        mul_le_mul_of_nonneg_right hmass (abs_nonneg _)
      _ = _ := by ring

theorem tailNaturalNode_weighted_ratio_sq {T : DeepTailData} (hT : DeepTailHypotheses T)
    (hK : 32 ≤ T.K) {a : ℕ → ℝ} (ha : ∀ n, a n ≠ 0)
    (hstep : ∀ n, |a (n + 1)| ≤
      8 / (T.Λ * tailMass T (n + 1) * tailResistance T n) * |a n|) (n : ℕ) :
    tailMass T (n + 1) * (a (n + 1) / a n) ^ 2 ≤ tailMass T n / 4 := by
  have hc := tailNaturalNode_abs_contractions hT hK hstep n
  have hmul := mul_le_mul hc.2 hc.1 (abs_nonneg (a (n + 1)))
    (mul_nonneg (by norm_num) (mul_nonneg (tailMass_pos hT n).le (abs_nonneg _)))
  have hsq : tailMass T (n + 1) * a (n + 1) ^ 2 ≤
      (tailMass T n / 16) * a n ^ 2 := by
    calc
      tailMass T (n + 1) * a (n + 1) ^ 2 =
          (tailMass T (n + 1) * |a (n + 1)|) * |a (n + 1)| := by
        rw [← sq_abs (a (n + 1))]
        ring
      _ ≤ ((1 / 4 : ℝ) * (tailMass T n * |a n|)) * ((1 / 4 : ℝ) * |a n|) := hmul
      _ = (tailMass T n / 16) * a n ^ 2 := by rw [← sq_abs (a n)]; ring
  rw [div_pow, ← mul_div_assoc]
  apply (div_le_iff₀ (sq_pos_of_ne_zero (ha n))).mpr
  nlinarith only [hsq, mul_nonneg (tailMass_pos hT n).le (sq_nonneg (a n))]

theorem tailNaturalNode_backward_ratio {T : DeepTailData} (hT : DeepTailHypotheses T)
    (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K) {a : ℕ → ℝ}
    (ha : ∀ n, a n ≠ 0)
    (hrec : ∀ n, -tailActualInteriorDiagonal T hT n * a (n + 1) =
      tailActualNodeCoupling T hT n * a n +
        tailActualNodeCoupling T hT (n + 1) * a (n + 2))
    (hstep : ∀ n, |a (n + 1)| ≤
      8 / (T.Λ * tailMass T (n + 1) * tailResistance T n) * |a n|) (n : ℕ) :
    tailMass T (n + 1) * |a (n + 1) / (tailActualNodeCoupling T hT n * a n)| ≤
      4 / T.Λ := by
  let A := T.Λ * tailMass T (n + 1)
  let c := tailActualNodeCoupling T hT n
  let c' := tailActualNodeCoupling T hT (n + 1)
  let b := tailActualInteriorDiagonal T hT n
  have hc : 0 < c := tailActualNodeCoupling_pos hT n
  have hc' : 0 ≤ c' := (tailActualNodeCoupling_pos hT (n + 1)).le
  have hb : 0 < b := tailActualInteriorDiagonal_pos hT hη hK n
  have hbL : A / 2 ≤ b := (tailActualInteriorDiagonal_bounds hT hη hK n).1
  have hcU : c' ≤ A / 8 := tailNode_coupling_le_eighth_mass
    (tailResistance_pos hT (n + 1)) hK
    (hT.2.2.2.2.2.2.2.2.2.2 (n + 1)).2.2.2.1
    (tailActualNodeCoupling_upper hT hη (n + 1))
  have hnext : |a (n + 2)| ≤ |a (n + 1)| :=
    ((tailNaturalNode_abs_contractions hT hK hstep (n + 1)).1).trans
      (mul_le_of_le_one_left (abs_nonneg _) (by norm_num))
  have hrecabs : b * |a (n + 1)| ≤ c * |a n| + c' * |a (n + 2)| := by
    calc
      b * |a (n + 1)| = |-b * a (n + 1)| := by
        rw [abs_mul, abs_neg, abs_of_pos hb]
      _ = |c * a n + c' * a (n + 2)| := congrArg abs (hrec n)
      _ ≤ |c * a n| + |c' * a (n + 2)| := by
        simpa only [Real.norm_eq_abs] using norm_add_le (c * a n) (c' * a (n + 2))
      _ = _ := by rw [abs_mul, abs_mul, abs_of_pos hc, abs_of_nonneg hc']
  have hlower : (A / 4) * |a (n + 1)| ≤ c * |a n| := by
    have h₁ := mul_le_mul_of_nonneg_right hbL (abs_nonneg (a (n + 1)))
    have h₂ := mul_le_mul_of_nonneg_left hnext hc'
    have h₃ := mul_le_mul_of_nonneg_right hcU (abs_nonneg (a (n + 1)))
    have hA : 0 ≤ A := (mul_pos hT.2.2.1 (tailMass_pos hT (n + 1))).le
    nlinarith only [hrecabs, h₁, h₂, h₃, mul_nonneg hA (abs_nonneg (a (n + 1)))]
  rw [abs_div, abs_mul, abs_of_pos hc, ← mul_div_assoc]
  apply (div_le_div_iff₀ (mul_pos hc (abs_pos.mpr (ha n))) hT.2.2.1).mpr
  dsimp only [A] at hlower
  nlinarith only [hlower]

/-- The unit discrete Wronskian controls one diagonal Green step. -/
theorem tailNode_green_diagonal_step {μ ν a A w W c Λ : ℝ}
    (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (ha : a ≠ 0) (hc : c ≠ 0)
    (hwronskian : c * (a * W - A * w) = 1)
    (hratio : ν * (A / a) ^ 2 ≤ μ / 4)
    (hsource : ν * |A / (c * a)| ≤ 4 / Λ) :
    ν * |A * W| ≤ μ * |a * w| / 4 + 4 / Λ := by
  have heq : A * W = (A / a) ^ 2 * (a * w) + A / (c * a) := by
    have hW := congrArg (fun t : ℝ => A * t) hwronskian
    calc
      A * W = (c * A ^ 2 * w + A) / (c * a) := by
        apply (eq_div_iff (mul_ne_zero hc ha)).mpr
        nlinarith only [hW]
      _ = (A / a) ^ 2 * (a * w) + A / (c * a) := by
        field_simp [ha, hc] <;> ring
  rw [heq]
  calc
    ν * |(A / a) ^ 2 * (a * w) + A / (c * a)| ≤
        ν * (|(A / a) ^ 2 * (a * w)| + |A / (c * a)|) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using norm_add_le ((A / a) ^ 2 * (a * w)) (A / (c * a))) hν
    _ = (ν * (A / a) ^ 2) * |a * w| + ν * |A / (c * a)| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      ring
    _ ≤ (μ / 4) * |a * w| + 4 / Λ :=
      add_le_add (mul_le_mul_of_nonneg_right hratio (abs_nonneg _)) hsource
    _ = _ := by ring

theorem exists_tailFundamentalNode_bound {T : DeepTailData} (hT : DeepTailHypotheses T)
    (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K) {a w : ℕ → ℝ}
    (ha : ∀ n, a n ≠ 0)
    (hrec : ∀ n, -tailActualInteriorDiagonal T hT n * a (n + 1) =
      tailActualNodeCoupling T hT n * a n +
        tailActualNodeCoupling T hT (n + 1) * a (n + 2))
    (hstep : ∀ n, |a (n + 1)| ≤
      8 / (T.Λ * tailMass T (n + 1) * tailResistance T n) * |a n|)
    (hW : ∀ n, tailActualNodeCoupling T hT n *
      (a n * w (n + 1) - a (n + 1) * w n) = 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ m n, m ≤ n →
      |w m * a n| ≤ B / tailMass T m *
        ∏ k ∈ Finset.Ico m n, 8 / (T.Λ * tailMass T (k + 1) * tailResistance T k) := by
  let B := tailMass T 0 * |a 0 * w 0| + 8 / T.Λ
  have hB : 0 < B := add_pos_of_nonneg_of_pos
    (mul_nonneg (tailMass_pos hT 0).le (abs_nonneg _)) (div_pos (by norm_num) hT.2.2.1)
  have hdiagStep (n : ℕ) : tailMass T (n + 1) * |a (n + 1) * w (n + 1)| ≤
      tailMass T n * |a n * w n| / 4 + 4 / T.Λ :=
    tailNode_green_diagonal_step (tailMass_pos hT n).le (tailMass_pos hT (n + 1)).le
      (ha n) (tailActualNodeCoupling_pos hT n).ne' (hW n)
      (tailNaturalNode_weighted_ratio_sq hT hK ha hstep n)
      (tailNaturalNode_backward_ratio hT hη hK ha hrec hstep n)
  have hdiag (n : ℕ) : tailMass T n * |a n * w n| ≤ B := by
    induction n with
    | zero => exact le_add_of_nonneg_right (div_nonneg (by norm_num) hT.2.2.1.le)
    | succ n ih =>
      have hbase : 8 / T.Λ ≤ B := le_add_of_nonneg_left
        (mul_nonneg (tailMass_pos hT 0).le (abs_nonneg _))
      have h := hdiagStep n
      have heq : 8 / T.Λ = 2 * (4 / T.Λ) := by ring
      linarith only [h, ih, hbase, hB, heq]
  refine ⟨B, hB, ?_⟩
  intro m n hmn
  have hprod := tailNode_ratio_le_prod (fun k => abs_pos.mpr (ha k))
    (fun k => div_nonneg (by norm_num)
      (mul_pos (mul_pos hT.2.2.1 (tailMass_pos hT (k + 1))) (tailResistance_pos hT k)).le)
    hstep hmn
  have hdm : |w m * a m| ≤ B / tailMass T m := by
    apply (le_div_iff₀ (tailMass_pos hT m)).mpr
    simpa only [abs_mul, mul_comm, mul_left_comm, mul_assoc] using hdiag m
  have heq : |w m * a n| = |w m * a m| * (|a n| / |a m|) := by
    rw [abs_mul, abs_mul]
    field_simp [(abs_pos.mpr (ha m)).ne']
  rw [heq]
  exact mul_le_mul hdm hprod
    (div_nonneg (abs_nonneg _) (abs_nonneg _)) (div_nonneg hB.le (tailMass_pos hT m).le)

end ContinuousFlexibility.Radial
