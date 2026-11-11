import ContinuousFlexibility.Analysis.N06CubicMultiplierJets

/-!
# The actual positive-piece cubic multipliers

The primitive hypotheses concern only the three divided coefficient
fields on positive pieces. Negative pieces contribute zero. This keeps
their different canonical intervals out of the unit-cylinder estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- Primitive local regularity, symmetries and finite mixed jet bounds
of the three actual divided coefficients. -/
structure N06PositiveCubicControl
    {S : PhysicalSpacesData} (K : CanonicalData S) (b : ℕ)
    (scale : ℕ → ℝ) (δ : ℝ) (A B C : ℕ → PolarPoint → ℝ) : Prop where
  a_smooth : ∀ m, K.positive m = true → ContDiffOn ℝ ∞ (A m) (canonicalOpen S K m)
  b_smooth : ∀ m, K.positive m = true → ContDiffOn ℝ ∞ (B m) (canonicalOpen S K m)
  c_smooth : ∀ m, K.positive m = true → ContDiffOn ℝ ∞ (C m) (canonicalOpen S K m)
  a_periodic : ∀ m, K.positive m = true → ∀ p ∈ canonicalOpen S K m,
    A m (p + (0, Real.pi)) = A m p
  b_periodic : ∀ m, K.positive m = true → ∀ p ∈ canonicalOpen S K m,
    B m (p + (0, Real.pi)) = B m p
  c_periodic : ∀ m, K.positive m = true → ∀ p ∈ canonicalOpen S K m,
    C m (p + (0, Real.pi)) = C m p
  a_even : ∀ m, K.positive m = true → ∀ p ∈ canonicalOpen S K m,
    A m (p.1, Real.pi - p.2) = A m p
  b_odd : ∀ m, K.positive m = true → ∀ p ∈ canonicalOpen S K m,
    B m (p.1, Real.pi - p.2) = -B m p
  c_even : ∀ m, K.positive m = true → ∀ p ∈ canonicalOpen S K m,
    C m (p.1, Real.pi - p.2) = C m p
  jets : ∀ m, K.positive m = true → ∀ a j, a + j ≤ b + 1 →
    ∀ p ∈ canonicalOpen S K m,
      |mixedDerivative a j (A m) p| ≤ δ * scale m ∧
      |mixedDerivative a j (B m) p| ≤ δ * scale m ∧
      |mixedDerivative a j (C m) p| ≤ δ * scale m

def n06PositiveCubicMultipliers
    {S : PhysicalSpacesData} (K : CanonicalData S) (A B C : ℕ → PolarPoint → ℝ)
    (i : Fin 5) (m : ℕ) : PolarPoint → ℝ :=
  if K.positive m = true then
    n06CubicGraphMultipliers cylinderWeight (fun r => 1 - 2 * r) (A m) (B m) (C m) i
  else fun _ => 0

theorem n06PositiveCubicMultipliers_of_positive
    {S : PhysicalSpacesData} {K : CanonicalData S} (A B C : ℕ → PolarPoint → ℝ)
    (i : Fin 5) (m : ℕ) (hm : K.positive m = true) :
    n06PositiveCubicMultipliers K A B C i m =
      n06CubicGraphMultipliers cylinderWeight (fun r => 1 - 2 * r) (A m) (B m) (C m) i := by
  simp only [n06PositiveCubicMultipliers, if_pos hm]

theorem n06PositiveCubicMultipliers_of_not_positive
    {S : PhysicalSpacesData} {K : CanonicalData S} (A B C : ℕ → PolarPoint → ℝ)
    (i : Fin 5) (m : ℕ) (hm : K.positive m ≠ true) :
    n06PositiveCubicMultipliers K A B C i m = fun _ => 0 := by
  simp only [n06PositiveCubicMultipliers, if_neg hm]

variable {S : PhysicalSpacesData} {K : CanonicalData S} {b : ℕ}
  {scale : ℕ → ℝ} {δ : ℝ} {A B C : ℕ → PolarPoint → ℝ}

theorem N06PositiveCubicControl.multiplier_smooth
    (h : N06PositiveCubicControl K b scale δ A B C)
    (hl : ∀ m, K.positive m = true → K.left m = 0)
    (hr : ∀ m, K.positive m = true → K.right m = 1) (i : Fin 5) (m : ℕ) :
    ContDiffOn ℝ ∞ (n06PositiveCubicMultipliers K A B C i m) (canonicalOpen S K m) := by
  by_cases hm : K.positive m = true
  · rw [n06PositiveCubicMultipliers_of_positive A B C i m hm]
    have hd : ContDiff ℝ ∞ cylinderWeight := by
      change ContDiff ℝ ∞ (fun r : ℝ => r * (1 - r))
      exact contDiff_id.mul (contDiff_const.sub contDiff_id)
    have he : ContDiff ℝ ∞ (fun r : ℝ => 1 - 2 * r) :=
      contDiff_const.sub (contDiff_const.mul contDiff_id)
    have hdpos (r : ℝ) (hrr : r ∈ Ioo (K.left m) (K.right m)) : 0 < cylinderWeight r := by
      rw [hl m hm, hr m hm] at hrr
      exact mul_pos hrr.1 (sub_pos.mpr hrr.2)
    exact n06CubicGraphMultipliers_contDiffOn_strip hd.contDiffOn he.contDiffOn hdpos
      (h.a_smooth m hm) (h.b_smooth m hm) (h.c_smooth m hm) i
  · rw [n06PositiveCubicMultipliers_of_not_positive A B C i m hm]
    exact contDiffOn_const

theorem N06PositiveCubicControl.multiplier_periodic
    (h : N06PositiveCubicControl K b scale δ A B C)
    (i : Fin 5) (m : ℕ) (p : PolarPoint) (hp : p ∈ canonicalOpen S K m) :
    n06PositiveCubicMultipliers K A B C i m (p + (0, Real.pi)) =
      n06PositiveCubicMultipliers K A B C i m p := by
  by_cases hm : K.positive m = true
  · rw [n06PositiveCubicMultipliers_of_positive A B C i m hm]
    exact n06CubicGraphMultipliers_periodicOn_strip cylinderWeight (fun r => 1 - 2 * r)
      (fun q hq => h.a_periodic m hm q ⟨hq, mem_univ _⟩)
      (fun q hq => h.b_periodic m hm q ⟨hq, mem_univ _⟩)
      (fun q hq => h.c_periodic m hm q ⟨hq, mem_univ _⟩) i p hp.1
  · rw [n06PositiveCubicMultipliers_of_not_positive A B C i m hm]

theorem N06PositiveCubicControl.multiplier_reflection
    (h : N06PositiveCubicControl K b scale δ A B C)
    (i : Fin 5) (m : ℕ) (p : PolarPoint) (hp : p ∈ canonicalOpen S K m) :
    n06PositiveCubicMultipliers K A B C i m (p.1, Real.pi - p.2) =
      n06CubicGraphParity i * n06PositiveCubicMultipliers K A B C i m p := by
  by_cases hm : K.positive m = true
  · rw [n06PositiveCubicMultipliers_of_positive A B C i m hm]
    exact n06CubicGraphMultipliers_reflectionOn_strip cylinderWeight (fun r => 1 - 2 * r)
      (h.a_smooth m hm) (h.b_smooth m hm) (h.c_smooth m hm)
      (fun q hq => h.a_even m hm q ⟨hq, mem_univ _⟩)
      (fun q hq => h.b_odd m hm q ⟨hq, mem_univ _⟩)
      (fun q hq => h.c_even m hm q ⟨hq, mem_univ _⟩) i p hp.1
  · rw [n06PositiveCubicMultipliers_of_not_positive A B C i m hm]
    exact (mul_zero _).symm

theorem N06PositiveCubicControl.multiplier_jet_bound
    (h : N06PositiveCubicControl K b scale δ A B C)
    (hl : ∀ m, K.positive m = true → K.left m = 0)
    (hr : ∀ m, K.positive m = true → K.right m = 1)
    (hscale : ∀ m, 0 ≤ scale m) (hδ : 0 ≤ δ)
    (i : Fin 5) (m j : ℕ) (hj : j ≤ b) (p : PolarPoint) (hp : p ∈ canonicalOpen S K m) :
    |mixedDerivative 0 j (n06PositiveCubicMultipliers K A B C i m) p| ≤ 5 * (δ * scale m) := by
  by_cases hm : K.positive m = true
  · rw [n06PositiveCubicMultipliers_of_positive A B C i m hm]
    have hp' : p.1 ∈ Icc (0 : ℝ) 1 := by
      have h := hp.1
      rw [hl m hm, hr m hm] at h
      exact ⟨h.1.le, h.2.le⟩
    have he : |1 - 2 * p.1| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> linarith [hp'.1, hp'.2]
    exact n06CubicGraphMultipliers_angularJet_abs_leOn_strip cylinderWeight
      (fun r => 1 - 2 * r) (h.a_smooth m hm) (h.b_smooth m hm) (h.c_smooth m hm)
      (mul_nonneg hδ (hscale m)) p hp.1 (cylinderWeight_nonneg hp')
      (cylinderWeight_le_one hp') he (fun a k hak => h.jets m hm a k hak p hp) j hj i
  · rw [n06PositiveCubicMultipliers_of_not_positive A B C i m hm]
    simpa only [mixedDerivative, iteratedDeriv_fun_const_zero, abs_zero] using
      mul_nonneg (show (0 : ℝ) ≤ 5 by norm_num) (mul_nonneg hδ (hscale m))

end ContinuousFlexibility.Analysis
