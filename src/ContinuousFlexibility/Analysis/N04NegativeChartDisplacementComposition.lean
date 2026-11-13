import ContinuousFlexibility.Analysis.N04NegativeGeometryFlowCoefficientBounds

/-!
# The sharp spatial degree of a composed displacement

At a positive spatial order, subtracting the outer value at the
evaluation point removes its unused zeroth jet. Weighted composition
then retains the degree `j - 1`, including when the inner angle itself
is unbounded. The zeroth order is estimated directly.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

private theorem positive_jet_sub_const
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {g : Y → ℝ} (hg : ContDiff ℝ ∞ g) {j : ℕ} (hj : 0 < j)
    (c : ℝ) (y : Y) :
    iteratedFDeriv ℝ j (fun z => g z - c) y = iteratedFDeriv ℝ j g y := by
  rw [iteratedFDeriv_sub_apply (hg.contDiffAt.of_le (by simp)) contDiffAt_const]
  cases j with
  | zero => omega
  | succ j => simp only [iteratedFDeriv_succ_const, sub_zero]

/-- The finite prefix constant is uniform in the point and the inner
and outer maps. No zeroth-order bound on the inner map is required. -/
theorem n04NegativeChart_displacementComposition_prefix
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} {g : Y → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (K : ℕ) (x : X) {A B ρ : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hρ : 1 ≤ ρ)
    (houter : ∀ j, j ≤ K → ‖iteratedFDeriv ℝ j g (f x)‖ ≤ A * ρ ^ (j - 1))
    (hinner : ∀ j, 1 ≤ j → j ≤ K →
      ‖iteratedFDeriv ℝ j f x‖ ≤ B * ρ ^ (j - 1)) :
    ∀ j, j ≤ K → ‖iteratedFDeriv ℝ j (g ∘ f) x‖ ≤
      (K.factorial : ℝ) * A * B ^ K * ρ ^ (j - 1) := by
  intro j hj
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  have hfac : 1 ≤ (K.factorial : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos K)
  by_cases hj0 : j = 0
  · subst j
    have hraw : ‖g (f x)‖ ≤ A := by
      simpa only [norm_iteratedFDeriv_zero, Nat.zero_sub, pow_zero, mul_one] using
        houter 0 (Nat.zero_le K)
    have hpack : A ≤ (K.factorial : ℝ) * A * B ^ K :=
      (le_mul_of_one_le_left hA hfac).trans
        (le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans hfac) hA) (one_le_pow₀ hB))
    simpa only [norm_iteratedFDeriv_zero, Function.comp_apply,
      Nat.zero_sub, pow_zero, mul_one] using hraw.trans hpack
  have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
  let g₀ : Y → ℝ := fun y => g y - g (f x)
  have hg₀ : ContDiff ℝ ∞ g₀ := hg.sub contDiff_const
  have ho (l : ℕ) (hl : l ≤ j) :
      ‖iteratedFDeriv ℝ l g₀ (f x)‖ ≤ (A / ρ) * ρ ^ l := by
    by_cases hl0 : l = 0
    · subst l
      simp only [norm_iteratedFDeriv_zero, g₀, sub_self, norm_zero, pow_zero, mul_one]
      exact div_nonneg hA hρpos.le
    · rw [positive_jet_sub_const hg (Nat.pos_of_ne_zero hl0)]
      have he : (A / ρ) * ρ ^ l = A * ρ ^ (l - 1) := by
        have hpow : ρ ^ l = ρ ^ (l - 1) * ρ := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ l)]
        rw [hpow]
        field_simp [hρpos.ne'] <;> ring
      rw [he]
      exact houter l (hl.trans hj)
  have hb := n04NegativeGeometry_weighted_composition_jet_le hf hg₀ x j hB hρ ho
    (fun l hl hlj => hinner l hl (hlj.trans hj))
  have he : iteratedFDeriv ℝ j (g₀ ∘ f) x = iteratedFDeriv ℝ j (g ∘ f) x :=
    positive_jet_sub_const (hg.comp hf) hjpos (g (f x)) x
  rw [he] at hb
  have hpow : ρ ^ j = ρ ^ (j - 1) * ρ := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ j)]
  have hc : (j.factorial : ℝ) * (A / ρ) * B ^ j * ρ ^ j =
      (j.factorial : ℝ) * A * B ^ j * ρ ^ (j - 1) := by
    rw [hpow]
    field_simp [hρpos.ne'] <;> ring
  rw [hc] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_right
      (show (j.factorial : ℝ) ≤ (K.factorial : ℝ) by exact_mod_cast Nat.factorial_le hj) hA)
      (pow_le_pow_right₀ hB hj) (pow_nonneg (zero_le_one.trans hB) _)
      (mul_nonneg (Nat.cast_nonneg _) hA)) (pow_nonneg hρpos.le _))

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_displacementComposition_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_displacementComposition_prefix
