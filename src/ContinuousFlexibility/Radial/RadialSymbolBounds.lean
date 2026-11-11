import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fixed-threshold bounds for actual radial derivative symbols

The derivatives are the genuine one-dimensional iterated derivatives.
Every derivative order uses the same lower threshold `L0`; only the
constants may depend on the order. These generic closure results must
still be instantiated on the actual Laplace moments and radial weights.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Smoothness on the positive half-line and power estimates for every
actual derivative, all on one fixed tail. -/
def RadialSymbolBounds (L0 s : ℝ) (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f (Ioi 0) ∧
    ∀ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, L0 ≤ L → 0 < L →
      ‖iteratedDeriv r f L‖ ≤ C * L ^ (s - (r : ℝ))

theorem RadialSymbolBounds.contDiffAt {L0 s L : ℝ} {f : ℝ → ℝ}
    (hf : RadialSymbolBounds L0 s f) (hL : 0 < L) : ContDiffAt ℝ ∞ f L :=
  hf.1.contDiffAt (isOpen_Ioi.mem_nhds hL)

/-- Addition preserves the order and the original threshold. -/
theorem RadialSymbolBounds.add {L0 s : ℝ} {f g : ℝ → ℝ}
    (hf : RadialSymbolBounds L0 s f) (hg : RadialSymbolBounds L0 s g) :
    RadialSymbolBounds L0 s (f + g) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  intro r
  obtain ⟨A, hA, hAf⟩ := hf.2 r
  obtain ⟨B, hB, hBg⟩ := hg.2 r
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  intro L hL0 hL
  rw [iteratedDeriv_add ((hf.contDiffAt hL).of_le (by simp))
    ((hg.contDiffAt hL).of_le (by simp))]
  calc
    _ ≤ ‖iteratedDeriv r f L‖ + ‖iteratedDeriv r g L‖ := norm_add_le _ _
    _ ≤ A * L ^ (s - (r : ℝ)) + B * L ^ (s - (r : ℝ)) :=
      add_le_add (hAf L hL0 hL) (hBg L hL0 hL)
    _ = _ := by ring

private theorem norm_product_power_bound {L s t A B a u v : ℝ}
    (hL : 0 < L) (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hu : ‖u‖ ≤ A * L ^ s) (hv : ‖v‖ ≤ B * L ^ t) :
    ‖a * u * v‖ ≤ (a * A * B) * L ^ (s + t) := by
  rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg ha]
  calc
    a * ‖u‖ * ‖v‖ ≤ (a * (A * L ^ s)) * (B * L ^ t) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hu ha) hv (norm_nonneg _)
        (mul_nonneg ha (mul_nonneg hA (rpow_nonneg hL.le _)))
    _ = (a * A * B) * (L ^ s * L ^ t) := by ring
    _ = _ := by rw [← Real.rpow_add hL]

/-- The product estimate uses the actual Leibniz formula at every order.
The tail threshold is unchanged. -/
theorem RadialSymbolBounds.mul {L0 s t : ℝ} {f g : ℝ → ℝ}
    (hf : RadialSymbolBounds L0 s f) (hg : RadialSymbolBounds L0 t g) :
    RadialSymbolBounds L0 (s + t) (f * g) := by
  classical
  choose A hA hAf using hf.2
  choose B hB hBg using hg.2
  refine ⟨hf.1.mul hg.1, ?_⟩
  intro r
  let C : ℝ := ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * A i * B (r - i)
  refine ⟨C, Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB (r - i))), ?_⟩
  intro L hL0 hL
  rw [iteratedDeriv_mul ((hf.contDiffAt hL).of_le (by simp))
    ((hg.contDiffAt hL).of_le (by simp))]
  calc
    _ ≤ ∑ i ∈ Finset.range (r + 1),
        ‖(r.choose i : ℝ) * iteratedDeriv i f L * iteratedDeriv (r - i) g L‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (r + 1),
        ((r.choose i : ℝ) * A i * B (r - i)) * L ^ (s + t - (r : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hir : i ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have he : (s - (i : ℝ)) + (t - ((r - i : ℕ) : ℝ)) = s + t - (r : ℝ) := by
        rw [Nat.cast_sub hir]
        ring
      simpa only [he] using norm_product_power_bound hL (hA i) (Nat.cast_nonneg _)
        (hAf i L hL0 hL) (hBg (r - i) L hL0 hL)
    _ = C * L ^ (s + t - (r : ℝ)) := by rw [Finset.sum_mul]

/-- Multiplication by a constant preserves the original tail. -/
theorem RadialSymbolBounds.const_mul {L0 s : ℝ} {f : ℝ → ℝ}
    (hf : RadialSymbolBounds L0 s f) (a : ℝ) :
    RadialSymbolBounds L0 s (fun L => a * f L) := by
  refine ⟨contDiffOn_const.mul hf.1, ?_⟩
  intro r
  obtain ⟨C, hC, hCf⟩ := hf.2 r
  refine ⟨|a| * C, mul_nonneg (abs_nonneg _) hC, ?_⟩
  intro L hL0 hL
  rw [iteratedDeriv_const_mul_field, norm_mul, Real.norm_eq_abs]
  calc
    _ ≤ |a| * (C * L ^ (s - (r : ℝ))) :=
      mul_le_mul_of_nonneg_left (hCf L hL0 hL) (abs_nonneg _)
    _ = _ := by ring

private theorem reciprocal_zero_bound {L s c y : ℝ}
    (hL : 0 < L) (hc : 0 < c) (hy : c * L ^ s ≤ y) :
    ‖y⁻¹‖ ≤ c⁻¹ * L ^ (-s) := by
  have hlow : 0 < c * L ^ s := mul_pos hc (rpow_pos_of_pos hL _)
  have hy0 : 0 < y := lt_of_lt_of_le hlow hy
  rw [norm_inv, Real.norm_eq_abs, abs_of_pos hy0]
  have hh := one_div_le_one_div_of_le hlow hy
  calc
    y⁻¹ ≤ (c * L ^ s)⁻¹ := by simpa only [one_div] using hh
    _ = c⁻¹ * L ^ (-s) := by rw [mul_inv, Real.rpow_neg hL.le]

private theorem reciprocal_derivative_formula {L0 s : ℝ} {f : ℝ → ℝ}
    (hf : RadialSymbolBounds L0 s f) (hne : ∀ L : ℝ, f L ≠ 0)
    {r : ℕ} (hr : 0 < r) {L : ℝ} (hL : 0 < L) :
    iteratedDeriv r f⁻¹ L = -(f L)⁻¹ *
      ∑ i ∈ Finset.range r, (r.choose (i + 1) : ℝ) *
        iteratedDeriv (i + 1) f L * iteratedDeriv (r - (i + 1)) f⁻¹ L := by
  have hprod := iteratedDeriv_mul
    ((hf.contDiffAt hL).of_le (by simp : (r : ℕ∞ω) ≤ ∞))
    (((hf.contDiffAt hL).inv (hne L)).of_le (by simp : (r : ℕ∞ω) ≤ ∞))
  have hfun : f * f⁻¹ = (fun _ : ℝ => 1) := by
    funext x
    simp only [Pi.mul_apply, Pi.inv_apply, mul_inv_cancel₀ (hne x)]
  rw [hfun, iteratedDeriv_const, ite_eq_right (Nat.ne_of_gt hr), Finset.sum_range_succ'] at hprod
  simp only [Nat.choose_zero_right, Nat.cast_one, iteratedDeriv_zero, Nat.sub_zero,
    one_mul] at hprod
  have hrec : f L * iteratedDeriv r f⁻¹ L =
      -(∑ i ∈ Finset.range r, (r.choose (i + 1) : ℝ) *
        iteratedDeriv (i + 1) f L * iteratedDeriv (r - (i + 1)) f⁻¹ L) := by
    linarith only [hprod]
  calc
    _ = ((f L)⁻¹ * f L) * iteratedDeriv r f⁻¹ L := by rw [inv_mul_cancel₀ (hne L), one_mul]
    _ = (f L)⁻¹ * (f L * iteratedDeriv r f⁻¹ L) := by ring
    _ = _ := by rw [hrec]; ring

/-- Reciprocal symbols have the opposite order on exactly the same tail.
The proof derives every inverse derivative from the genuine Leibniz
formula and lower orders; no inverse-jet estimate is assumed. The global
nonvanishing hypothesis is satisfied by the actual positive moments. -/
theorem RadialSymbolBounds.inv {L0 s : ℝ} {f : ℝ → ℝ}
    (hf : RadialSymbolBounds L0 s f) (hne : ∀ L : ℝ, f L ≠ 0)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ L : ℝ, L0 ≤ L → 0 < L → c * L ^ s ≤ f L) :
    RadialSymbolBounds L0 (-s) f⁻¹ := by
  classical
  choose A hA hAf using hf.2
  refine ⟨hf.1.inv (fun L _ => hne L), ?_⟩
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hr : r = 0
    · subst r
      refine ⟨c⁻¹, inv_nonneg.mpr hc.le, ?_⟩
      intro L hL0 hL
      simpa only [iteratedDeriv_zero, Nat.cast_zero, sub_zero, Pi.inv_apply] using
        reciprocal_zero_bound hL hc (hlower L hL0 hL)
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
      have hprev : ∀ m : Fin r, ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, L0 ≤ L → 0 < L →
          ‖iteratedDeriv m.val f⁻¹ L‖ ≤ C * L ^ (-s - (m.val : ℝ)) :=
        fun m => ih m.val m.isLt
      choose B hB hBb using hprev
      let m (i : ℕ) : Fin r := ⟨r - (i + 1), Nat.sub_lt hrpos (Nat.succ_pos i)⟩
      let S : ℝ := ∑ i ∈ Finset.range r,
        (r.choose (i + 1) : ℝ) * A (i + 1) * B (m i)
      have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA (i + 1))) (hB (m i)))
      refine ⟨c⁻¹ * S, mul_nonneg (inv_nonneg.mpr hc.le) hS, ?_⟩
      intro L hL0 hL
      have hsum :
          ‖∑ i ∈ Finset.range r, (r.choose (i + 1) : ℝ) *
            iteratedDeriv (i + 1) f L * iteratedDeriv (r - (i + 1)) f⁻¹ L‖ ≤
            S * L ^ (-(r : ℝ)) := by
        calc
          _ ≤ ∑ i ∈ Finset.range r,
              ‖(r.choose (i + 1) : ℝ) * iteratedDeriv (i + 1) f L *
                iteratedDeriv (r - (i + 1)) f⁻¹ L‖ := norm_sum_le _ _
          _ ≤ ∑ i ∈ Finset.range r,
              ((r.choose (i + 1) : ℝ) * A (i + 1) * B (m i)) * L ^ (-(r : ℝ)) := by
            apply Finset.sum_le_sum
            intro i hi
            have hir : i + 1 ≤ r := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
            have he : (s - ((i + 1 : ℕ) : ℝ)) +
                (-s - ((r - (i + 1) : ℕ) : ℝ)) = -(r : ℝ) := by
              rw [Nat.cast_sub hir]
              ring
            have hGi := hBb (m i) L hL0 hL
            change ‖iteratedDeriv (r - (i + 1)) f⁻¹ L‖ ≤
              B (m i) * L ^ (-s - ((r - (i + 1) : ℕ) : ℝ)) at hGi
            simpa only [he] using norm_product_power_bound hL (hA (i + 1))
              (Nat.cast_nonneg _) (hAf (i + 1) L hL0 hL) hGi
          _ = S * L ^ (-(r : ℝ)) := by rw [Finset.sum_mul]
      rw [reciprocal_derivative_formula hf hne hrpos hL, norm_mul, norm_neg]
      calc
        _ ≤ (c⁻¹ * L ^ (-s)) * (S * L ^ (-(r : ℝ))) :=
          mul_le_mul (reciprocal_zero_bound hL hc (hlower L hL0 hL)) hsum
            (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr hc.le) (rpow_nonneg hL.le _))
        _ = (c⁻¹ * S) * (L ^ (-s) * L ^ (-(r : ℝ))) := by ring
        _ = (c⁻¹ * S) * L ^ (-s - (r : ℝ)) := by
          rw [← Real.rpow_add hL]
          congr 1

theorem RadialSymbolBounds.neg {L0 s : ℝ} {f : ℝ → ℝ}
    (hf : RadialSymbolBounds L0 s f) : RadialSymbolBounds L0 s (-f) := by
  have h := hf.const_mul (-1)
  simp only [neg_one_mul] at h
  rw [show (fun L : ℝ => -f L) = -f from rfl] at h
  exact h

theorem RadialSymbolBounds.sub {L0 s : ℝ} {f g : ℝ → ℝ}
    (hf : RadialSymbolBounds L0 s f) (hg : RadialSymbolBounds L0 s g) :
    RadialSymbolBounds L0 s (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- Quotients use the same lower threshold and the proved reciprocal
estimates, rather than a fresh threshold for each output order. -/
theorem RadialSymbolBounds.div {L0 s t : ℝ} {f g : ℝ → ℝ}
    (hf : RadialSymbolBounds L0 s f) (hg : RadialSymbolBounds L0 t g)
    (hne : ∀ L : ℝ, g L ≠ 0) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ L : ℝ, L0 ≤ L → 0 < L → c * L ^ t ≤ g L) :
    RadialSymbolBounds L0 (s - t) (f / g) := by
  simpa only [sub_eq_add_neg, div_eq_mul_inv] using hf.mul (hg.inv hne hc hlower)

end ContinuousFlexibility.Radial
