import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Power decay for genuine damped scalar differential equations

The estimates concern actual derivatives on a fixed positive half-line.
A power fence gives a bound on a further tail. A genuine compact-interval
bound then restores the original threshold, which may therefore be kept
fixed when the lemma is used at successive derivative orders.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A later power estimate extends to the original positive threshold
by continuity on the actual compact gap. -/
theorem extend_norm_power_bound_from_tail {u : ℝ → ℝ} {L0 L1 s B : ℝ}
    (hL0 : 0 < L0) (_hL1 : L0 ≤ L1) (hB : 0 ≤ B)
    (hu : ContinuousOn u (Ici L0))
    (htail : ∀ L : ℝ, L1 ≤ L → ‖u L‖ ≤ B * L ^ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, L0 ≤ L → ‖u L‖ ≤ C * L ^ s := by
  have hc : ContinuousOn (fun L : ℝ => u L * L ^ (-s)) (Icc L0 L1) :=
    (hu.mono Icc_subset_Ici_self).mul
      (continuousOn_id.rpow_const (fun L hL => Or.inl (ne_of_gt (hL0.trans_le hL.1))))
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max B A, hB.trans (le_max_left _ _), ?_⟩
  intro L hL
  have hLp : 0 < L := hL0.trans_le hL
  by_cases hLtail : L1 ≤ L
  · exact (htail L hLtail).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (rpow_nonneg hLp.le _))
  · have hh := mul_le_mul_of_nonneg_right (hA L ⟨hL, (lt_of_not_ge hLtail).le⟩)
      (rpow_nonneg hLp.le s)
    rw [norm_mul, Real.norm_of_nonneg (rpow_nonneg hLp.le (-s))] at hh
    have hid : L ^ (-s) * L ^ s = 1 := by rw [← rpow_add hLp]; simp
    rw [mul_assoc, hid, mul_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (rpow_nonneg hLp.le _))

private theorem damped_upper_power_fence {u a b : ℝ → ℝ} {A c B m C : ℝ}
    (hA : 0 < A) (hc : 0 < c) (hC : 0 < C)
    (hquad : 2 * (m + 1) ≤ c * A ^ 2) (hBC : 2 * B < c * C)
    (hu : ContinuousOn u (Ici A))
    (hdu : ∀ L : ℝ, A ≤ L → HasDerivAt u (-a L * u L + b L) L)
    (ha : ∀ L : ℝ, A ≤ L → c * L ≤ a L)
    (hb : ∀ L : ℝ, A ≤ L → b L ≤ B * L ^ (-m))
    (hinit : u A ≤ C * A ^ (-m - 1)) :
    ∀ L : ℝ, A ≤ L → u L ≤ C * L ^ (-m - 1) := by
  intro L hL
  have hbound : ContinuousOn (fun x : ℝ => C * x ^ (-m - 1)) (Icc A L) :=
    continuousOn_const.mul
      (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (hA.trans_le hx.1))))
  have hdbound (x : ℝ) (hx : x ∈ Ico A L) :
      HasDerivWithinAt (fun y : ℝ => C * y ^ (-m - 1))
        (C * (-m - 1) * x ^ (-m - 2)) (Ici x) x := by
    have hxp : 0 < x := hA.trans_le hx.1
    have hh := (hasDerivAt_rpow_const (x := x) (p := -m - 1) (Or.inl hxp.ne')).const_mul C
    rw [show (-m - 1) - 1 = -m - 2 by ring] at hh
    simpa only [mul_assoc] using hh.hasDerivWithinAt (s := Ici x)
  apply image_le_of_deriv_right_lt_deriv_boundary'
    (hu.mono Icc_subset_Ici_self)
    (fun x hx => (hdu x hx.1).hasDerivWithinAt) hinit hbound hdbound ?_ ⟨hL, le_rfl⟩
  intro x hx heq
  have hxp : 0 < x := hA.trans_le hx.1
  have hx2 : 2 * (m + 1) ≤ c * x ^ 2 :=
    hquad.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hA.le hx.1 2) hc.le)
  have hpow1 : x ^ (-m - 1) = x * x ^ (-m - 2) := by
    calc
      _ = x ^ (1 + (-m - 2)) := by congr 1; ring
      _ = _ := by rw [rpow_add hxp, rpow_one]
  have hpow2 : x ^ (-m) = x ^ 2 * x ^ (-m - 2) := by
    calc
      _ = x ^ (2 + (-m - 2)) := by congr 1; ring
      _ = _ := by rw [rpow_add hxp, rpow_two]
  have hnum : -a x * C * x + B * x ^ 2 < C * (-m - 1) := by
    have hstrict := mul_pos (sub_pos.mpr hBC) (sq_pos_of_pos hxp)
    have hnonneg := mul_nonneg hC.le (sub_nonneg.mpr hx2)
    have ha' := mul_nonneg (sub_nonneg.mpr (ha x hx.1)) (mul_nonneg hC.le hxp.le)
    nlinarith only [hstrict, hnonneg, ha']
  calc
    -a x * u x + b x ≤ -a x * (C * x ^ (-m - 1)) + B * x ^ (-m) := by
      rw [heq]
      exact add_le_add le_rfl (hb x hx.1)
    _ = (-a x * C * x + B * x ^ 2) * x ^ (-m - 2) := by rw [hpow1, hpow2]; ring
    _ < (C * (-m - 1)) * x ^ (-m - 2) :=
      mul_lt_mul_of_pos_right hnum (rpow_pos_of_pos hxp _)

/-- Linear damping of size at least `c L` gains one power of decay.
The conclusion keeps exactly the original threshold `L0`; the constant
absorbs both the initial value and the genuine compact gap. -/
theorem exists_norm_power_bound_of_damped_deriv {u a b : ℝ → ℝ} {L0 c B m : ℝ}
    (hL0 : 0 < L0) (hc : 0 < c) (hB : 0 ≤ B) (hm : 0 ≤ m)
    (hu : ContinuousOn u (Ici L0))
    (hdu : ∀ L : ℝ, L0 ≤ L → HasDerivAt u (-a L * u L + b L) L)
    (ha : ∀ L : ℝ, L0 ≤ L → c * L ≤ a L)
    (hb : ∀ L : ℝ, L0 ≤ L → ‖b L‖ ≤ B * L ^ (-m)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, L0 ≤ L → ‖u L‖ ≤ C * L ^ (-m - 1) := by
  let A : ℝ := max L0 (sqrt (2 * (m + 1) / c) + 1)
  have hLA : L0 ≤ A := le_max_left _ _
  have hAp : 0 < A := hL0.trans_le hLA
  have hquad : 2 * (m + 1) ≤ c * A ^ 2 := by
    have hs : sqrt (2 * (m + 1) / c) ≤ A :=
      (by linarith : sqrt (2 * (m + 1) / c) ≤ sqrt (2 * (m + 1) / c) + 1).trans
        (le_max_right _ _)
    have hh := pow_le_pow_left₀ (sqrt_nonneg (2 * (m + 1) / c)) hs 2
    rw [sq_sqrt (by positivity : 0 ≤ 2 * (m + 1) / c)] at hh
    have hh' := (div_le_iff₀ hc).mp hh
    nlinarith only [hh']
  let C : ℝ := 2 * B / c + 1 + ‖u A‖ * A ^ (m + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hBC : 2 * B < c * C := by
    have hnonneg : 0 ≤ ‖u A‖ * A ^ (m + 1) := by positivity
    have hid : c * (2 * B / c) = 2 * B := by field_simp [hc.ne']
    calc
      2 * B < 2 * B + c := by linarith only [hc]
      _ ≤ 2 * B + c + c * (‖u A‖ * A ^ (m + 1)) :=
        le_add_of_nonneg_right (mul_nonneg hc.le hnonneg)
      _ = c * C := by
        dsimp only [C]
        rw [mul_add, mul_add, hid, mul_one]
  have hinit : ‖u A‖ ≤ C * A ^ (-m - 1) := by
    have hCA : ‖u A‖ * A ^ (m + 1) ≤ C := by
      have hh : 0 ≤ 2 * B / c := by positivity
      dsimp [C]
      linarith only [hh]
    have hh := mul_le_mul_of_nonneg_right hCA (rpow_nonneg hAp.le (-m - 1))
    have hid : A ^ (m + 1) * A ^ (-m - 1) = 1 := by
      rw [← rpow_add hAp, show (m + 1) + (-m - 1) = (0 : ℝ) by ring, rpow_zero]
    rwa [mul_assoc, hid, mul_one] at hh
  have hupper : ∀ L : ℝ, A ≤ L → u L ≤ C * L ^ (-m - 1) :=
    damped_upper_power_fence hAp hc hC hquad hBC
      (hu.mono (Ici_subset_Ici.mpr hLA))
      (fun L hL => hdu L (hLA.trans hL))
      (fun L hL => ha L (hLA.trans hL))
      (fun L hL => (le_norm_self (b L)).trans (hb L (hLA.trans hL)))
      ((le_norm_self (u A)).trans hinit)
  have hlower : ∀ L : ℝ, A ≤ L → -u L ≤ C * L ^ (-m - 1) := by
    apply damped_upper_power_fence (u := fun L => -u L) (a := a) (b := fun L => -b L)
      hAp hc hC hquad hBC
      ((hu.neg).mono (Ici_subset_Ici.mpr hLA))
    · intro L hL
      convert (hdu L (hLA.trans hL)).neg using 1
      ring
    · exact fun L hL => ha L (hLA.trans hL)
    · intro L hL
      exact (neg_le_abs (b L)).trans (hb L (hLA.trans hL))
    · exact (neg_le_abs (u A)).trans hinit
  apply extend_norm_power_bound_from_tail hL0 hLA hC.le hu
  intro L hL
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨neg_le.mpr (hlower L hL), hupper L hL⟩

end ContinuousFlexibility.Radial
