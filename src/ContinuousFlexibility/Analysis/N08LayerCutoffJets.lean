import ContinuousFlexibility.Analysis.IntervalLayerCutoffDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Nat.Choose.Sum

/-!
# Uniform ordinary jets of the actual endpoint-band cutoff

The constants precede the interval, the two layer widths and the evaluation
point. Each fixed order costs only a fixed inverse power of the inner
width. This estimate also applies when the two layers lie near either end
of the annulus at once.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

theorem n08_smoothTransition_jet_bound (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, |iteratedDeriv n Real.smoothTransition x| ≤ B := by
  cases n with
  | zero =>
    exact ⟨1, zero_le_one, fun x => by
      simpa only [iteratedDeriv_zero, abs_of_nonneg (Real.smoothTransition.nonneg x)] using
        Real.smoothTransition.le_one x⟩
  | succ n =>
    have hs : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
      (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2
    obtain ⟨B, hB, hb⟩ :=
      Analysis.hasCompactSupport_deriv_smoothTransition.exists_bound_iteratedFDeriv hs n
    refine ⟨B, hB, fun x => ?_⟩
    simpa only [iteratedDeriv_succ', norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      Real.norm_eq_abs] using hb n le_rfl x

theorem n08_smoothTransition_prefix_bound (s : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ j ≤ s, ∀ x : ℝ,
      |iteratedDeriv j Real.smoothTransition x| ≤ B := by
  choose B hB hb using fun j : Fin (s + 1) => n08_smoothTransition_jet_bound j.val
  let K : ℝ := 1 + ∑ j, B j
  have hsum : 0 ≤ ∑ j, B j := Finset.sum_nonneg (fun j _ => hB j)
  refine ⟨K, by dsimp only [K]; linarith, fun j hj x => ?_⟩
  let k : Fin (s + 1) := ⟨j, by omega⟩
  have hk : B k ≤ ∑ i, B i :=
    Finset.single_le_sum (fun i _ => hB i) (Finset.mem_univ k)
  exact (hb k x).trans (by dsimp only [K]; linarith)

theorem n08_intervalLayerThreshold_jet (δ x : ℝ) (j : ℕ) :
    iteratedDeriv j (Analysis.intervalLayerThreshold δ) x =
      δ⁻¹ ^ j * iteratedDeriv j Real.smoothTransition (x / δ - 1) := by
  have he : Analysis.intervalLayerThreshold δ =
      fun y => (fun t => Real.smoothTransition (t - 1)) (δ⁻¹ * y) := by
    funext y
    simp only [Analysis.intervalLayerThreshold, div_eq_mul_inv, mul_comm]
  have hs : ContDiff ℝ j (fun t : ℝ => Real.smoothTransition (t - 1)) :=
    Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)
  rw [he, congrFun (iteratedDeriv_comp_const_mul hs δ⁻¹) x,
    iteratedDeriv_comp_sub_const]
  simp only [div_eq_mul_inv, mul_comm]

theorem n08_threshold_prefix_bound {s : ℕ} {B L δ : ℝ}
    (hB : 0 ≤ B) (hL : 1 ≤ L) (hδ : 0 < δ) (hδL : δ⁻¹ ≤ L)
    (hb : ∀ j ≤ s, ∀ x : ℝ, |iteratedDeriv j Real.smoothTransition x| ≤ B)
    (a x : ℝ) (j : ℕ) (hj : j ≤ s) :
    |iteratedDeriv j (fun y => Analysis.intervalLayerThreshold δ (y - a)) x| ≤ B * L ^ s ∧
      |iteratedDeriv j (fun y => Analysis.intervalLayerThreshold δ (a - y)) x| ≤ B * L ^ s := by
  have hpow : δ⁻¹ ^ j ≤ L ^ s :=
    (pow_le_pow_left₀ (inv_nonneg.mpr hδ.le) hδL j).trans
      (pow_le_pow_right₀ hL hj)
  have hbase (t : ℝ) : |iteratedDeriv j (Analysis.intervalLayerThreshold δ) t| ≤ B * L ^ s := by
    rw [n08_intervalLayerThreshold_jet, abs_mul,
      abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hδ.le) _)]
    exact (mul_le_mul hpow (hb j hj _) (abs_nonneg _)
      (pow_nonneg (zero_le_one.trans hL) _)).trans_eq (mul_comm _ _)
  constructor
  · simpa only [iteratedDeriv_comp_sub_const] using hbase (x - a)
  · simpa only [iteratedDeriv_comp_const_sub, smul_eq_mul, abs_mul, abs_pow,
      abs_neg, abs_one, one_pow, one_mul] using hbase (a - x)

theorem n08_jetPrefix_mul_bound {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) {s : ℕ} {x A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbF : ∀ j ≤ s, |iteratedDeriv j f x| ≤ A)
    (hbG : ∀ j ≤ s, |iteratedDeriv j g x| ≤ B) (n : ℕ) (hn : n ≤ s) :
    |iteratedDeriv n (fun y => f y * g y) x| ≤ (2 : ℝ) ^ s * A * B := by
  rw [iteratedDeriv_fun_mul (hf.contDiffAt.of_le (by simp)) (hg.contDiffAt.of_le (by simp))]
  have hchoose : ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) = (2 : ℝ) ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * A * B := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
      have hjs : j ≤ s := (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hn
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hbF j hjs) (Nat.cast_nonneg _))
        (hbG (n - j) ((Nat.sub_le _ _).trans hn)) (abs_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = (2 : ℝ) ^ n * A * B := by rw [← Finset.sum_mul, ← Finset.sum_mul, hchoose]
    _ ≤ (2 : ℝ) ^ s * A * B :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hA) hB

theorem n08_jetPrefix_one_sub_bound {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {s : ℕ} {x B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j ≤ s, |iteratedDeriv j f x| ≤ B) (j : ℕ) (hj : j ≤ s) :
    |iteratedDeriv j (fun y => 1 - f y) x| ≤ 1 + B := by
  by_cases hz : j = 0
  · subst j
    rw [iteratedDeriv_zero]
    calc
      |1 - f x| ≤ |1| + |f x| := abs_sub _ _
      _ = 1 + |f x| := by rw [abs_one]
      _ ≤ 1 + B := add_le_add le_rfl
        (by simpa only [iteratedDeriv_zero] using hb 0 (Nat.zero_le s))
  · rw [iteratedDeriv_const_sub (Nat.pos_of_ne_zero hz), iteratedDeriv_neg, abs_neg]
    exact (hb j hj).trans (le_add_of_nonneg_left zero_le_one)

/-- The exponent is deliberately coarse; every fixed inverse-width power
will be absorbed by one positive material-height power. -/
theorem n08_intervalLayerCutoff_jet_bound (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a b δ Δ : ℝ, 0 < δ → δ ≤ 1 → δ ≤ Δ → ∀ x : ℝ,
      |iteratedDeriv s (Analysis.intervalLayerCutoff a b δ Δ) x| ≤
        K * δ⁻¹ ^ (4 * s) := by
  obtain ⟨B, hB, hb⟩ := n08_smoothTransition_prefix_bound s
  let C : ℝ := (2 : ℝ) ^ s * (B * (2 : ℝ) ^ s) * (B * (2 : ℝ) ^ s)
  refine ⟨(2 : ℝ) ^ s * C * (2 * C), by dsimp only [C]; positivity, ?_⟩
  intro a b δ Δ hδ hδ1 hδΔ x
  let L : ℝ := 2 * δ⁻¹
  have hR : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ1
  have hL : 1 ≤ L := by dsimp only [L]; linarith
  have hδh : 0 < δ / 2 := by positivity
  have hhL : (δ / 2)⁻¹ ≤ L := by
    dsimp only [L]
    rw [inv_div, div_eq_mul_inv]
  have hΔ : 0 < Δ := hδ.trans_le hδΔ
  have hΔL : Δ⁻¹ ≤ L := (inv_anti₀ hδ hδΔ).trans (by dsimp only [L]; linarith)
  let f : ℝ → ℝ := fun y => Analysis.intervalLayerThreshold (δ / 2) (y - a)
  let g : ℝ → ℝ := fun y => Analysis.intervalLayerThreshold (δ / 2) (b - y)
  let h : ℝ → ℝ := fun y => Analysis.intervalLayerThreshold Δ (y - a)
  let k : ℝ → ℝ := fun y => Analysis.intervalLayerThreshold Δ (b - y)
  have hf : ContDiff ℝ ∞ f := (Analysis.contDiff_intervalLayerThreshold _).comp
    (contDiff_id.sub contDiff_const)
  have hg : ContDiff ℝ ∞ g := (Analysis.contDiff_intervalLayerThreshold _).comp
    (contDiff_const.sub contDiff_id)
  have hh : ContDiff ℝ ∞ h := (Analysis.contDiff_intervalLayerThreshold _).comp
    (contDiff_id.sub contDiff_const)
  have hk : ContDiff ℝ ∞ k := (Analysis.contDiff_intervalLayerThreshold _).comp
    (contDiff_const.sub contDiff_id)
  let V : ℝ := B * L ^ s
  let Q : ℝ := (2 : ℝ) ^ s * V * V
  have hV : 1 ≤ V := one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hL)
  have hQ : 1 ≤ Q := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hV) hV
  have hfg (j : ℕ) (hj : j ≤ s) : |iteratedDeriv j (fun y => f y * g y) x| ≤ Q :=
    n08_jetPrefix_mul_bound hf hg (zero_le_one.trans hV) (zero_le_one.trans hV)
      (fun i hi => (n08_threshold_prefix_bound (zero_le_one.trans hB) hL hδh hhL hb a x i hi).1)
      (fun i hi => (n08_threshold_prefix_bound (zero_le_one.trans hB) hL hδh hhL hb b x i hi).2) j hj
  have hhk (j : ℕ) (hj : j ≤ s) : |iteratedDeriv j (fun y => h y * k y) x| ≤ Q :=
    n08_jetPrefix_mul_bound hh hk (zero_le_one.trans hV) (zero_le_one.trans hV)
      (fun i hi => (n08_threshold_prefix_bound (zero_le_one.trans hB) hL hΔ hΔL hb a x i hi).1)
      (fun i hi => (n08_threshold_prefix_bound (zero_le_one.trans hB) hL hΔ hΔL hb b x i hi).2) j hj
  have hout (j : ℕ) (hj : j ≤ s) :
      |iteratedDeriv j (fun y => 1 - h y * k y) x| ≤ 2 * Q :=
    (n08_jetPrefix_one_sub_bound (hh.mul hk) (zero_le_one.trans hQ) hhk j hj).trans
      (by linarith)
  have hfinal := n08_jetPrefix_mul_bound (hf.mul hg) (contDiff_const.sub (hh.mul hk))
    (zero_le_one.trans hQ) (by positivity : 0 ≤ 2 * Q) hfg hout s le_rfl
  have hQeq : Q = C * (δ⁻¹ ^ s) ^ 2 := by
    dsimp only [Q, V, L, C]
    rw [mul_pow]
    ring
  change |iteratedDeriv s (fun y => (f y * g y) * (1 - h y * k y)) x| ≤ _
  apply hfinal.trans_eq
  rw [hQeq, show 4 * s = s * 4 by omega, pow_mul]
  ring

end ContinuousFlexibility.Statements
