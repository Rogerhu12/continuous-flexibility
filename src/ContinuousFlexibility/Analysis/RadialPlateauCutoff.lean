module

public import ContinuousFlexibility.Analysis.CompactRadialHeightMember
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Quantitative radial plateau cutoffs

The same fixed smooth transition is translated and rescaled at the two
ends of an interval. The cutoff equals one on the whole closed interval,
has an explicit exterior collar, and its order-n derivative loses only
the n-th power of the collar width.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

theorem smoothTransition_iteratedDeriv_bounded (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, |iteratedDeriv n Real.smoothTransition x| ≤ K := by
  have hreg : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  cases n with
  | zero =>
    refine ⟨1, zero_le_one, fun x => ?_⟩
    simpa only [iteratedDeriv_zero, abs_of_nonneg (Real.smoothTransition.nonneg x)] using
      Real.smoothTransition.le_one x
  | succ n =>
    have hsupp : HasCompactSupport (iteratedDeriv (n + 1) Real.smoothTransition) := by
      apply HasCompactSupport.intro (K := Icc (0 : ℝ) 1) isCompact_Icc
      intro x hx
      simp only [mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · have hn : ∀ᶠ y : ℝ in 𝓝 x, y < 0 := Iio_mem_nhds hx
        have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => 0) :=
          hn.mono (fun y hy => Real.smoothTransition.zero_of_nonpos hy.le)
        simpa only [iteratedDeriv_const, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          ite_false] using heq.iteratedDeriv_eq (n + 1)
      · have hn : ∀ᶠ y : ℝ in 𝓝 x, 1 < y := Ioi_mem_nhds hx
        have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => 1) :=
          hn.mono (fun y hy => Real.smoothTransition.one_of_one_le hy.le)
        simpa only [iteratedDeriv_const, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          ite_false] using heq.iteratedDeriv_eq (n + 1)
    have hc := hreg.continuous_iteratedDeriv (n + 1) (by simp)
    obtain ⟨K, hK⟩ := hsupp.exists_bound_of_continuous hc
    refine ⟨max K 0, le_max_right _ _, fun x => ?_⟩
    have hb : |iteratedDeriv (n + 1) Real.smoothTransition x| ≤ K := by
      simpa only [Real.norm_eq_abs] using hK x
    exact hb.trans (le_max_left _ _)

theorem iteratedDeriv_comp_affine_real {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (a b x : ℝ) :
    iteratedDeriv n (fun t => f (a * t + b)) x =
      a ^ n * iteratedDeriv n f (a * x + b) := by
  let g : ℝ → ℝ := fun t => f (t + b)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  have h := congrFun (iteratedDeriv_comp_const_mul (n := n) (hg.of_le (by simp)) a) x
  simpa only [g, iteratedDeriv_comp_add_const] using h

def radialPlateauCutoff (l r δ : ℝ) : ℝ → ℝ :=
  fun x => Real.smoothTransition ((x - l) / δ + 1) *
    Real.smoothTransition ((r - x) / δ + 1)

theorem radialPlateauCutoff_contDiff (l r δ : ℝ) :
    ContDiff ℝ ∞ (radialPlateauCutoff l r δ) :=
  (Real.smoothTransition.contDiff.comp (((contDiff_id.sub contDiff_const).div_const δ).add contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp (((contDiff_const.sub contDiff_id).div_const δ).add contDiff_const))

theorem radialPlateauCutoff_one {l r δ : ℝ} (hδ : 0 < δ)
    {x : ℝ} (hx : x ∈ Icc l r) : radialPlateauCutoff l r δ x = 1 := by
  have hl : 1 ≤ (x - l) / δ + 1 := le_add_of_nonneg_left (div_nonneg (sub_nonneg.mpr hx.1) hδ.le)
  have hr : 1 ≤ (r - x) / δ + 1 := le_add_of_nonneg_left (div_nonneg (sub_nonneg.mpr hx.2) hδ.le)
  simp only [radialPlateauCutoff, Real.smoothTransition.one_of_one_le hl,
    Real.smoothTransition.one_of_one_le hr, one_mul]

theorem radialPlateauCutoff_zero {l r δ : ℝ} (hδ : 0 < δ)
    {x : ℝ} (hx : x ∉ Ioo (l - δ) (r + δ)) : radialPlateauCutoff l r δ x = 0 := by
  simp only [mem_Ioo, not_and_or, not_lt] at hx
  rcases hx with hx | hx
  · have harg : (x - l) / δ + 1 ≤ 0 := by
      have hdiv : (x - l) / δ ≤ -1 := (div_le_iff₀ hδ).mpr (by linarith)
      linarith
    simp only [radialPlateauCutoff, Real.smoothTransition.zero_of_nonpos harg, zero_mul]
  · have harg : (r - x) / δ + 1 ≤ 0 := by
      have hdiv : (r - x) / δ ≤ -1 := (div_le_iff₀ hδ).mpr (by linarith)
      linarith
    simp only [radialPlateauCutoff, Real.smoothTransition.zero_of_nonpos harg, mul_zero]

theorem radialPlateauCutoff_hasCompactSupport {l r δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (radialPlateauCutoff l r δ) :=
  HasCompactSupport.intro isCompact_Icc
    (fun _ hx => radialPlateauCutoff_zero hδ (fun h => hx ⟨h.1.le, h.2.le⟩))

/-- Every derivative order has one constant for all locations and widths. -/
theorem radialPlateauCutoff_iteratedDeriv_bound (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ l r δ : ℝ, 0 < δ → ∀ x : ℝ,
      |iteratedDeriv n (radialPlateauCutoff l r δ) x| ≤ K / δ ^ n := by
  classical
  choose A hA hbound using smoothTransition_iteratedDeriv_bounded
  let K : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i * A (n - i)
  have hK : 0 ≤ K := Finset.sum_nonneg (fun i hi =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hA (n - i)))
  refine ⟨K, hK, fun l r δ hδ x => ?_⟩
  let L : ℝ → ℝ := fun t => Real.smoothTransition ((t - l) / δ + 1)
  let R : ℝ → ℝ := fun t => Real.smoothTransition ((r - t) / δ + 1)
  have hL : ContDiff ℝ ∞ L :=
    Real.smoothTransition.contDiff.comp (((contDiff_id.sub contDiff_const).div_const δ).add contDiff_const)
  have hR : ContDiff ℝ ∞ R :=
    Real.smoothTransition.contDiff.comp (((contDiff_const.sub contDiff_id).div_const δ).add contDiff_const)
  have hLjet (i : ℕ) :
      |iteratedDeriv i L x| ≤ δ⁻¹ ^ i * A i := by
    have heq : L = fun t => Real.smoothTransition (δ⁻¹ * t + (1 - l / δ)) := by
      funext t
      dsimp only [L]
      congr 1
      ring
    rw [heq, iteratedDeriv_comp_affine_real Real.smoothTransition.contDiff,
      abs_mul, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hδ.le) i)]
    exact mul_le_mul_of_nonneg_left (hbound i _) (pow_nonneg (inv_nonneg.mpr hδ.le) i)
  have hRjet (i : ℕ) :
      |iteratedDeriv i R x| ≤ δ⁻¹ ^ i * A i := by
    have heq : R = fun t => Real.smoothTransition ((-δ⁻¹) * t + (1 + r / δ)) := by
      funext t
      dsimp only [R]
      congr 1
      ring
    rw [heq, iteratedDeriv_comp_affine_real Real.smoothTransition.contDiff,
      abs_mul, abs_pow, abs_neg, abs_of_nonneg (inv_nonneg.mpr hδ.le)]
    exact mul_le_mul_of_nonneg_left (hbound i _) (pow_nonneg (inv_nonneg.mpr hδ.le) i)
  have hprod : iteratedDeriv n (radialPlateauCutoff l r δ) x =
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * iteratedDeriv i L x * iteratedDeriv (n - i) R x :=
    iteratedDeriv_fun_mul (hL.contDiffAt.of_le (by simp)) (hR.contDiffAt.of_le (by simp))
  rw [hprod]
  calc
    |∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * iteratedDeriv i L x * iteratedDeriv (n - i) R x| ≤
        ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * |iteratedDeriv i L x| * |iteratedDeriv (n - i) R x| := by
      apply (Finset.abs_sum_le_sum_abs
        (fun i => (n.choose i : ℝ) * iteratedDeriv i L x * iteratedDeriv (n - i) R x)
        (Finset.range (n + 1))).trans_eq
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (n.choose i))]
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * (δ⁻¹ ^ i * A i) * (δ⁻¹ ^ (n - i) * A (n - i)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hLjet i) (Nat.cast_nonneg _)) (hRjet (n - i))
        (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (pow_nonneg (inv_nonneg.mpr hδ.le) i) (hA i)))
    _ = K * δ⁻¹ ^ n := by
      dsimp only [K]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hpow : δ⁻¹ ^ i * δ⁻¹ ^ (n - i) = δ⁻¹ ^ n := by
        rw [← pow_add, Nat.add_sub_of_le hin]
      calc
        _ = ((n.choose i : ℝ) * A i * A (n - i)) *
            (δ⁻¹ ^ i * δ⁻¹ ^ (n - i)) := by ring
        _ = _ := by rw [hpow]
    _ = K / δ ^ n := by rw [inv_pow, div_eq_mul_inv]

end ContinuousFlexibility.Statements
