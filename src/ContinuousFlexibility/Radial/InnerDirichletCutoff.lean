import ContinuousFlexibility.Radial.OscillatorCompactCore
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Smooth cutoffs at the two endpoints of a finite interval

The two endpoint factors use one transition function and one derivative estimate.
When a field vanishes at an endpoint, the factor of the cutoff scale in its
derivative is cancelled by the linear vanishing of the field.  This is the
uniform bound needed for convergence in the actual Dirichlet energy domain.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff

private theorem innerTransition_eventually_zero {x : ℝ} (hx : x < 0) :
    smoothTransition =ᶠ[𝓝 x] (fun _ => 0) := by
  filter_upwards [Iio_mem_nhds hx] with y hy
  exact smoothTransition.zero_of_nonpos hy.le

private theorem innerTransition_eventually_one {x : ℝ} (hx : 1 < x) :
    smoothTransition =ᶠ[𝓝 x] (fun _ => 1) := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact smoothTransition.one_of_one_le hy.le

theorem innerTransition_deriv_eq_zero {x : ℝ} (hx : x ∉ Icc (0 : ℝ) 1) :
    deriv smoothTransition x = 0 := by
  rcases lt_or_ge x 0 with hneg | hnonneg
  · exact (innerTransition_eventually_zero hneg).deriv_eq.trans (deriv_const x 0)
  · have hpos : 1 < x := lt_of_not_ge (fun h => hx ⟨hnonneg, h⟩)
    exact (innerTransition_eventually_one hpos).deriv_eq.trans (deriv_const x 1)

theorem innerTransition_deriv_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |deriv smoothTransition x| ≤ C := by
  have hc : Continuous (deriv smoothTransition) :=
    (smoothTransition.contDiff : ContDiff ℝ ∞ smoothTransition).continuous_deriv (by simp)
  have hs : HasCompactSupport (deriv smoothTransition) :=
    HasCompactSupport.intro isCompact_Icc (fun x hx => innerTransition_deriv_eq_zero hx)
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨max 0 C, le_max_left _ _, fun x => (hC x).trans (le_max_right _ _)⟩

/-- The same scalar estimate applies to the distance from either endpoint. -/
theorem innerTransition_deriv_mul_bound {k t v C M : ℝ}
    (hk : 0 < k) (ht : 0 ≤ t) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hderiv : ∀ x, |deriv smoothTransition x| ≤ C) (hv : |v| ≤ M * t) :
    |deriv smoothTransition (k * t - 1) * k * v| ≤ 2 * C * M := by
  by_cases hlarge : 1 < k * t - 1
  · have hz := innerTransition_deriv_eq_zero
      (x := k * t - 1) (fun h => (not_lt_of_ge h.2) hlarge)
    rw [hz, zero_mul, zero_mul, abs_zero]
    positivity
  · have hkt : k * t ≤ 2 := by linarith
    calc
      |deriv smoothTransition (k * t - 1) * k * v| =
          |deriv smoothTransition (k * t - 1)| * k * |v| := by
            rw [abs_mul, abs_mul, abs_of_pos hk]
      _ ≤ C * k * (M * t) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hderiv _) hk.le) hv
          (abs_nonneg _) (mul_nonneg hC hk.le)
      _ = C * M * (k * t) := by ring
      _ ≤ C * M * 2 := mul_le_mul_of_nonneg_left hkt (mul_nonneg hC hM)
      _ = 2 * C * M := by ring

/-- This cutoff is zero on a neighbourhood of both endpoints and one on every
fixed compact subinterval once its scale is sufficiently large. -/
def innerDirichletCutoff (a b k x : ℝ) : ℝ :=
  smoothTransition (k * (x - a) - 1) * smoothTransition (k * (b - x) - 1)

theorem innerDirichletCutoff_contDiff (a b k : ℝ) :
    ContDiff ℝ ∞ (innerDirichletCutoff a b k) := by
  exact (smoothTransition.contDiff.comp
    (((contDiff_id.sub contDiff_const).const_mul k).sub contDiff_const)).mul
      (smoothTransition.contDiff.comp
        (((contDiff_const.sub contDiff_id).const_mul k).sub contDiff_const))

theorem innerDirichletCutoff_nonneg (a b k x : ℝ) :
    0 ≤ innerDirichletCutoff a b k x :=
  mul_nonneg (smoothTransition.nonneg _) (smoothTransition.nonneg _)

theorem innerDirichletCutoff_le_one (a b k x : ℝ) :
    innerDirichletCutoff a b k x ≤ 1 := by
  exact (mul_le_mul (smoothTransition.le_one _) (smoothTransition.le_one _)
    (smoothTransition.nonneg _) zero_le_one).trans_eq (mul_one 1)

theorem innerDirichletCutoff_eventually_zero {a b k x : ℝ}
    (hk : 0 < k) (hx : x ∉ Ioo a b) :
    innerDirichletCutoff a b k =ᶠ[𝓝 x] (fun _ => 0) := by
  have hzero {g : ℝ → ℝ} (hg : ContinuousAt g x) (hgx : g x < 0) :
      (fun y => smoothTransition (g y)) =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [hg.preimage_mem_nhds (Iio_mem_nhds hgx)] with y hy
    exact smoothTransition.zero_of_nonpos hy.le
  by_cases hleft : x ≤ a
  · have h := hzero (g := fun y => k * (y - a) - 1)
      (by fun_prop) (by nlinarith)
    filter_upwards [h] with y hy
    simp only [innerDirichletCutoff, hy, zero_mul]
  · have hright : b ≤ x := le_of_not_gt (fun h => hx ⟨lt_of_not_ge hleft, h⟩)
    have h := hzero (g := fun y => k * (b - y) - 1)
      (by fun_prop) (by nlinarith)
    filter_upwards [h] with y hy
    simp only [innerDirichletCutoff, hy, mul_zero]

theorem innerDirichletCutoff_support {a b k : ℝ} (hk : 0 < k) :
    Function.support (innerDirichletCutoff a b k) ⊆ Ioo a b := by
  intro x hx
  by_contra hout
  exact hx (innerDirichletCutoff_eventually_zero hk hout).eq_of_nhds

theorem innerDirichletCutoff_hasCompactSupport {a b k : ℝ} (hk : 0 < k) :
    HasCompactSupport (innerDirichletCutoff a b k) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc a b))
  intro x hx
  exact (innerDirichletCutoff_eventually_zero hk
    (fun h => hx (Ioo_subset_Icc_self h))).eq_of_nhds

theorem innerDirichletCutoff_eventually_one {a b k x : ℝ}
    (hleft : 2 < k * (x - a)) (hright : 2 < k * (b - x)) :
    innerDirichletCutoff a b k =ᶠ[𝓝 x] (fun _ => 1) := by
  have hL : ∀ᶠ y in 𝓝 x, 1 < k * (y - a) - 1 :=
    (show ContinuousAt (fun y : ℝ => k * (y - a) - 1) x by fun_prop).preimage_mem_nhds
      (Ioi_mem_nhds (by linarith))
  have hR : ∀ᶠ y in 𝓝 x, 1 < k * (b - y) - 1 :=
    (show ContinuousAt (fun y : ℝ => k * (b - y) - 1) x by fun_prop).preimage_mem_nhds
      (Ioi_mem_nhds (by linarith))
  filter_upwards [hL, hR] with y hyL hyR
  simp only [innerDirichletCutoff, smoothTransition.one_of_one_le hyL.le,
    smoothTransition.one_of_one_le hyR.le, mul_one]

theorem innerDirichletCutoff_eventually_one_atTop {a b x : ℝ} (hx : x ∈ Ioo a b) :
    ∀ᶠ n : ℕ in atTop,
      innerDirichletCutoff a b ((n : ℝ) + 1) =ᶠ[𝓝 x] (fun _ => 1) := by
  have hL : 0 < x - a := sub_pos.mpr hx.1
  have hR : 0 < b - x := sub_pos.mpr hx.2
  obtain ⟨N, hN⟩ := exists_nat_gt (max (2 / (x - a)) (2 / (b - x)))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  apply innerDirichletCutoff_eventually_one
  · have h : 2 / (x - a) < (n : ℝ) + 1 :=
      (lt_of_le_of_lt (le_max_left _ _) hN).trans_le (by linarith)
    exact (div_lt_iff₀ hL).mp h
  · have h : 2 / (b - x) < (n : ℝ) + 1 :=
      (lt_of_le_of_lt (le_max_right _ _) hN).trans_le (by linarith)
    exact (div_lt_iff₀ hR).mp h

/-- Multiplication by the cutoff is smooth even when the original function
is only known to be smooth on a neighbourhood of the closed interval. -/
theorem innerDirichletCutoff_mul_contDiff {a b k : ℝ} {u : ℝ → ℝ}
    (hk : 0 < k) (hu : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ u x) :
    ContDiff ℝ ∞ (fun x => innerDirichletCutoff a b k x * u x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ Ioo a b
  · exact (innerDirichletCutoff_contDiff a b k).contDiffAt.mul
      (hu x (Ioo_subset_Icc_self hx))
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [innerDirichletCutoff_eventually_zero hk hx] with y hy
    exact show innerDirichletCutoff a b k y * u y = 0 by rw [hy, zero_mul]

theorem innerDirichletCutoff_mul_support {a b k : ℝ} {u : ℝ → ℝ} (hk : 0 < k) :
    Function.support (fun x => innerDirichletCutoff a b k x * u x) ⊆ Ioo a b := by
  intro x hx
  apply innerDirichletCutoff_support hk
  intro hzero
  exact hx (by rw [hzero, zero_mul])

theorem innerDirichlet_endpoint_bound {a b c x M : ℝ} {u : ℝ → ℝ}
    (hu : ∀ y ∈ Icc a b, DifferentiableAt ℝ u y)
    (hM : ∀ y ∈ Icc a b, |deriv u y| ≤ M)
    (hc : c ∈ Icc a b) (hx : x ∈ Icc a b) (huc : u c = 0) :
    |u x| ≤ M * |x - c| := by
  have h := norm_image_sub_le_of_norm_deriv_le hu
    (fun y hy => by simpa only [Real.norm_eq_abs] using hM y hy) (convex_Icc a b) hc hx
  simpa only [huc, sub_zero, Real.norm_eq_abs] using h

end ContinuousFlexibility.Radial
