import ContinuousFlexibility.Statements.Radial
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Topology.Order.Compact

/-!
# Optical lower bounds on finitely many actual negative components

A positive function with simple endpoint zeros dominates the distance to the
two endpoints.  We prove this using the continuous divided differences on
the two closed half intervals.  For a real negative component of a radial
profile, this applies to `-deriv w`; the positive continuous denominator
`r * w r` then gives the same lower bound for the actual optical ratio.

The constants are obtained from compactness.  Thus this module handles a
fixed component, or a finite collection of components.  It does not assert
a uniform quantitative bound on an infinite family of components; that
requires the actual tail geometry.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped Topology

/-- Simple zeros and strict positivity in the interior give a positive
linear lower bound in the distance to the endpoints. -/
theorem exists_linear_distance_lower_bound_of_simple_zeros
    {f : ℝ → ℝ} {l h dl dh : ℝ}
    (hlh : l < h) (hf : Continuous f)
    (hl : HasDerivAt f dl l) (hh : HasDerivAt f dh h)
    (hfl : f l = 0) (hfh : f h = 0)
    (hdl : dl ≠ 0) (hdh : dh ≠ 0)
    (hpos : ∀ r ∈ Ioo l h, 0 < f r) :
    ∃ c : ℝ, 0 < c ∧ ∀ r ∈ Icc l h,
      c * min (r - l) (h - r) ≤ f r := by
  let m : ℝ := (l + h) / 2
  have hlm : l < m := by dsimp only [m]; linarith
  have hmh : m < h := by dsimp only [m]; linarith
  have hcL : Continuous (dslope f l) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    by_cases hr : r = l
    · subst r
      exact continuousAt_dslope_same.mpr hl.differentiableAt
    · exact (continuousAt_dslope_of_ne hr).mpr hf.continuousAt
  have hcR : Continuous (dslope f h) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    by_cases hr : r = h
    · subst r
      exact continuousAt_dslope_same.mpr hh.differentiableAt
    · exact (continuousAt_dslope_of_ne hr).mpr hf.continuousAt
  have hposL (r : ℝ) (hr : r ∈ Icc l m) : 0 < |dslope f l r| := by
    by_cases he : r = l
    · subst r
      rw [dslope_same, hl.deriv]
      exact abs_pos.mpr hdl
    · have hri : r ∈ Ioo l h :=
        ⟨(lt_or_eq_of_le hr.1).resolve_right he.symm, hr.2.trans_lt hmh⟩
      apply abs_pos.mpr
      intro hz
      have hid : (r - l) * dslope f l r = f r := by
        simpa only [smul_eq_mul, hfl, sub_zero] using sub_smul_dslope f l r
      rw [hz, mul_zero] at hid
      exact (hpos r hri).ne' hid.symm
  have hposR (r : ℝ) (hr : r ∈ Icc m h) : 0 < |dslope f h r| := by
    by_cases he : r = h
    · subst r
      rw [dslope_same, hh.deriv]
      exact abs_pos.mpr hdh
    · have hri : r ∈ Ioo l h :=
        ⟨hlm.trans_le hr.1, (lt_or_eq_of_le hr.2).resolve_right he⟩
      apply abs_pos.mpr
      intro hz
      have hid : (r - h) * dslope f h r = f r := by
        simpa only [smul_eq_mul, hfh, sub_zero] using sub_smul_dslope f h r
      rw [hz, mul_zero] at hid
      exact (hpos r hri).ne' hid.symm
  obtain ⟨cL, hcLpos, hcLbound⟩ :=
    (isCompact_Icc : IsCompact (Icc l m)).exists_forall_le'
      hcL.abs.continuousOn hposL
  obtain ⟨cR, hcRpos, hcRbound⟩ :=
    (isCompact_Icc : IsCompact (Icc m h)).exists_forall_le'
      hcR.abs.continuousOn hposR
  have hnonneg (r : ℝ) (hr : r ∈ Icc l h) : 0 ≤ f r := by
    by_cases hel : r = l
    · simpa only [hel, hfl] using (le_refl (0 : ℝ))
    by_cases heh : r = h
    · simpa only [heh, hfh] using (le_refl (0 : ℝ))
    exact (hpos r ⟨(lt_or_eq_of_le hr.1).resolve_right hel.symm,
      (lt_or_eq_of_le hr.2).resolve_right heh⟩).le
  refine ⟨min cL cR, lt_min hcLpos hcRpos, fun r hr => ?_⟩
  have hdelta : 0 ≤ min (r - l) (h - r) :=
    le_min (sub_nonneg.mpr hr.1) (sub_nonneg.mpr hr.2)
  by_cases hrm : r ≤ m
  · have hid : (r - l) * |dslope f l r| = f r := by
      have he := congrArg abs (sub_smul_dslope f l r)
      simpa only [smul_eq_mul, abs_mul, hfl, sub_zero,
        abs_of_nonneg (sub_nonneg.mpr hr.1), abs_of_nonneg (hnonneg r hr)] using he
    calc
      min cL cR * min (r - l) (h - r) ≤ cL * (r - l) :=
        mul_le_mul (min_le_left _ _) (min_le_left _ _) hdelta hcLpos.le
      _ ≤ |dslope f l r| * (r - l) :=
        mul_le_mul_of_nonneg_right (hcLbound r ⟨hr.1, hrm⟩) (sub_nonneg.mpr hr.1)
      _ = f r := by rw [mul_comm]; exact hid
  · have hmr : m ≤ r := (lt_of_not_ge hrm).le
    have hid : (h - r) * |dslope f h r| = f r := by
      have he := congrArg abs (sub_smul_dslope f h r)
      have hdist : |r - h| = h - r := by
        rw [abs_of_nonpos (sub_nonpos.mpr hr.2)]
        ring
      simpa only [smul_eq_mul, abs_mul, hfh, sub_zero, hdist,
        abs_of_nonneg (hnonneg r hr)] using he
    calc
      min cL cR * min (r - l) (h - r) ≤ cR * (h - r) :=
        mul_le_mul (min_le_right _ _) (min_le_right _ _) hdelta hcRpos.le
      _ ≤ |dslope f h r| * (h - r) :=
        mul_le_mul_of_nonneg_right (hcRbound r ⟨hmr, hr.2⟩) (sub_nonneg.mpr hr.2)
      _ = f r := by rw [mul_comm]; exact hid

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

/-- A fixed actual negative component has an optical lower bound all the
way to both simple turning points.  No quantitative optical hypothesis is
an input. -/
theorem negativeRadialComponent_optical_lower_bound
    {D : ReferenceData} {l h : ℝ}
    (hD : RadialProfileGeometry D) (hcomponent : NegativeRadialComponent D l h) :
    ∃ c : ℝ, 0 < c ∧ ∀ r ∈ Icc l h,
      c * min (r - l) (h - r) ≤ -deriv D.w r / (r * D.w r) := by
  obtain ⟨ha, _, hw, _, hwpos, _, hsimple⟩ := hD
  obtain ⟨hal, hlh, hhb, hleft, hright, hneg⟩ := hcomponent
  have hlcore : l ∈ radialCore D := ⟨hal, hlh.trans hhb⟩
  have hhcore : h ∈ radialCore D := ⟨hal.trans hlh, hhb⟩
  have hwd : ContDiff ℝ ∞ (deriv D.w) := (contDiff_infty_iff_deriv.mp hw.1).2
  let F : ℝ → ℝ := fun r => -deriv D.w r
  have hFc : Continuous F := hwd.continuous.neg
  have hFl : HasDerivAt F (-deriv (deriv D.w) l) l := by
    simpa only [F, Pi.neg_apply] using
      ((hwd.differentiable (by simp)) l).hasDerivAt.neg
  have hFh : HasDerivAt F (-deriv (deriv D.w) h) h := by
    simpa only [F, Pi.neg_apply] using
      ((hwd.differentiable (by simp)) h).hasDerivAt.neg
  obtain ⟨c, hc, hbound⟩ :=
    Analysis.exists_linear_distance_lower_bound_of_simple_zeros hlh hFc hFl hFh
      (by simp only [F, hleft, neg_zero]) (by simp only [F, hright, neg_zero])
      (neg_ne_zero.mpr (hsimple l hlcore hleft))
      (neg_ne_zero.mpr (hsimple h hhcore hright))
      (fun r hr => neg_pos.mpr (hneg r hr))
  have hdenom (r : ℝ) (hr : r ∈ Icc l h) : 0 < r * D.w r :=
    mul_pos ((ha.trans hal).trans_le hr.1)
      (hwpos r ⟨hal.trans_le hr.1, hr.2.trans_lt hhb⟩)
  obtain ⟨x, hx, hmax⟩ :=
    (isCompact_Icc : IsCompact (Icc l h)).exists_isMaxOn
      ⟨l, le_rfl, hlh.le⟩ (continuous_id.mul hw.1.continuous).continuousOn
  let M : ℝ := x * D.w x
  have hM : 0 < M := hdenom x hx
  refine ⟨c / M, div_pos hc hM, fun r hr => ?_⟩
  have hMbound : r * D.w r ≤ M := hmax hr
  have hFnonneg : 0 ≤ F r :=
    (mul_nonneg hc.le
      (le_min (sub_nonneg.mpr hr.1) (sub_nonneg.mpr hr.2))).trans (hbound r hr)
  change (c / M) * min (r - l) (h - r) ≤ F r / (r * D.w r)
  rw [show (c / M) * min (r - l) (h - r) =
    (c * min (r - l) (h - r)) / M by ring]
  exact (div_le_div_iff₀ hM (hdenom r hr)).mpr
    (mul_le_mul (hbound r hr) hMbound (hdenom r hr).le hFnonneg)

/-- The optical constants can be chosen uniformly over any finite head
of actual components.  This is the compact part of the tail/head assembly. -/
theorem finite_negativeRadialComponents_optical_lower_bound
    {ι : Type*} {D : ReferenceData} (hD : RadialProfileGeometry D)
    (left right : ι → ℝ) (s : Finset ι)
    (hcomponents : ∀ i ∈ s, NegativeRadialComponent D (left i) (right i)) :
    ∃ c : ℝ, 0 < c ∧ ∀ i ∈ s, ∀ r ∈ Icc (left i) (right i),
      c * min (r - left i) (right i - r) ≤ -deriv D.w r / (r * D.w r) := by
  classical
  revert hcomponents
  induction s using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨1, zero_lt_one, ?_⟩
    intro i hi
    simp at hi
  | @insert i s hi ih =>
    intro hcomponents
    obtain ⟨ci, hci, hibound⟩ :=
      negativeRadialComponent_optical_lower_bound hD (hcomponents i (by simp))
    obtain ⟨cs, hcs, hsbound⟩ := ih
      (fun j hj => hcomponents j (Finset.mem_insert_of_mem hj))
    refine ⟨min ci cs, lt_min hci hcs, fun j hj r hr => ?_⟩
    have hdelta : 0 ≤ min (r - left j) (right j - r) :=
      le_min (sub_nonneg.mpr hr.1) (sub_nonneg.mpr hr.2)
    rcases Finset.mem_insert.mp hj with rfl | hjs
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hdelta).trans (hibound r hr)
    · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hdelta).trans
        (hsbound j hjs r hr)

end ContinuousFlexibility.Statements
