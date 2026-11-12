import ContinuousFlexibility.Analysis.PositiveComponentEndpoints
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Topology.Order.Compact

/-!
# A physical lower coefficient on one actual positive component

The derivative has simple zeroes at the two actual interior endpoints.
On each half interval its divided slope is continuous and nonzero,
including at that endpoint. Compactness gives one positive coefficient
for this component. This qualitative coefficient is used only for the
finite central exceptions; no uniform tail estimate is inferred here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

private theorem positiveInterval_simple_root_min_lower
    {f : ℝ → ℝ} {l u : ℝ} (hlu : l < u) (hf : Continuous f)
    (hpos : ∀ x ∈ Ioo l u, 0 < f x)
    (hend : ∀ side : Bool,
      f (if side then u else l) = 0 ∧
        DifferentiableAt ℝ f (if side then u else l) ∧
        deriv f (if side then u else l) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Icc l u,
      c * min (x - l) (u - x) ≤ f x := by
  let m : ℝ := (l + u) / 2
  have hlm : l < m := by dsimp only [m]; linarith only [hlu]
  have hmu : m < u := by dsimp only [m]; linarith only [hlu]
  have hside (side : Bool) : ∃ b : ℝ, 0 < b ∧
      ∀ x ∈ uIcc (if side then u else l) m,
        b ≤ |dslope f (if side then u else l) x| := by
    let e : ℝ := if side then u else l
    have hezero : f e = 0 := (hend side).1
    have hcontinuous : Continuous (dslope f e) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      by_cases he : x = e
      · subst x
        exact continuousAt_dslope_same.mpr (hend side).2.1
      · exact (continuousAt_dslope_of_ne he).mpr hf.continuousAt
    have hpositive : ∀ x ∈ uIcc e m, 0 < |dslope f e x| := by
      intro x hx
      by_cases he : x = e
      · subst x
        simpa only [dslope_same] using abs_pos.mpr (hend side).2.2
      · have hxopen : x ∈ Ioo l u := by
          cases side
          · change x ∈ uIcc l m at hx
            change x ≠ l at he
            rw [uIcc_of_le hlm.le] at hx
            exact ⟨lt_of_le_of_ne hx.1 he.symm, hx.2.trans_lt hmu⟩
          · change x ∈ uIcc u m at hx
            change x ≠ u at he
            rw [uIcc_of_ge hmu.le] at hx
            exact ⟨hlm.trans_le hx.1, lt_of_le_of_ne hx.2 he⟩
        apply abs_pos.mpr
        intro hz
        have heq : (x - e) * dslope f e x = f x := by
          simpa only [smul_eq_mul, hezero, sub_zero] using sub_smul_dslope f e x
        rw [hz, mul_zero] at heq
        exact (hpos x hxopen).ne' heq.symm
    exact isCompact_uIcc.exists_forall_le' hcontinuous.abs.continuousOn hpositive
  choose b hb hbound using hside
  let c : ℝ := min (b false) (b true)
  have hc : 0 < c := lt_min (hb false) (hb true)
  refine ⟨c, hc, ?_⟩
  intro x hx
  have hfn : 0 ≤ f x := by
    by_cases hxL : x = l
    · subst x
      exact le_of_eq (hend false).1.symm
    · by_cases hxR : x = u
      · subst x
        exact le_of_eq (hend true).1.symm
      · exact (hpos x ⟨lt_of_le_of_ne hx.1 hxL.symm,
          lt_of_le_of_ne hx.2 hxR⟩).le
  have hhalf (side : Bool)
      (hxm : x ∈ uIcc (if side then u else l) m) :
      c * min (x - l) (u - x) ≤ f x := by
    let e : ℝ := if side then u else l
    have hezero : f e = 0 := (hend side).1
    have hcb : c ≤ b side := by
      cases side
      · exact min_le_left _ _
      · exact min_le_right _ _
    have hdistance : min (x - l) (u - x) ≤ |x - e| := by
      cases side
      · simpa only [e, Bool.false_eq_true, ↓reduceIte,
          abs_of_nonneg (sub_nonneg.mpr hx.1)] using min_le_left (x - l) (u - x)
      · have he : |x - u| = u - x := by
          rw [abs_of_nonpos (sub_nonpos.mpr hx.2)]
          ring
        simpa only [e, ↓reduceIte, he] using min_le_right (x - l) (u - x)
    have hproduct : |x - e| * |dslope f e x| = f x := by
      rw [← abs_mul]
      have heq : (x - e) * dslope f e x = f x := by
        simpa only [smul_eq_mul, hezero, sub_zero] using sub_smul_dslope f e x
      rw [heq, abs_of_nonneg hfn]
    calc
      c * min (x - l) (u - x) ≤ b side * |x - e| :=
        mul_le_mul hcb hdistance
          (le_min (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)) (hb side).le
      _ ≤ |dslope f e x| * |x - e| :=
        mul_le_mul_of_nonneg_right (hbound side x hxm) (abs_nonneg _)
      _ = f x := by rw [mul_comm]; exact hproduct
  by_cases hxm : x ≤ m
  · exact hhalf false (mem_uIcc_of_le hx.1 hxm)
  · exact hhalf true (mem_uIcc_of_ge (le_of_not_ge hxm) hx.2)

/-- The genuine simple roots give a positive physical profile coefficient
on this one component. Uniform control across infinitely many components
is a separate quantitative assertion. -/
theorem n04PositiveComponent_simple_profile_min_lower
    {D : ReferenceData} (hD : RadialProfileGeometry D)
    (i : N04PositiveComponent D.a D.b (deriv D.w))
    (hroots : ∀ side : Bool, n04PositiveEndpoint i side ∈ radialCore D ∧
      deriv D.w (n04PositiveEndpoint i side) = 0 ∧
      deriv (deriv D.w) (n04PositiveEndpoint i side) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ r ∈ Icc (n04PositiveLeft i) (n04PositiveRight i),
      c * min (r - n04PositiveLeft i) (n04PositiveRight i - r) ≤ deriv D.w r / r := by
  have hsm : ContDiff ℝ ∞ (deriv D.w) :=
    (contDiff_infty_iff_deriv.mp hD.2.2.1.1).2
  have hb := n04PositiveComponent_bounds hsm.continuous i
  have hend (side : Bool) :
      deriv D.w (if side then n04PositiveRight i else n04PositiveLeft i) = 0 ∧
        DifferentiableAt ℝ (deriv D.w)
          (if side then n04PositiveRight i else n04PositiveLeft i) ∧
        deriv (deriv D.w) (if side then n04PositiveRight i else n04PositiveLeft i) ≠ 0 :=
    ⟨(hroots side).2.1, hsm.differentiable (by simp) _, (hroots side).2.2⟩
  obtain ⟨c, hc, hbound⟩ := positiveInterval_simple_root_min_lower hb.2.1 hsm.continuous
    (fun r hr => n04PositiveComponent_interval_pos hsm.continuous i hr) hend
  have hbpos : 0 < D.b := hD.1.trans hD.2.1
  refine ⟨c / D.b, div_pos hc hbpos, ?_⟩
  intro r hr
  have hrpos : 0 < r := hD.1.trans_le (hb.1.trans hr.1)
  have hrb : r ≤ D.b := hr.2.trans hb.2.2
  have hmin : 0 ≤ min (r - n04PositiveLeft i) (n04PositiveRight i - r) :=
    le_min (sub_nonneg.mpr hr.1) (sub_nonneg.mpr hr.2)
  calc
    (c / D.b) * min (r - n04PositiveLeft i) (n04PositiveRight i - r) =
        (c * min (r - n04PositiveLeft i) (n04PositiveRight i - r)) / D.b := by ring
    _ ≤ (c * min (r - n04PositiveLeft i) (n04PositiveRight i - r)) / r :=
      div_le_div_of_nonneg_left (mul_nonneg hc.le hmin) hrpos hrb
    _ ≤ deriv D.w r / r := div_le_div_of_nonneg_right (hbound r hr) hrpos.le

end ContinuousFlexibility.Analysis
