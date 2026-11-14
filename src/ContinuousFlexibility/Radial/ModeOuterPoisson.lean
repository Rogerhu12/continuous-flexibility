module

public import ContinuousFlexibility.Radial.ModeOuterRestriction
public import ContinuousFlexibility.Radial.ModeSmoothWeakEquation
public import ContinuousFlexibility.Radial.SeedPairGluing
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Exterior Poisson vectors from actual smooth natural solutions

A smooth separating function changes only in the open inner interval.
It therefore gives a global smooth lift with the exact natural solution
on the chosen outer component and zero on the other. Restricting this
lift produces the actual Hilbert vector and its piecewise representative.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def modeOuterSeparation (l h r : ℝ) : ℝ :=
  smoothTransition (3 * ((r - l) / (h - l)) - 1)

theorem contDiff_modeOuterSeparation (l h : ℝ) :
    ContDiff ℝ ∞ (modeOuterSeparation l h) :=
  smoothTransition.contDiff.comp
    ((contDiff_const.mul ((contDiff_id.sub contDiff_const).div_const (h - l))).sub
      contDiff_const)

theorem modeOuterSeparation_zero {l h r : ℝ} (hm : l < h)
    (hr : r ≤ (2 * l + h) / 3) : modeOuterSeparation l h r = 0 := by
  apply smoothTransition.zero_of_nonpos
  have hq : (r - l) / (h - l) ≤ (1 / 3 : ℝ) :=
    (div_le_iff₀ (sub_pos.mpr hm)).mpr (by linarith only [hr])
  linarith only [hq]

theorem modeOuterSeparation_one {l h r : ℝ} (hm : l < h)
    (hr : (l + 2 * h) / 3 ≤ r) : modeOuterSeparation l h r = 1 := by
  apply smoothTransition.one_of_one_le
  have hq : (2 / 3 : ℝ) ≤ (r - l) / (h - l) :=
    (le_div_iff₀ (sub_pos.mpr hm)).mpr (by linarith only [hr])
  linarith only [hq]

def modeOuterSideLift (l h : ℝ) (right : Bool) (u : ℝ → ℝ) (r : ℝ) : ℝ :=
  (if right then modeOuterSeparation l h r else 1 - modeOuterSeparation l h r) * u r

theorem contDiff_modeOuterSideLift (l h : ℝ) (right : Bool)
    {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (modeOuterSideLift l h right u) := by
  cases right
  · exact (contDiff_const.sub (contDiff_modeOuterSeparation l h)).mul hu
  · exact (contDiff_modeOuterSeparation l h).mul hu

theorem modeOuterSideLift_left_germ {l h r : ℝ} (hm : l < h)
    (hr : r ≤ l) (right : Bool) (u : ℝ → ℝ) :
    modeOuterSideLift l h right u =ᶠ[𝓝 r] fun x => if right then 0 else u x := by
  filter_upwards [Iio_mem_nhds (show r < (2 * l + h) / 3 by linarith)] with x hx
  have hz := modeOuterSeparation_zero hm hx.le
  cases right <;> simp only [modeOuterSideLift, Bool.false_eq_true, if_false, if_true,
    hz, sub_zero, one_mul, zero_mul]

theorem modeOuterSideLift_right_germ {l h r : ℝ} (hm : l < h)
    (hr : h ≤ r) (right : Bool) (u : ℝ → ℝ) :
    modeOuterSideLift l h right u =ᶠ[𝓝 r] fun x => if right then u x else 0 := by
  filter_upwards [Ioi_mem_nhds (show (l + 2 * h) / 3 < r by linarith)] with x hx
  have hz := modeOuterSeparation_one hm hx.le
  cases right <;> simp only [modeOuterSideLift, Bool.false_eq_true, if_false, if_true,
    hz, sub_self, one_mul, zero_mul]

/-- This closed-half-line representative keeps its chosen cut value. -/
def modeOuterSideFunction (l h : ℝ) (right : Bool) (u : ℝ → ℝ) : ℝ → ℝ :=
  (if right then Ici h else Iic l).indicator u

theorem modeOuterSideFunction_eq_extension {l h : ℝ} (hm : l < h)
    (right : Bool) (u : ℝ → ℝ) :
    modeOuterSideFunction l h right u =
      modeOuterExtension l h (modeOuterSideLift l h right u) := by
  classical
  funext r
  by_cases hi : r ∈ Ioo l h
  · rw [modeOuterExtension_zero_inside _ hi]
    cases right
    · exact Set.indicator_of_notMem (s := Iic l) (not_le.mpr hi.1) u
    · exact Set.indicator_of_notMem (s := Ici h) (not_le.mpr hi.2) u
  · rw [modeOuterExtension_eqOn _ hi]
    rcases le_or_gt r l with hr | hr
    · rw [(modeOuterSideLift_left_germ hm hr right u).eq_of_nhds]
      cases right
      · exact Set.indicator_of_mem (s := Iic l) hr u
      · exact Set.indicator_of_notMem (s := Ici h) (not_le.mpr (hr.trans_lt hm)) u
    · have hh : h ≤ r := le_of_not_gt (fun hh => hi ⟨hr, hh⟩)
      rw [(modeOuterSideLift_right_germ hm hh right u).eq_of_nhds]
      cases right
      · exact Set.indicator_of_notMem (s := Iic l) (not_le.mpr hr) u
      · exact Set.indicator_of_mem (s := Ici h) hh u

theorem modeOuterSideFunction_zero_inside {l h r : ℝ} (right : Bool)
    (u : ℝ → ℝ) (hr : r ∈ Ioo l h) : modeOuterSideFunction l h right u r = 0 := by
  cases right
  · exact Set.indicator_of_notMem (s := Iic l) (not_le.mpr hr.1) u
  · exact Set.indicator_of_notMem (s := Ici h) (not_le.mpr hr.2) u

theorem modeOuterSideFunction_contDiffOn {a b l h : ℝ} (hm : l < h)
    (right : Bool) {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiffOn ℝ 2 (modeOuterSideFunction l h right u) (Ioc a l ∪ Ico h b) := by
  rw [modeOuterSideFunction_eq_extension hm right u]
  exact modeOuterExtension_contDiffOn
    ((contDiff_modeOuterSideLift l h right hu).of_le (by simp)).contDiffOn

theorem modeOuterSideLift_homogeneous {D : ReferenceData} {j : ℕ} {l h : ℝ}
    (hm : l < h) (right : Bool) {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (hODE : RadialHomogeneousOn D j
      (radialTailInterval D right (if right then h else l)) u) :
    RadialHomogeneousOn D j (Ioo D.a l ∪ Ioo h D.b)
      (modeOuterSideLift l h right u) := by
  refine ⟨(contDiff_modeOuterSideLift l h right hu).contDiffOn, ?_⟩
  intro r hr
  rcases hr with hL | hR
  · have he := modeOuterSideLift_left_germ hm hL.2.le right u
    rw [radialJacobi_eq_of_germs (Filter.EventuallyEq.refl (𝓝 r) D.w) he]
    cases right
    · exact hODE.2 r hL
    · simp only [if_true, radialJacobi, deriv_const, mul_zero, sub_zero]
  · have he := modeOuterSideLift_right_germ hm hR.1.le right u
    rw [radialJacobi_eq_of_germs (Filter.EventuallyEq.refl (𝓝 r) D.w) he]
    cases right
    · simp only [Bool.false_eq_true, if_false, radialJacobi, deriv_const, mul_zero, sub_zero]
    · exact hODE.2 r hR

/-- An actual vector, obtained from a smooth lift and the exterior projection. -/
def modeOuterPoissonVector (D : ReferenceData) (hD : IsAccumulatingProfile D)
    (l h : ℝ) (right : Bool) (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) : RadialModePair D :=
  modeOuterSource D l h
    (matchingSmoothVector D hD (modeOuterSideLift l h right u)
      (contDiff_modeOuterSideLift l h right hu), 0)

theorem modeOuterPoissonVector_coe {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {l h : ℝ} (hm : l < h) (right : Bool)
    (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) :
    ((modeOuterPoissonVector D hD l h right u hu).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      modeOuterSideFunction l h right u := by
  rw [modeOuterSideFunction_eq_extension hm right u]
  apply modeOuterSource_extension_ae
  exact matchingTestInput_coe hD (modeOuterSideLift l h right u)
    (contDiff_modeOuterSideLift l h right hu) 0

theorem modeOuterPoissonVector_scalar {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (l h : ℝ) (right : Bool)
    (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) :
    (modeOuterPoissonVector D hD l h right u hu).2 = 0 := rfl

theorem modeOuterPoissonVector_zero_inside {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (l h : ℝ) (right : Bool)
    (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) :
    ((modeOuterPoissonVector D hD l h right u hu).1 : ℝ → ℝ) =ᵐ[
      (radialHilbertMeasure D).restrict (Ioo l h)] fun _ => 0 :=
  modeOuterSource_zero_inside D l h _

theorem modeOuterPoissonVector_weak {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {j : ℕ} {l h : ℝ} (hm : l < h)
    (right : Bool) {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (hODE : RadialHomogeneousOn D j
      (radialTailInterval D right (if right then h else l)) u) :
    ModeLocalEquation D j (Ioo D.a l ∪ Ioo h D.b)
      (modeOuterPoissonVector D hD l h right u hu) 0 := by
  let W := modeOuterSideLift l h right u
  have hW : ContDiff ℝ ∞ W := contDiff_modeOuterSideLift l h right hu
  let U : RadialModePair D := (matchingSmoothVector D hD W hW, 0)
  have hUW : (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] W :=
    matchingTestInput_coe hD W hW 0
  have hzero : ((0 : RadialModePair D).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      fun _ => 0 := Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D)
  have hEq : ModeLocalEquation D j (Ioo D.a l ∪ Ioo h D.b) U 0 := by
    apply modeLocalEquation_of_smooth_pointwise hD hW hUW hzero rfl
    intro r hr
    simpa only [mul_zero, neg_zero] using
      (modeOuterSideLift_homogeneous hm right hu hODE).2 r hr
  exact (modeLocalEquation_modeOuterSource_iff hD).mp
    (modeLocalEquation_modeOuterRestriction hD rfl hEq)

end ContinuousFlexibility.Radial
