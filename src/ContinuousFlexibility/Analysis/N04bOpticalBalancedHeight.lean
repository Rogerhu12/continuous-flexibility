module

public import ContinuousFlexibility.Analysis.N04bOpticalBalancedTests
public import ContinuousFlexibility.Analysis.N04bOpticalHeightVariation

/-!
# Balanced actual radial height increments

The weight in the actual height variation is continuous up to the radial
roots, smooth and positive in a negative component, and zero at the roots.
Consequently every interior cut has a compact radial increment whose total
first-order optical pairing vanishes while its left pairing is one.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology

/-- The optical height weight is continuous through the component roots. -/
theorem n04b_opticalHeightWeight_continuousOn {w : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hw : ContDiff ℝ ∞ w) (hpos : ∀ r ∈ Icc a b, 0 < w r) :
    ContinuousOn (n04bOpticalHeightWeight w) (Icc a b) := by
  have hd := (contDiff_infty_iff_deriv.mp hw).2
  have hQ : ContinuousOn (fun r => -deriv w r / (r * w r)) (Icc a b) :=
    hd.continuous.neg.continuousOn.div (continuous_id.mul hw.continuous).continuousOn
      (fun r hr => (mul_pos (ha.trans_le hr.1) (hpos r hr)).ne')
  exact ((Real.continuous_sqrt.comp_continuousOn hQ).mul
    (continuousOn_const.add (hw.continuous.continuousOn.pow 2))).div
      hw.continuous.continuousOn (fun r hr => (hpos r hr).ne')

/-- The weight is smooth in the open negative component. -/
theorem n04b_opticalHeightWeight_contDiffOn {w : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Ioo a b, 0 < w r) (hneg : ∀ r ∈ Ioo a b, deriv w r < 0) :
    ContDiffOn ℝ ∞ (n04bOpticalHeightWeight w) (Ioo a b) := by
  have hd := (contDiff_infty_iff_deriv.mp hw).2
  have hQ : ContDiffOn ℝ ∞ (fun r => -deriv w r / (r * w r)) (Ioo a b) :=
    hd.neg.contDiffOn.div (contDiff_id.mul hw).contDiffOn
      (fun r hr => (mul_pos (ha.trans hr.1) (hpos r hr)).ne')
  have hQpos (r : ℝ) (hr : r ∈ Ioo a b) : 0 < -deriv w r / (r * w r) :=
    div_pos (neg_pos.mpr (hneg r hr)) (mul_pos (ha.trans hr.1) (hpos r hr))
  exact ((hQ.sqrt (fun r hr => (hQpos r hr).ne')).mul
    (contDiffOn_const.add (hw.contDiffOn.pow 2))).div hw.contDiffOn
      (fun r hr => (hpos r hr).ne')

/-- A zero of the actual profile derivative is a zero of the height weight. -/
theorem n04b_opticalHeightWeight_eq_zero {w : ℝ → ℝ} {r : ℝ}
    (hroot : deriv w r = 0) : n04bOpticalHeightWeight w r = 0 := by
  simp [n04bOpticalHeightWeight, opticalSpeed, hroot]

/-- The weight is strictly positive on a negative component. -/
theorem n04b_opticalHeightWeight_pos {w : ℝ → ℝ} {r : ℝ}
    (hr : 0 < r) (hwp : 0 < w r) (hwn : deriv w r < 0) :
    0 < n04bOpticalHeightWeight w r := by
  have hQ : 0 < -deriv w r / (r * w r) :=
    div_pos (neg_pos.mpr hwn) (mul_pos hr hwp)
  exact div_pos (mul_pos (Real.sqrt_pos.mpr hQ) (by positivity)) hwp

/-- Every fixed interior cut has a compact radial increment that leaves
the total first-order optical pairing zero but changes the left pairing. -/
theorem n04b_exists_balanced_opticalHeight_increment {w : ℝ → ℝ} {a b c : ℝ}
    (ha : 0 < a) (hc : c ∈ Ioo a b) (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Icc a b, 0 < w r) (hneg : ∀ r ∈ Ioo a b, deriv w r < 0)
    (hrootA : deriv w a = 0) (hrootB : deriv w b = 0) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Ioo a b ∧
      (∫ r in a..b, n04bOpticalHeightWeight w r * deriv f r) = 0 ∧
      (∫ r in a..c, n04bOpticalHeightWeight w r * deriv f r) = 1 := by
  exact n04b_exists_balanced_compact_deriv_test hc
    (n04b_opticalHeightWeight_continuousOn ha hw hpos)
    (n04b_opticalHeightWeight_eq_zero hrootA)
    (n04b_opticalHeightWeight_eq_zero hrootB)
    (n04b_opticalHeightWeight_pos (ha.trans hc.1)
      (hpos c (Ioo_subset_Icc_self hc)) (hneg c hc)).ne'

/-- The balanced test is an actual height increment, and its displayed
pairings use the weight furnished by its genuine pointwise speed derivative.
This does not assert an interchange of parameter differentiation and travel
integration. -/
theorem n04b_exists_balanced_actual_height_variation {h w : ℝ → ℝ} {a b c : ℝ}
    (ha : 0 < a) (hc : c ∈ Ioo a b)
    (hh : ContDiff ℝ ∞ h) (hhw : ∀ r, HasDerivAt h (w r) r)
    (hw : ContDiff ℝ ∞ w) (hpos : ∀ r ∈ Icc a b, 0 < w r)
    (hneg : ∀ r ∈ Ioo a b, deriv w r < 0)
    (hrootA : deriv w a = 0) (hrootB : deriv w b = 0) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Ioo a b ∧
      (∫ r in a..b, n04bOpticalHeightWeight w r * deriv f r) = 0 ∧
      (∫ r in a..c, n04bOpticalHeightWeight w r * deriv f r) = 1 ∧
      ∀ r ∈ Icc a b, ∀ θ : ℝ, HasDerivAt (fun q => characteristicSpeed w
        (heightFamily (radialHeightField h) (radialHeightField f) q) (r, θ))
        (-n04bOpticalHeightWeight w r * deriv f r) 0 := by
  obtain ⟨f, hf, hfc, hfs, htotal, hhalf⟩ :=
    n04b_exists_balanced_opticalHeight_increment ha hc hw hpos hneg hrootA hrootB
  refine ⟨f, hf, hfc, hfs, htotal, hhalf, ?_⟩
  intro r hr θ
  exact n04b_hasDerivAt_characteristicSpeed_radial_increment hh hhw hf
    (ha.trans_le hr.1) (hpos r hr)

end ContinuousFlexibility.Statements
