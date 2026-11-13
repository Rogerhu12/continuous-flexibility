import ContinuousFlexibility.Analysis.N04PositiveQuantitativeNormalizationBuffer
import ContinuousFlexibility.Analysis.RetainedPositiveComponentMaterialWidth
import ContinuousFlexibility.Analysis.N04RealizationLeadAssembly

/-!
# A normalization buffer with material costs on every gap

The normalization support is compact inside the positive region. The existing
quantitative buffer construction therefore gives one positive fraction of
each component width for every consecutive gap. The retained positive-width
estimate turns those margins into one power of the actual midpoint sample.

The buffer and its constant are selected before the state, parameter order,
or output spatial order. They are constructed from the retained start; no
estimate for a future transport is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial

/-- A positive proportional margin transfers a reciprocal-width bound
to the reciprocal gap, without losing its uniformity in the component. -/
theorem n04PositiveGeometry_inverse_gap_le_of_margin
    {c span gap M : ℝ} (hc : 0 < c) (hspan : 0 < span)
    (hgap : c * span ≤ gap) (hwidth : span⁻¹ ≤ M) :
    gap⁻¹ ≤ c⁻¹ * M := by
  calc
    gap⁻¹ ≤ (c * span)⁻¹ := inv_anti₀ (mul_pos hc hspan) hgap
    _ = c⁻¹ * span⁻¹ := by rw [mul_inv_rev, mul_comm]
    _ ≤ c⁻¹ * M := mul_le_mul_of_nonneg_left hwidth (inv_nonneg.mpr hc.le)

/-- One legal normalization buffer has material bounds on all five
consecutive inverse gaps. Its midpoint cells and enlarged material data
are exactly those already attached to the retained realization choice. -/
theorem n04PositiveGeometry_exists_controlled_buffer
    (W : N04RealizationStart) (X : N04RealizationChoice W) :
    ∃ B : N04PositiveNormalizationBuffer
        W.D.a W.D.b (deriv W.D.w) (tsupport W.D.chi),
      ∃ C : ℝ, 0 < C ∧
        ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w),
          (B.centerLeft i - n04PositiveLeft i)⁻¹ ≤
            C * W.U.E0 (W.U.sample (X.cell i)) ^ C ∧
          (B.normalizationLeft i - B.centerLeft i)⁻¹ ≤
            C * W.U.E0 (W.U.sample (X.cell i)) ^ C ∧
          (B.normalizationRight i - B.normalizationLeft i)⁻¹ ≤
            C * W.U.E0 (W.U.sample (X.cell i)) ^ C ∧
          (B.centerRight i - B.normalizationRight i)⁻¹ ≤
            C * W.U.E0 (W.U.sample (X.cell i)) ^ C ∧
          (n04PositiveRight i - B.centerRight i)⁻¹ ≤
            C * W.U.E0 (W.U.sample (X.cell i)) ^ C := by
  have hprofile := n04b_profileGeometry_of_through03 W.through03
  have hf : Continuous (deriv W.D.w) :=
    hprofile.2.2.1.1.continuous_deriv (by simp)
  have hborder : RadialTrueBorder W.D := W.radial.2.2.2.1
  have hbuffer := n04PositiveNormalizationBuffer_exists_uniform_margins
    hprofile.2.1 hf hborder.2.1 hborder.2.2.1
  let B := hbuffer.choose
  let c : ℝ := hbuffer.choose_spec.choose
  have hc : 0 < c := hbuffer.choose_spec.choose_spec.1
  have hmargins := hbuffer.choose_spec.choose_spec.2
  have hwidth := retainedReference_positive_component_material_width
    W.P W.metadata.selected W.metadata.first_two one_pos W.realizes W.hw W.coordinates
    W.through03.1.1.2.2.2.1 W.hT
  let C₀ : ℝ := hwidth.choose
  let A : ℝ := hwidth.choose_spec.choose
  have hC₀ : 0 < C₀ := hwidth.choose_spec.choose_spec.1
  have hA : 0 ≤ A := hwidth.choose_spec.choose_spec.2.1
  have hspans := hwidth.choose_spec.choose_spec.2.2
  have hpacked := coefficientEnvelope_pack (c⁻¹ * C₀) A
  let C : ℝ := hpacked.choose
  have hC : 0 < C := hpacked.choose_spec.1
  have hcost (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) :
      c⁻¹ * (C₀ * W.T.E0 (W.T.sample (X.cell i)) ^ A) ≤
        C * W.U.E0 (W.U.sample (X.cell i)) ^ C := by
    have hE : 0 ≤ W.T.E0 (W.T.sample (X.cell i)) :=
      zero_le_one.trans (W.floor _)
    have hEU : W.T.E0 (W.T.sample (X.cell i)) ≤
        W.U.E0 (W.U.sample (X.cell i)) := le_enlargedMaterialData_E0 W.T _
    have hfloor : 1 ≤ W.U.E0 (W.U.sample (X.cell i)) :=
      (W.floor _).trans hEU
    calc
      _ = (c⁻¹ * C₀) * W.T.E0 (W.T.sample (X.cell i)) ^ A := by ring
      _ ≤ (c⁻¹ * C₀) * W.U.E0 (W.U.sample (X.cell i)) ^ A :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hE hEU hA)
          (mul_nonneg (inv_nonneg.mpr hc.le) hC₀.le)
      _ ≤ C * W.U.E0 (W.U.sample (X.cell i)) ^ C :=
        hpacked.choose_spec.2 _ hfloor
  refine ⟨B, C, hC, ?_⟩
  intro i
  have hspan : 0 < n04PositiveRight i - n04PositiveLeft i :=
    sub_pos.mpr (n04PositiveComponent_bounds hf i).2.1
  have hinv (gap : ℝ)
      (hgap : c * (n04PositiveRight i - n04PositiveLeft i) ≤ gap) :
      gap⁻¹ ≤ C * W.U.E0 (W.U.sample (X.cell i)) ^ C :=
    (n04PositiveGeometry_inverse_gap_le_of_margin hc hspan hgap
      (hspans i (X.cell i) (X.cell_mem i)).1).trans (hcost i)
  have hm := hmargins i
  exact ⟨hinv _ hm.1, hinv _ hm.2.1, hinv _ hm.2.2.1,
    hinv _ hm.2.2.2.1, hinv _ hm.2.2.2.2⟩

end ContinuousFlexibility.Analysis
