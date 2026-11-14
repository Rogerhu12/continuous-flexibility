module

public import ContinuousFlexibility.Radial.InnerWeightL2
public import ContinuousFlexibility.Radial.InnerRadialFiniteWeakGraph

/-!
# The actual signed radial potential on a finite piece

The multiplier is constructed from (j²/12)*(r*w'/w) in the same physical
measure. Its finite bound follows from compactness and positivity of
w on the retained closed interval. No sign of w' and no uniform final
inverse estimate is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

def innerRadialPotentialCoefficient (D : ReferenceData) (j a b : ℝ) : ℝ → ℝ :=
  (Ioo a b).indicator (fun r => (j ^ 2 / 12) * (r * deriv D.w r / D.w r))

theorem innerRadialPotentialCoefficient_measurable (D : ReferenceData)
    (hw : ContDiff ℝ ∞ D.w) (j a b : ℝ) :
    Measurable (innerRadialPotentialCoefficient D j a b) :=
  (measurable_const.mul
    ((measurable_id.mul (contDiff_infty_iff_deriv.mp hw).2.continuous.measurable).div
      hw.continuous.measurable)).indicator measurableSet_Ioo

theorem exists_innerRadialPotentialCoefficient_bound (D : ReferenceData)
    (hw : ContDiff ℝ ∞ D.w) (j : ℝ) {a b : ℝ}
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, |innerRadialPotentialCoefficient D j a b r| ≤ C := by
  have hc : ContinuousOn (fun r => (j ^ 2 / 12) * (r * deriv D.w r / D.w r))
      (Icc a b) :=
    continuousOn_const.mul
      ((continuous_id.continuousOn.mul
        (contDiff_infty_iff_deriv.mp hw).2.continuous.continuousOn).div
          hw.continuous.continuousOn (fun r hr => (hpos r hr).ne'))
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hc
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro r
  unfold innerRadialPotentialCoefficient
  by_cases hr : r ∈ Ioo a b
  · rw [indicator_of_mem hr]
    simpa only [Real.norm_eq_abs] using
      (hC r (Ioo_subset_Icc_self hr)).trans (le_max_right 0 C)
  · rw [indicator_of_notMem hr, abs_zero]
    exact le_max_left _ _

def innerRadialPotentialMultiplier (D : ReferenceData)
    (hw : ContDiff ℝ ∞ D.w) (j : ℝ) {a b : ℝ}
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r) :
    RadialModeL2 D →L[ℝ] RadialModeL2 D :=
  innerWeightMultiplier (radialHilbertMeasure D) (innerRadialPotentialCoefficient D j a b)
    (innerRadialPotentialCoefficient_measurable D hw j a b)
    (Classical.choose (exists_innerRadialPotentialCoefficient_bound D hw j hpos))
    (Classical.choose_spec (exists_innerRadialPotentialCoefficient_bound D hw j hpos)).2

theorem innerRadialPotentialMultiplier_ae (D : ReferenceData)
    (hw : ContDiff ℝ ∞ D.w) (j : ℝ) {a b : ℝ}
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (u : RadialModeL2 D) :
    (innerRadialPotentialMultiplier D hw j hpos u : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (fun r => innerRadialPotentialCoefficient D j a b r * u r) :=
  innerWeightMultiplier_ae _ _ _ _ _ u

theorem innerRadialPotentialMultiplier_adjoint (D : ReferenceData)
    (hw : ContDiff ℝ ∞ D.w) (j : ℝ) {a b : ℝ}
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r) :
    (innerRadialPotentialMultiplier D hw j hpos).adjoint =
      innerRadialPotentialMultiplier D hw j hpos :=
  innerWeightMultiplier_adjoint _ _ _ _ _

theorem innerRadialPotentialMultiplier_class (D : ReferenceData)
    (hw : ContDiff ℝ ∞ D.w) (j : ℝ) {a b : ℝ}
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (u : RadialModeL2 D) :
    InnerRadialPotentialClass D j a b u (innerRadialPotentialMultiplier D hw j hpos u) := by
  unfold InnerRadialPotentialClass
  filter_upwards [innerRadialPotentialMultiplier_ae D hw j hpos u] with r hr
  rw [hr, innerRadialPotentialCoefficient]
  by_cases hmem : r ∈ Ioo a b
  · rw [indicator_of_mem hmem, indicator_of_mem hmem]
  · rw [indicator_of_notMem hmem, indicator_of_notMem hmem, zero_mul]

theorem innerRadialPotentialClass_iff_multiplier (D : ReferenceData)
    (hw : ContDiff ℝ ∞ D.w) (j : ℝ) {a b : ℝ}
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (u v : RadialModeL2 D) :
    InnerRadialPotentialClass D j a b u v ↔
      v = innerRadialPotentialMultiplier D hw j hpos u := by
  constructor
  · intro h
    apply Lp.ext
    exact h.trans (innerRadialPotentialMultiplier_class D hw j hpos u).symm
  · rintro rfl
    exact innerRadialPotentialMultiplier_class D hw j hpos u

end ContinuousFlexibility.Radial
