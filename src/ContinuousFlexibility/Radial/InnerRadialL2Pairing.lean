module

public import ContinuousFlexibility.Radial.InnerRadialL2Mass
public import ContinuousFlexibility.Statements.RadialTargets

/-!
# Physical L² pairings of interval fields

These identities use the existing radial measure and arbitrary L²
representatives. The two-field version gives the exact interval pairing
needed for the physical closed-energy form.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped InnerProductSpace

theorem innerRadialIntervalToLp_inner_right (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r) (v : ℝ → ℝ) (hv : ContinuousOn v (Icc a b))
    (F : RadialModeL2 D) :
    ⟪F, innerRadialIntervalToLp D hw ha hcore hpos v hv⟫_ℝ =
      ∫ r in Ioo a b, (12 * D.w r / r ^ 2) * F r * v r := by
  rw [L2.inner_def]
  calc
    _ = ∫ r, (Ioo a b).indicator (fun r => F r * v r) r ∂radialHilbertMeasure D := by
      apply integral_congr_ae
      filter_upwards [innerRadialIntervalToLp_ae D hw ha hcore hpos v hv] with r hr
      rw [hr]
      by_cases hmem : r ∈ Ioo a b
      · simp only [indicator_of_mem hmem, RCLike.inner_apply, conj_trivial] <;> ring
      · simp only [indicator_of_notMem hmem, inner_zero_right]
    _ = ∫ r in Ioo a b, F r * v r ∂radialHilbertMeasure D :=
      integral_indicator measurableSet_Ioo
    _ = _ := by
      rw [innerRadialInterval_integral D hw hcore hpos]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r _
      dsimp only
      ring

theorem innerRadialIntervalToLp_inner (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r)
    (u v : ℝ → ℝ) (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b)) :
    ⟪innerRadialIntervalToLp D hw ha hcore hpos u hu,
      innerRadialIntervalToLp D hw ha hcore hpos v hv⟫_ℝ =
      ∫ r in a..b, (12 * D.w r / r ^ 2) * u r * v r := by
  rw [L2.inner_def]
  calc
    _ = ∫ r, (Ioo a b).indicator (fun r => u r * v r) r ∂radialHilbertMeasure D := by
      apply integral_congr_ae
      filter_upwards [innerRadialIntervalToLp_ae D hw ha hcore hpos u hu,
        innerRadialIntervalToLp_ae D hw ha hcore hpos v hv] with r hur hvr
      rw [hur, hvr]
      by_cases hmem : r ∈ Ioo a b
      · simp only [indicator_of_mem hmem, RCLike.inner_apply, conj_trivial] <;> ring
      · simp only [indicator_of_notMem hmem, inner_zero_left]
    _ = ∫ r in Ioo a b, u r * v r ∂radialHilbertMeasure D :=
      integral_indicator measurableSet_Ioo
    _ = ∫ r in Ioo a b, (12 * D.w r / r ^ 2) * u r * v r := by
      rw [innerRadialInterval_integral D hw hcore hpos]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r _
      dsimp only
      ring
    _ = _ := by
      rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

end ContinuousFlexibility.Radial
