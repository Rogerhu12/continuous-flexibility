module

public import ContinuousFlexibility.Radial.PositiveBufferIntervalFormBridge

/-!
# Adjoint restriction of zero-trace energy fields
Both fields may initially extend beyond the retained interval. Restriction acts
on their actual derivatives and potential weights, is self-adjoint for the
physical form, and preserves the admissible scalar border coordinate.
-/

@[expose] public section
noncomputable section
namespace ContinuousFlexibility.Radial
open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

theorem positiveBufferEnergyForm_restrict_adjoint {V : ℝ → ℝ}
    (hV : Continuous V) (hreal : ActualClosedFormRealization V) {l h : ℝ} (hlh : l < h)
    (u w : PositiveBufferEnergy V)
    (hul : positiveBufferTraceAt V l u = 0) (huh : positiveBufferTraceAt V h u = 0)
    (hwl : positiveBufferTraceAt V l w = 0) (hwh : positiveBufferTraceAt V h w = 0) :
    positiveBufferEnergyForm V hV (positiveBufferEnergyRestrict hV hreal hlh u hul huh) w =
      positiveBufferEnergyForm V hV u (positiveBufferEnergyRestrict hV hreal hlh w hwl hwh) := by
  rw [positiveBufferEnergyForm_eq_integral, positiveBufferEnergyForm_eq_integral,
    positiveBufferEnergyRestrict_base, positiveBufferEnergyRestrict_derivative,
    positiveBufferEnergyRestrict_base, positiveBufferEnergyRestrict_derivative]
  congr 1
  · exact positiveBuffer_indicator_inner (Ioo l h) measurableSet_Ioo _ _
  · apply integral_congr_ae
    filter_upwards [bufferL2Indicator_coeFn (Ioo l h) measurableSet_Ioo
      (positiveBufferEnergyCoordinate V 0 u),
      bufferL2Indicator_coeFn (Ioo l h) measurableSet_Ioo
        (positiveBufferEnergyCoordinate V 0 w)] with x hu hw
    rw [hu, hw]
    by_cases hx : x ∈ Ioo l h
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, mul_zero, zero_mul]

theorem positiveBufferEnergyRestrict_supported {V : ℝ → ℝ}
    (hV : Continuous V) (hreal : ActualClosedFormRealization V) {l h : ℝ} (hlh : l < h)
    (u : PositiveBufferEnergy V)
    (hl : positiveBufferTraceAt V l u = 0) (hh : positiveBufferTraceAt V h u = 0) :
    (positiveBufferEnergyCoordinate V 0 (positiveBufferEnergyRestrict hV hreal hlh u hl hh) :
      ℝ → ℝ) =ᵐ[volume.restrict (Ioo l h)ᶜ] (fun _ => 0) := by
  have hs := positiveBufferRetainedProjection_supported l h
    (positiveBufferEnergyCoordinate V 0 u, 0)
  simpa only [positiveBufferRetainedProjection_apply, positiveBufferEnergyRestrict_base] using hs

theorem positiveBufferEnergyRestrict_zero_trace {V : ℝ → ℝ}
    (hV : Continuous V) (hreal : ActualClosedFormRealization V) {l h : ℝ} (hlh : l < h)
    (u : PositiveBufferEnergy V)
    (hl : positiveBufferTraceAt V l u = 0) (hh : positiveBufferTraceAt V h u = 0) :
    positiveBufferTraceAt V l (positiveBufferEnergyRestrict hV hreal hlh u hl hh) = 0 ∧
      positiveBufferTraceAt V h (positiveBufferEnergyRestrict hV hreal hlh u hl hh) = 0 :=
  positiveBufferEnergy_supported_zero_trace _
    (positiveBufferEnergyRestrict_supported hV hreal hlh u hl hh)

theorem positiveBufferEnergyRestrict_eq_self {V : ℝ → ℝ}
    (hV : Continuous V) (hreal : ActualClosedFormRealization V) {l h : ℝ} (hlh : l < h)
    (u : PositiveBufferEnergy V)
    (hl : positiveBufferTraceAt V l u = 0) (hh : positiveBufferTraceAt V h u = 0)
    (hu : (positiveBufferEnergyCoordinate V 0 u : ℝ → ℝ) =ᵐ[volume.restrict (Ioo l h)ᶜ]
      (fun _ => 0)) :
    positiveBufferEnergyRestrict hV hreal hlh u hl hh = u := by
  apply positiveBufferEnergy_base_injective V
  rw [positiveBufferEnergyRestrict_base]
  exact bufferL2Indicator_eq_self_of_supported (Ioo l h) measurableSet_Ioo _ hu

/-- Restriction keeps the scalar component and the frozen admissibility condition. -/
def positiveBufferBorderedEnergyRestrict {V : ℝ → ℝ}
    (hV : Continuous V) (hreal : ActualClosedFormRealization V) {l h : ℝ} (hlh : l < h)
    {bordered : Bool} (U : PositiveBufferBorderedEnergy V bordered)
    (hl : positiveBufferTraceAt V l U.val.1 = 0)
    (hh : positiveBufferTraceAt V h U.val.1 = 0) : PositiveBufferBorderedEnergy V bordered :=
  ⟨(positiveBufferEnergyRestrict hV hreal hlh U.val.1 hl hh, U.val.2), U.property⟩

@[simp] theorem positiveBufferBorderedEnergyRestrict_field {V : ℝ → ℝ}
    (hV : Continuous V) (hreal : ActualClosedFormRealization V) {l h : ℝ} (hlh : l < h)
    {bordered : Bool} (U : PositiveBufferBorderedEnergy V bordered)
    (hl : positiveBufferTraceAt V l U.val.1 = 0)
    (hh : positiveBufferTraceAt V h U.val.1 = 0) :
    positiveBufferBorderedField V bordered (positiveBufferBorderedEnergyRestrict hV hreal hlh U hl hh) =
      positiveBufferEnergyRestrict hV hreal hlh U.val.1 hl hh := rfl

@[simp] theorem positiveBufferBorderedEnergyRestrict_scalar {V : ℝ → ℝ}
    (hV : Continuous V) (hreal : ActualClosedFormRealization V) {l h : ℝ} (hlh : l < h)
    {bordered : Bool} (U : PositiveBufferBorderedEnergy V bordered)
    (hl : positiveBufferTraceAt V l U.val.1 = 0)
    (hh : positiveBufferTraceAt V h U.val.1 = 0) :
    positiveBufferBorderedScalar V bordered (positiveBufferBorderedEnergyRestrict hV hreal hlh U hl hh) =
      positiveBufferBorderedScalar V bordered U := rfl

theorem positiveBufferBorderedEnergyRestrict_state {V : ℝ → ℝ}
    (hV : Continuous V) (hreal : ActualClosedFormRealization V) {l h : ℝ} (hlh : l < h)
    {bordered : Bool} (U : PositiveBufferBorderedEnergy V bordered)
    (hl : positiveBufferTraceAt V l U.val.1 = 0)
    (hh : positiveBufferTraceAt V h U.val.1 = 0) :
    positiveBufferBorderedState V bordered (positiveBufferBorderedEnergyRestrict hV hreal hlh U hl hh) =
      positiveBufferRetainedProjection l h (positiveBufferBorderedState V bordered U) := by
  rw [positiveBufferBorderedState_apply, positiveBufferRetainedProjection_apply,
    positiveBufferBorderedState_apply]
  change (positiveBufferEnergyCoordinate V 0
      (positiveBufferEnergyRestrict hV hreal hlh U.val.1 hl hh), U.val.2) =
    (bufferL2Indicator (Ioo l h) measurableSet_Ioo
      (positiveBufferEnergyCoordinate V 0 U.val.1), U.val.2)
  rw [positiveBufferEnergyRestrict_base]

theorem positiveBufferBorderedEnergyRestrict_supported {V : ℝ → ℝ}
    (hV : Continuous V) (hreal : ActualClosedFormRealization V) {l h : ℝ} (hlh : l < h)
    {bordered : Bool} (U : PositiveBufferBorderedEnergy V bordered)
    (hl : positiveBufferTraceAt V l U.val.1 = 0)
    (hh : positiveBufferTraceAt V h U.val.1 = 0) :
    (positiveBufferEnergyCoordinate V 0
      (positiveBufferBorderedEnergyRestrict hV hreal hlh U hl hh).val.1 :
        ℝ → ℝ) =ᵐ[volume.restrict (Ioo l h)ᶜ] (fun _ => 0) :=
  positiveBufferEnergyRestrict_supported hV hreal hlh U.val.1 hl hh

theorem positiveBufferBorderedEnergyRestrict_zero_trace {V : ℝ → ℝ}
    (hV : Continuous V) (hreal : ActualClosedFormRealization V) {l h : ℝ} (hlh : l < h)
    {bordered : Bool} (U : PositiveBufferBorderedEnergy V bordered)
    (hl : positiveBufferTraceAt V l U.val.1 = 0)
    (hh : positiveBufferTraceAt V h U.val.1 = 0) :
    positiveBufferTraceAt V l (positiveBufferBorderedEnergyRestrict hV hreal hlh U hl hh).val.1 = 0 ∧
      positiveBufferTraceAt V h (positiveBufferBorderedEnergyRestrict hV hreal hlh U hl hh).val.1 = 0 :=
  positiveBufferEnergyRestrict_zero_trace hV hreal hlh U.val.1 hl hh

/-- Self-adjointness for the full bordered form, with both original fields
having zero endpoint traces and the actual border supported in the interval. -/
theorem positiveBufferBorderedForm_restrict_adjoint {V : ℝ → ℝ}
    (hV : Continuous V) (hreal : ActualClosedFormRealization V) {l h : ℝ} (hlh : l < h)
    (g : RadialL2) (bordered : Bool)
    (hg : (g : ℝ → ℝ) =ᵐ[volume.restrict (Ioo l h)ᶜ] (fun _ => 0))
    (U W : PositiveBufferBorderedEnergy V bordered)
    (hul : positiveBufferTraceAt V l U.val.1 = 0) (huh : positiveBufferTraceAt V h U.val.1 = 0)
    (hwl : positiveBufferTraceAt V l W.val.1 = 0) (hwh : positiveBufferTraceAt V h W.val.1 = 0) :
    positiveBufferBorderedForm V hV g bordered
      (positiveBufferBorderedEnergyRestrict hV hreal hlh U hul huh) W =
    positiveBufferBorderedForm V hV g bordered U
      (positiveBufferBorderedEnergyRestrict hV hreal hlh W hwl hwh) := by
  have hborder (v : RadialL2) :
      inner (𝕜 := ℝ) g (bufferL2Indicator (Ioo l h) measurableSet_Ioo v) =
        inner (𝕜 := ℝ) g v := by
    rw [← positiveBuffer_indicator_inner,
      bufferL2Indicator_eq_self_of_supported (Ioo l h) measurableSet_Ioo g hg]
  change
    positiveBufferEnergyForm V hV (positiveBufferEnergyRestrict hV hreal hlh U.val.1 hul huh) W.val.1 +
      U.val.2 * inner (𝕜 := ℝ) g (positiveBufferEnergyCoordinate V 0 W.val.1) +
      W.val.2 * inner (𝕜 := ℝ) g
        (positiveBufferEnergyCoordinate V 0 (positiveBufferEnergyRestrict hV hreal hlh U.val.1 hul huh)) =
    positiveBufferEnergyForm V hV U.val.1 (positiveBufferEnergyRestrict hV hreal hlh W.val.1 hwl hwh) +
      U.val.2 * inner (𝕜 := ℝ) g
        (positiveBufferEnergyCoordinate V 0 (positiveBufferEnergyRestrict hV hreal hlh W.val.1 hwl hwh)) +
      W.val.2 * inner (𝕜 := ℝ) g (positiveBufferEnergyCoordinate V 0 U.val.1)
  rw [positiveBufferEnergyForm_restrict_adjoint hV hreal hlh U.val.1 W.val.1 hul huh hwl hwh,
    positiveBufferEnergyRestrict_base, positiveBufferEnergyRestrict_base, hborder, hborder]

theorem positiveBufferBorderedEnergyRestrict_state_norm_le {V : ℝ → ℝ}
    (hV : Continuous V) (hreal : ActualClosedFormRealization V) {l h : ℝ} (hlh : l < h)
    {bordered : Bool} (U : PositiveBufferBorderedEnergy V bordered)
    (hl : positiveBufferTraceAt V l U.val.1 = 0)
    (hh : positiveBufferTraceAt V h U.val.1 = 0) :
    ‖positiveBufferBorderedState V bordered
      (positiveBufferBorderedEnergyRestrict hV hreal hlh U hl hh)‖ ≤
        ‖positiveBufferBorderedState V bordered U‖ := by
  rw [positiveBufferBorderedEnergyRestrict_state]
  exact positiveBufferRetainedProjection_norm_le l h _

end ContinuousFlexibility.Radial
