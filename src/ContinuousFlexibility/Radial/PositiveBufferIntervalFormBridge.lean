import ContinuousFlexibility.Radial.PositiveBufferIntervalProjection
import ContinuousFlexibility.Radial.BufferIntervalRestriction

/-!
# The frozen interval graph and all zero-trace energy tests

Restriction acts on all three actual energy coordinates. A supported
solution and its derivative pair identically with the original and
restricted tests. The resulting equivalence preserves the scalar border
and arbitrary outside values of the interval source.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

@[simp] theorem positiveBufferEnergyOfLift_derivative {V : ℝ → ℝ}
    (u d q : RadialL2) (h : (u, d, q) ∈ SchrodingerEnergyLift V) :
    positiveBufferEnergyCoordinate V 1 (positiveBufferEnergyOfLift u d q h) = d := rfl

theorem positiveBuffer_indicator_inner (s : Set ℝ) (hs : MeasurableSet s)
    (u v : RadialL2) :
    ⟪bufferL2Indicator s hs u, v⟫_ℝ = ⟪u, bufferL2Indicator s hs v⟫_ℝ := by
  rw [positiveBufferL2_inner_integral, positiveBufferL2_inner_integral]
  apply integral_congr_ae
  filter_upwards [bufferL2Indicator_coeFn s hs u, bufferL2Indicator_coeFn s hs v]
    with x hu hv
  rw [hu, hv]
  by_cases hx : x ∈ s
  · simp only [indicator_of_mem hx]
  · simp only [indicator_of_notMem hx, zero_mul, mul_zero]

theorem positiveBuffer_indicator_inner_supported (s : Set ℝ) (hs : MeasurableSet s)
    (f u : RadialL2) (hu : (u : ℝ → ℝ) =ᵐ[volume.restrict sᶜ] (fun _ => 0)) :
    ⟪bufferL2Indicator s hs f, u⟫_ℝ = ⟪f, u⟫_ℝ := by
  rw [positiveBuffer_indicator_inner, bufferL2Indicator_eq_self_of_supported s hs u hu]

theorem positiveBufferEnergy_supported_zero_trace {V : ℝ → ℝ} {l h : ℝ}
    (u : PositiveBufferEnergy V)
    (hu : (positiveBufferEnergyCoordinate V 0 u : ℝ → ℝ) =ᵐ[volume.restrict (Ioo l h)ᶜ]
      (fun _ => 0)) :
    positiveBufferTraceAt V l u = 0 ∧ positiveBufferTraceAt V h u = 0 := by
  have hrep := positiveBufferEnergyRepresentative_spec V u
  simpa only [positiveBufferTraceAt_apply] using
    buffer_supported_interval_zero_traces hrep.1 hrep.2.1 hu

/-- The actual public core closure certifies the restricted weak derivative. -/
def positiveBufferEnergyRestrict {V : ℝ → ℝ} (hV : Continuous V)
    (hreal : ActualClosedFormRealization V) {l h : ℝ} (hlh : l < h)
    (u : PositiveBufferEnergy V)
    (hl : positiveBufferTraceAt V l u = 0) (hh : positiveBufferTraceAt V h u = 0) :
    PositiveBufferEnergy V :=
  positiveBufferEnergyOfLift
    (bufferL2Indicator (Ioo l h) measurableSet_Ioo (positiveBufferEnergyCoordinate V 0 u))
    (bufferL2Indicator (Ioo l h) measurableSet_Ioo (positiveBufferEnergyCoordinate V 1 u))
    (bufferL2Indicator (Ioo l h) measurableSet_Ioo (positiveBufferEnergyCoordinate V 2 u))
    (intervalEnergyClosure_subset_energy V l h hreal
      (positiveBufferEnergy_restrict_zero_trace_mem_closure hV hlh u hl hh))

@[simp] theorem positiveBufferEnergyRestrict_base {V : ℝ → ℝ} (hV : Continuous V)
    (hreal : ActualClosedFormRealization V) {l h : ℝ} (hlh : l < h)
    (u : PositiveBufferEnergy V)
    (hl : positiveBufferTraceAt V l u = 0) (hh : positiveBufferTraceAt V h u = 0) :
    positiveBufferEnergyCoordinate V 0 (positiveBufferEnergyRestrict hV hreal hlh u hl hh) =
      bufferL2Indicator (Ioo l h) measurableSet_Ioo (positiveBufferEnergyCoordinate V 0 u) := rfl

@[simp] theorem positiveBufferEnergyRestrict_derivative {V : ℝ → ℝ} (hV : Continuous V)
    (hreal : ActualClosedFormRealization V) {l h : ℝ} (hlh : l < h)
    (u : PositiveBufferEnergy V)
    (hl : positiveBufferTraceAt V l u = 0) (hh : positiveBufferTraceAt V h u = 0) :
    positiveBufferEnergyCoordinate V 1 (positiveBufferEnergyRestrict hV hreal hlh u hl hh) =
      bufferL2Indicator (Ioo l h) measurableSet_Ioo (positiveBufferEnergyCoordinate V 1 u) := rfl

@[simp] theorem positiveBufferEnergyRestrict_weight {V : ℝ → ℝ} (hV : Continuous V)
    (hreal : ActualClosedFormRealization V) {l h : ℝ} (hlh : l < h)
    (u : PositiveBufferEnergy V)
    (hl : positiveBufferTraceAt V l u = 0) (hh : positiveBufferTraceAt V h u = 0) :
    positiveBufferEnergyCoordinate V 2 (positiveBufferEnergyRestrict hV hreal hlh u hl hh) =
      bufferL2Indicator (Ioo l h) measurableSet_Ioo (positiveBufferEnergyCoordinate V 2 u) := rfl

theorem positiveBufferEnergyForm_restrict_right {V : ℝ → ℝ} (hV : Continuous V)
    (hreal : ActualClosedFormRealization V) {l h : ℝ} (hlh : l < h)
    (u w : PositiveBufferEnergy V)
    (hu : (positiveBufferEnergyCoordinate V 0 u : ℝ → ℝ) =ᵐ[volume.restrict (Ioo l h)ᶜ]
      (fun _ => 0))
    (hl : positiveBufferTraceAt V l w = 0) (hh : positiveBufferTraceAt V h w = 0) :
    positiveBufferEnergyForm V hV u (positiveBufferEnergyRestrict hV hreal hlh w hl hh) =
      positiveBufferEnergyForm V hV u w := by
  have hdu := buffer_supported_interval_derivative (positiveBufferEnergy_derivative_weak V u) hu
  have hu' := (ae_restrict_iff' measurableSet_Ioo.compl).mp hu
  rw [positiveBufferEnergyForm_eq_integral, positiveBufferEnergyForm_eq_integral,
    positiveBufferEnergyRestrict_base, positiveBufferEnergyRestrict_derivative]
  congr 1
  · rw [← positiveBuffer_indicator_inner,
      bufferL2Indicator_eq_self_of_supported (Ioo l h) measurableSet_Ioo
        (positiveBufferEnergyCoordinate V 1 u) hdu]
  · apply integral_congr_ae
    filter_upwards [bufferL2Indicator_coeFn (Ioo l h) measurableSet_Ioo
      (positiveBufferEnergyCoordinate V 0 w), hu'] with x hw hux
    rw [hw]
    by_cases hx : x ∈ Ioo l h
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hux hx]
      simp only [mul_zero, zero_mul]

/-- The frozen Dirichlet graph equals the physical form equation on all
global energy tests having zero endpoint traces. -/
theorem positiveBuffer_intervalGraph_iff_zero_trace_form {V : ℝ → ℝ}
    (hV : Continuous V) (hreal : ActualClosedFormRealization V) {l h : ℝ} (hlh : l < h)
    (u : PositiveBufferEnergy V) (f : RadialL2)
    (hu : (positiveBufferEnergyCoordinate V 0 u : ℝ → ℝ) =ᵐ[volume.restrict (Ioo l h)ᶜ]
      (fun _ => 0)) :
    IntervalFormGraph V l h (positiveBufferEnergyCoordinate V 0 u) f ↔
      ∀ w : PositiveBufferEnergy V, positiveBufferTraceAt V l w = 0 →
        positiveBufferTraceAt V h w = 0 →
        positiveBufferEnergyForm V hV u w =
          ⟪bufferL2Indicator (Ioo l h) measurableSet_Ioo f, positiveBufferEnergyCoordinate V 0 w⟫_ℝ := by
  constructor
  · rintro ⟨d, q, hdom, hform⟩ w hl hh
    have hd : d = positiveBufferEnergyCoordinate V 1 u :=
      weakRadialDerivative_unique (intervalEnergyClosure_subset_energy V l h hreal hdom).1
        (positiveBufferEnergy_derivative_weak V u)
    let r := positiveBufferEnergyRestrict hV hreal hlh w hl hh
    have hr := positiveBufferEnergy_restrict_zero_trace_mem_closure hV hlh w hl hh
    have ht := hform _ hr
    calc
      _ = positiveBufferEnergyForm V hV u r :=
        (positiveBufferEnergyForm_restrict_right hV hreal hlh u w hu hl hh).symm
      _ = ⟪f, bufferL2Indicator (Ioo l h) measurableSet_Ioo
          (positiveBufferEnergyCoordinate V 0 w)⟫_ℝ := by
        rw [positiveBufferEnergyForm_eq_integral]
        simpa only [r, positiveBufferEnergyRestrict_base, positiveBufferEnergyRestrict_derivative, hd]
          using ht.symm
      _ = _ := (positiveBuffer_indicator_inner (Ioo l h) measurableSet_Ioo f _).symm
  · intro hform
    refine ⟨positiveBufferEnergyCoordinate V 1 u, positiveBufferEnergyCoordinate V 2 u,
      intervalEnergyClosure_of_supported hV hlh u.property hu, ?_⟩
    intro p hp
    let e := positiveBufferEnergyOfLift p.1 p.2.1 p.2.2
      (intervalEnergyClosure_subset_energy V l h hreal hp)
    have hes : (positiveBufferEnergyCoordinate V 0 e : ℝ → ℝ) =ᵐ[volume.restrict (Ioo l h)ᶜ]
        (fun _ => 0) := intervalEnergyClosure_supported V l h hp
    have hetrace := positiveBufferEnergy_supported_zero_trace e hes
    have ht := hform e hetrace.1 hetrace.2
    rw [positiveBuffer_indicator_inner_supported (Ioo l h) measurableSet_Ioo f _ hes,
      positiveBufferEnergyForm_eq_integral] at ht
    simpa only [e, positiveBufferEnergyOfLift_base, positiveBufferEnergyOfLift_derivative] using ht.symm

theorem positiveBuffer_indicator_inner_sub_border {g : RadialL2} {l h : ℝ}
    (hg : (g : ℝ → ℝ) =ᵐ[volume.restrict (Ioo l h)ᶜ] (fun _ => 0))
    (f v : RadialL2) (a : ℝ) :
    ⟪bufferL2Indicator (Ioo l h) measurableSet_Ioo (f - a • g), v⟫_ℝ =
      ⟪bufferL2Indicator (Ioo l h) measurableSet_Ioo f, v⟫_ℝ - a * ⟪g, v⟫_ℝ := by
  rw [positiveBuffer_indicator_inner, inner_sub_left, inner_smul_left, conj_trivial,
    ← positiveBuffer_indicator_inner (Ioo l h) measurableSet_Ioo f v,
    ← positiveBuffer_indicator_inner (Ioo l h) measurableSet_Ioo g v,
    bufferL2Indicator_eq_self_of_supported (Ioo l h) measurableSet_Ioo g hg]

/-- Restriction preserves the scalar border. The retained source makes
this equivalence valid for arbitrary outside values of the source. -/
theorem positiveBuffer_borderedIntervalGraph_iff_zero_trace_form {V : ℝ → ℝ}
    (hV : Continuous V) (hreal : ActualClosedFormRealization V) {l h : ℝ} (hlh : l < h)
    (g : RadialL2) (bordered : Bool) (U : PositiveBufferBorderedEnergy V bordered)
    (F : RadialL2 × ℝ)
    (hg : (g : ℝ → ℝ) =ᵐ[volume.restrict (Ioo l h)ᶜ] (fun _ => 0))
    (hU : (positiveBufferEnergyCoordinate V 0 U.val.1 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo l h)ᶜ]
      (fun _ => 0)) (hF : bordered = false → F.2 = 0) :
    BorderedIntervalGraph V g bordered l h (positiveBufferBorderedState V bordered U) F ↔
      ∀ W : PositiveBufferBorderedEnergy V bordered,
        positiveBufferTraceAt V l W.val.1 = 0 → positiveBufferTraceAt V h W.val.1 = 0 →
        positiveBufferBorderedForm V hV g bordered U W =
          positiveBufferStatePairing (positiveBufferRetainedProjection l h F)
            (positiveBufferBorderedState V bordered W) := by
  cases bordered with
  | false =>
    have hUs : U.val.2 = 0 := U.property rfl
    have hFs : F.2 = 0 := hF rfl
    simp only [BorderedIntervalGraph, Bool.false_eq_true, ite_false,
      positiveBufferBorderedState_apply]
    constructor
    · rintro ⟨hgraph, _, _⟩ W hl hh
      have he := (positiveBuffer_intervalGraph_iff_zero_trace_form hV hreal hlh U.val.1 F.1 hU).mp
        hgraph W.val.1 hl hh
      simpa only [positiveBufferBorderedForm, positiveBufferStatePairing_apply,
        positiveBufferRetainedProjection_apply, positiveBufferBorderedState_apply,
        hUs, W.property rfl, zero_mul, mul_zero, add_zero] using he
    · intro H
      refine ⟨(positiveBuffer_intervalGraph_iff_zero_trace_form hV hreal hlh U.val.1 F.1 hU).mpr ?_,
        hUs, hFs⟩
      intro w hl hh
      let W : PositiveBufferBorderedEnergy V false := ⟨(w, 0), by intro _; rfl⟩
      have he := H W hl hh
      simpa only [positiveBufferBorderedForm, positiveBufferStatePairing_apply,
        positiveBufferRetainedProjection_apply, positiveBufferBorderedState_apply,
        W, hUs, zero_mul, mul_zero, add_zero] using he
  | true =>
    simp only [BorderedIntervalGraph, ite_true, positiveBufferBorderedState_apply]
    constructor
    · rintro ⟨hgraph, hscalar⟩ W hl hh
      have he := (positiveBuffer_intervalGraph_iff_zero_trace_form hV hreal hlh U.val.1
        (F.1 - U.val.2 • g) hU).mp hgraph W.val.1 hl hh
      rw [positiveBuffer_indicator_inner_sub_border hg] at he
      simp only [positiveBufferBorderedForm, positiveBufferStatePairing_apply,
        positiveBufferRetainedProjection_apply, positiveBufferBorderedState_apply]
      rw [he, hscalar]
      ring
    · intro H
      have hscalar : ⟪g, positiveBufferEnergyCoordinate V 0 U.val.1⟫_ℝ = F.2 := by
        let W : PositiveBufferBorderedEnergy V true := ⟨(0, 1), by intro h; cases h⟩
        have hl : positiveBufferTraceAt V l W.val.1 = 0 := by
          change positiveBufferTraceAt V l 0 = 0
          exact map_zero _
        have hh : positiveBufferTraceAt V h W.val.1 = 0 := by
          change positiveBufferTraceAt V h 0 = 0
          exact map_zero _
        have he := H W hl hh
        simpa only [positiveBufferBorderedForm, positiveBufferStatePairing_apply,
          positiveBufferRetainedProjection_apply, positiveBufferBorderedState_apply,
          W, map_zero, inner_zero_right, zero_mul, mul_zero, one_mul, mul_one,
          zero_add, add_zero] using he
      refine ⟨(positiveBuffer_intervalGraph_iff_zero_trace_form hV hreal hlh U.val.1
        (F.1 - U.val.2 • g) hU).mpr ?_, hscalar⟩
      intro w hl hh
      let W : PositiveBufferBorderedEnergy V true := ⟨(w, 0), by intro h; cases h⟩
      have he := H W hl hh
      have he' : positiveBufferEnergyForm V hV U.val.1 w +
          U.val.2 * ⟪g, positiveBufferEnergyCoordinate V 0 w⟫_ℝ =
          ⟪bufferL2Indicator (Ioo l h) measurableSet_Ioo F.1,
            positiveBufferEnergyCoordinate V 0 w⟫_ℝ := by
        simpa only [positiveBufferBorderedForm, positiveBufferStatePairing_apply,
          positiveBufferRetainedProjection_apply, positiveBufferBorderedState_apply,
          W, zero_mul, mul_zero, add_zero] using he
      rw [positiveBuffer_indicator_inner_sub_border hg]
      linarith

/-- Every frozen interval-graph solution has an actual supported energy
lift with zero endpoint traces, even for an unrestricted exterior source. -/
theorem positiveBuffer_exists_bordered_energy_of_intervalGraph {V : ℝ → ℝ}
    (hreal : ActualClosedFormRealization V) (g : RadialL2) (bordered : Bool)
    (l h : ℝ) (U F : RadialL2 × ℝ) (hgraph : BorderedIntervalGraph V g bordered l h U F) :
    ∃ e : PositiveBufferBorderedEnergy V bordered,
      positiveBufferBorderedState V bordered e = U ∧
      (positiveBufferEnergyCoordinate V 0 e.val.1 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo l h)ᶜ]
        (fun _ => 0) ∧
      positiveBufferTraceAt V l e.val.1 = 0 ∧ positiveBufferTraceAt V h e.val.1 = 0 := by
  have hdom : ∃ d q : RadialL2, (U.1, d, q) ∈ closure (IntervalEnergyCore V l h) := by
    cases bordered with
    | false =>
      simp only [BorderedIntervalGraph, Bool.false_eq_true, ite_false] at hgraph
      obtain ⟨d, q, hd, _⟩ := hgraph.1
      exact ⟨d, q, hd⟩
    | true =>
      simp only [BorderedIntervalGraph, ite_true] at hgraph
      obtain ⟨d, q, hd, _⟩ := hgraph.1
      exact ⟨d, q, hd⟩
  have hscalar : bordered = false → U.2 = 0 := by
    intro hb
    subst bordered
    simp only [BorderedIntervalGraph, Bool.false_eq_true, ite_false] at hgraph
    exact hgraph.2.1
  obtain ⟨d, q, hd⟩ := hdom
  let u := positiveBufferEnergyOfLift U.1 d q (intervalEnergyClosure_subset_energy V l h hreal hd)
  let e : PositiveBufferBorderedEnergy V bordered := ⟨(u, U.2), hscalar⟩
  have hs : (positiveBufferEnergyCoordinate V 0 u : ℝ → ℝ) =ᵐ[volume.restrict (Ioo l h)ᶜ]
      (fun _ => 0) := intervalEnergyClosure_supported V l h hd
  have ht := positiveBufferEnergy_supported_zero_trace u hs
  exact ⟨e, Prod.ext rfl rfl, hs, ht.1, ht.2⟩

end ContinuousFlexibility.Radial
