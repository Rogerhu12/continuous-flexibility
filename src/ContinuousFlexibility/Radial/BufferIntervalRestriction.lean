import ContinuousFlexibility.Radial.BufferIntervalDomain
import ContinuousFlexibility.Radial.PositiveBufferTraceMap

/-!
# Restriction of zero-trace fields to the genuine Dirichlet domain

An arbitrary global energy field with zero values at the two endpoints can
be restricted by measurable indicators. The three restricted coordinates
belong to the closure of the actual supported smooth core. This identifies
the derivative of the restriction without assuming exterior vanishing of
the original field.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

theorem bufferL2Indicator_inner_interval {l h : ℝ} (hlh : l ≤ h) (u v : RadialL2) :
    inner (𝕜 := ℝ) u (bufferL2Indicator (Ioo l h) measurableSet_Ioo v) =
      ∫ x in l..h, u x * v x := by
  rw [positiveBufferL2_inner_integral, intervalIntegral.integral_of_le hlh,
    integral_Ioc_eq_integral_Ioo]
  calc
    _ = ∫ x : ℝ, (Ioo l h).indicator (fun x => u x * v x) x := by
      apply integral_congr_ae
      filter_upwards [bufferL2Indicator_coeFn (Ioo l h) measurableSet_Ioo v] with x hx
      rw [hx]
      by_cases hxi : x ∈ Ioo l h
      · simp only [indicator_of_mem hxi]
      · simp only [indicator_of_notMem hxi, mul_zero]
    _ = _ := integral_indicator measurableSet_Ioo

/-- Restricting a true zero-trace global energy field gives precisely an
element of the public Dirichlet energy domain. -/
theorem intervalEnergyClosure_restrict_zero_traces {V : ℝ → ℝ} (hV : Continuous V)
    {l h : ℝ} (hlh : l < h) {u d q : RadialL2}
    (he : (u, d, q) ∈ SchrodingerEnergyLift V)
    {U : ℝ → ℝ} (hU : Continuous U) (hu : (u : ℝ → ℝ) =ᵐ[volume] U)
    (hUl : U l = 0) (hUh : U h = 0) :
    (bufferL2Indicator (Ioo l h) measurableSet_Ioo u,
      bufferL2Indicator (Ioo l h) measurableSet_Ioo d,
      bufferL2Indicator (Ioo l h) measurableSet_Ioo q) ∈
        closure (IntervalEnergyCore V l h) := by
  let z : PositiveBufferEnergyTriple := WithLp.toLp 2
    ![bufferL2Indicator (Ioo l h) measurableSet_Ioo u,
      bufferL2Indicator (Ioo l h) measurableSet_Ioo d,
      bufferL2Indicator (Ioo l h) measurableSet_Ioo q]
  have hz : z ∈ (bufferHilbertIntervalCore V l h)ᗮᗮ := by
    apply (Submodule.mem_orthogonal _ _).mpr
    intro w hw
    rw [PiLp.inner_apply, Fin.sum_univ_three]
    change inner (𝕜 := ℝ) (w 0) (bufferL2Indicator (Ioo l h) measurableSet_Ioo u) +
      inner (𝕜 := ℝ) (w 1) (bufferL2Indicator (Ioo l h) measurableSet_Ioo d) +
      inner (𝕜 := ℝ) (w 2) (bufferL2Indicator (Ioo l h) measurableSet_Ioo q) = 0
    rw [bufferL2Indicator_inner_interval hlh.le, bufferL2Indicator_inner_interval hlh.le,
      bufferL2Indicator_inner_interval hlh.le]
    have h0 : IntervalIntegrable (fun x : ℝ => w 0 x * u x) volume l h :=
      ((Lp.memLp (w 0)).integrable_mul (Lp.memLp u)).intervalIntegrable
    have h1 : IntervalIntegrable (fun x : ℝ => w 1 x * d x) volume l h :=
      ((Lp.memLp (w 1)).integrable_mul (Lp.memLp d)).intervalIntegrable
    have h2 : IntervalIntegrable (fun x : ℝ => w 2 x * q x) volume l h :=
      ((Lp.memLp (w 2)).integrable_mul (Lp.memLp q)).intervalIntegrable
    calc
      _ = ∫ x in l..h, w 0 x * u x + w 1 x * d x + w 2 x * q x := by
        rw [intervalIntegral.integral_add (h0.add h1) h2,
          intervalIntegral.integral_add h0 h1]
      _ = 0 := buffer_energy_interval_annihilator hV hlh he hU hu hUl hUh hw
  rw [(bufferHilbertIntervalCore V l h).orthogonal_orthogonal_eq_closure] at hz
  exact bufferHilbertIntervalCore_closure_maps V l h hz

/-- The restricted derivative is the actual weak derivative supplied by
the public core closure, under the closed-form realization hypothesis. -/
theorem bufferL2Indicator_interval_energy_of_zero_traces {V : ℝ → ℝ}
    (hV : Continuous V) (hreal : ActualClosedFormRealization V)
    {l h : ℝ} (hlh : l < h) {u d q : RadialL2}
    (he : (u, d, q) ∈ SchrodingerEnergyLift V)
    {U : ℝ → ℝ} (hU : Continuous U) (hu : (u : ℝ → ℝ) =ᵐ[volume] U)
    (hUl : U l = 0) (hUh : U h = 0) :
    (bufferL2Indicator (Ioo l h) measurableSet_Ioo u,
      bufferL2Indicator (Ioo l h) measurableSet_Ioo d,
      bufferL2Indicator (Ioo l h) measurableSet_Ioo q) ∈ SchrodingerEnergyLift V :=
  intervalEnergyClosure_subset_energy V l h hreal
    (intervalEnergyClosure_restrict_zero_traces hV hlh he hU hu hUl hUh)

/-- The same restriction statement using the canonical continuous trace
maps of the actual energy space. -/
theorem positiveBufferEnergy_restrict_zero_trace_mem_closure {V : ℝ → ℝ}
    (hV : Continuous V) {l h : ℝ} (hlh : l < h) (e : PositiveBufferEnergy V)
    (hl : positiveBufferTraceAt V l e = 0) (hh : positiveBufferTraceAt V h e = 0) :
    (bufferL2Indicator (Ioo l h) measurableSet_Ioo (positiveBufferEnergyCoordinate V 0 e),
      bufferL2Indicator (Ioo l h) measurableSet_Ioo (positiveBufferEnergyCoordinate V 1 e),
      bufferL2Indicator (Ioo l h) measurableSet_Ioo (positiveBufferEnergyCoordinate V 2 e)) ∈
        closure (IntervalEnergyCore V l h) := by
  have hrep := positiveBufferEnergyRepresentative_spec V e
  apply intervalEnergyClosure_restrict_zero_traces hV hlh e.property hrep.1 hrep.2.1
  · simpa only [positiveBufferTraceAt_apply] using hl
  · simpa only [positiveBufferTraceAt_apply] using hh

end ContinuousFlexibility.Radial
