import ContinuousFlexibility.Radial.PositiveBufferComparisonBufferTrace
import ContinuousFlexibility.Radial.PositiveBufferTraceMap

/-!
# Sharp traces of actual energy corrections

These wrappers use the canonical continuous representative of the
closed energy domain. The cutoff source and scalar border vanish in
both comparison regions, so one estimate applies to every entry of
the cut-correction matrix.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem positiveBufferGreenCorrection_homogeneous {B : BufferData}
    (hB : BufferHypotheses B) (j : Fin 2) (A scalar : ℝ) (pin dpin U : ℝ → ℝ)
    (hEq : ∀ x : ℝ, -deriv (deriv U) x + B.potential x * U x =
      positiveBufferGreenError B j A pin dpin x - scalar * B.borderFunction x)
    (i : Fin 2) {t : ℝ} (ht : t < B.action i + 2) :
    -deriv (deriv U) (positiveBufferPoint B i t) +
      B.potential (positiveBufferPoint B i t) * U (positiveBufferPoint B i t) = 0 := by
  rw [hEq, positiveBufferGreenError_zero_on_buffer hB i j A pin dpin ht,
    positiveBufferPoint_border_eq_zero hB i (by linarith), mul_zero, sub_zero]

theorem positiveBufferEnergyRepresentative_cut_trace_bound {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) (u : PositiveBufferEnergy B.potential)
    (hU : ContDiff ℝ ∞ (positiveBufferEnergyRepresentative B.potential u))
    (hhom : ∀ t : ℝ, t < B.action i + 2 →
      -deriv (deriv (positiveBufferEnergyRepresentative B.potential u))
          (positiveBufferPoint B i t) +
        B.potential (positiveBufferPoint B i t) *
          positiveBufferEnergyRepresentative B.potential u (positiveBufferPoint B i t) = 0) :
    |positiveBufferEnergyRepresentative B.potential u (bufferCut B i)| ≤
      sqrt (B.mass i) * exp (-B.action i) * ‖positiveBufferEnergyCoordinate B.potential 0 u‖ := by
  exact positiveBuffer_oriented_cut_trace_bound (M := 2 * ‖u‖) hB i hU
    (positiveBufferEnergyCoordinate B.potential 0 u)
    (positiveBufferEnergyRepresentative_spec B.potential u).2.1 (by positivity)
    (positiveBufferEnergyRepresentative_bound B.potential u) hhom

theorem positiveBufferEnergyGreenCorrection_cut_trace_bound {B : BufferData}
    (hB : BufferHypotheses B) (i j : Fin 2) (A scalar : ℝ) (pin dpin : ℝ → ℝ)
    (u : PositiveBufferEnergy B.potential)
    (hU : ContDiff ℝ ∞ (positiveBufferEnergyRepresentative B.potential u))
    (hEq : ∀ x : ℝ, -deriv (deriv (positiveBufferEnergyRepresentative B.potential u)) x +
      B.potential x * positiveBufferEnergyRepresentative B.potential u x =
        positiveBufferGreenError B j A pin dpin x - scalar * B.borderFunction x)
    {N : ℝ} (hN : ‖positiveBufferEnergyCoordinate B.potential 0 u‖ ≤ N) :
    |positiveBufferEnergyRepresentative B.potential u (bufferCut B i)| ≤
      sqrt (B.mass i) * exp (-B.action i) * N := by
  apply (positiveBufferEnergyRepresentative_cut_trace_bound hB i u hU
    (fun t ht => positiveBufferGreenCorrection_homogeneous hB j A scalar pin dpin
      (positiveBufferEnergyRepresentative B.potential u) hEq i ht)).trans
  exact mul_le_mul_of_nonneg_left hN (by positivity)

end ContinuousFlexibility.Radial
