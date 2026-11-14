module

public import ContinuousFlexibility.Radial.PositiveBufferFullForm
public import ContinuousFlexibility.Radial.PositiveBufferTraceMap

/-!
# Concrete normalized corrected Green data

The columns are genuine bordered energy fields. Their smooth retained
representatives have the same true traces and the actual homogeneous
equation. The conormal and form identities retain the normalization by
the sum of the finite and exterior conormals.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

structure PositiveBufferCorrectedData (B : BufferData)
    (A αout : Fin 2 → ℝ) (K η : ℝ) where
  column : Fin 2 → PositiveBufferBorderedEnergy B.potential B.bordered
  representative : Fin 2 → ℝ → ℝ
  smooth : ∀ j, ContDiff ℝ ∞ (representative j)
  representative_eq : ∀ j,
    EqOn (representative j)
      (positiveBufferEnergyRepresentative B.potential
        (positiveBufferBorderedField B.potential B.bordered (column j)))
      (Icc B.l B.h)
  equation : ∀ j x, x ∈ Ioo B.l B.h →
    -deriv (deriv (representative j)) x + B.potential x * representative j x +
      positiveBufferBorderedScalar B.potential B.bordered (column j) * B.borderFunction x = 0
  border_row : ∀ j,
    if B.bordered then
      ⟪B.border, (positiveBufferBorderedState B.potential B.bordered (column j)).1⟫_ℝ = 0
    else (positiveBufferBorderedState B.potential B.bordered (column j)).2 = 0
  conormal : ∀ i j,
    bufferSign i * deriv (representative j) (bufferCut B i) =
      (if i = j then sqrt (A i) else 0) -
        αout i * representative j (bufferCut B i)
  delta_form : ∀ (hV : Continuous B.potential) j
      (W : PositiveBufferBorderedEnergy B.potential B.bordered),
    positiveBufferBorderedForm B.potential hV B.border B.bordered (column j) W =
      sqrt (A j) * positiveBufferTraceAt B.potential (bufferCut B j)
        (positiveBufferBorderedField B.potential B.bordered W)
  norm_bound : ∀ j,
    ‖positiveBufferBorderedState B.potential B.bordered (column j)‖ ≤ K / B.mass j
  trace_error : ∀ i j,
    |sqrt (A i) * representative j (bufferCut B i) - (if i = j then 1 else 0)| ≤
      η * (B.mass i * exp (-B.action i)) * (B.mass j * exp (-B.action j))

end ContinuousFlexibility.Radial
