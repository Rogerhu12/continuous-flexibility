module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledFamily
public import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentSplit

/-!
# The gauge of the selected controlled positive family

The retained transport, inverse and height are inserted into the actual
whole reference atlas. Its admissibility uses the same buffer and the
same endpoint matching produced by the controlled construction.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

namespace N04PositiveGeometryControlledFamily

variable {W : N04RealizationStart} {X : N04RealizationChoice W}

def gauge (F : N04PositiveGeometryControlledFamily W X 3)
    (e : ℕ ≃ N04WholePieceIndex W.D)
    (Y H : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ) :
    N04RealizationGauge :=
  .mk W X e Y H F.toN04PositiveGeometryControlData.τ F.toN04PositiveGeometryControlData.σ
    F.toN04PositiveGeometryControlData.Q F.buffer.region

theorem gauge_admissible (F : N04PositiveGeometryControlledFamily W X 3)
    (e : ℕ ≃ N04WholePieceIndex W.D)
    (Y H : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (href : N04PositiveReferenceFamily (W.A X.e₀) X.src 4 Y H) :
    (F.gauge e Y H).Admissible F.base F.ε :=
  ⟨F.base_le, F.radius_pos, F.radius_le, href, F.reference, F.buffer,
    F.toN04PositiveGeometryControlData.lower, F.toN04PositiveGeometryControlData.upper,
    rfl, F.matching⟩

end N04PositiveGeometryControlledFamily

end ContinuousFlexibility.Analysis
