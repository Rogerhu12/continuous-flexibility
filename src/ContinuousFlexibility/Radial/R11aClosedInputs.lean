import ContinuousFlexibility.Blueprint.R06a
import ContinuousFlexibility.Blueprint.R06b
import ContinuousFlexibility.Blueprint.R06c
import ContinuousFlexibility.Radial.PositiveBufferR09

/-!
# Closed analytic inputs for the retained R11a construction

Only proved deep-tail nodes and the proved positive-buffer theorem are
used. Keeping this logical composition outside Blueprint.Assembly avoids
an import cycle with the final R11a node.
-/

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

theorem r11a_closed_regional_inputs : R06Statement ∧ R09Statement := by
  obtain ⟨C, η, K, hC, hη, hη₁, hK, hoperator⟩ := R06a
  obtain ⟨C₁, η₁, K₁, hC₁, hη₁', hη₁₁, hK₁, hfull⟩ :=
    R06b C η K hC hη hη₁ hK hoperator
  obtain ⟨C₂, η₂, K₂, hC₂, hη₂, hη₂₁, hK₂, hfull', hphysical, hparameter⟩ :=
    R06c C₁ η₁ K₁ hC₁ hη₁' hη₁₁ hK₁ hfull
  exact ⟨⟨C₂, η₂, K₂, hC₂, hη₂, hη₂₁, hK₂, hfull', hphysical, hparameter⟩,
    r09Statement⟩

end ContinuousFlexibility.Radial
