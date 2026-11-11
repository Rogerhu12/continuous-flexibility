import ContinuousFlexibility.Blueprint.Statements
import ContinuousFlexibility.Analysis.PhysicalTransmissionJets
import ContinuousFlexibility.Analysis.PhysicalTransmissionGluing

/-!
# Blueprint node N04Transmission

Piecewise smooth solutions with matching value and conormal derivative have matching jets.

Source: `paper/flexible-surface-readable/07-fixed-geometry.tex` lines 1725–1755.

Task file: `docs/tasks/N04Transmission.md`. The actual equation determines
the normal jets, and the matching jets give a smooth physical gluing.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N04Transmission : PhysicalTransmissionTarget := by
  intro a r0 b L f u v har hrb ha hb hc hf hu hv hpositive hleft hright hvalue hconormal
  have hjets := physicalTransmission_matching_jets a r0 b L f u v
    har hrb ha hb hc hf hu hv hpositive hleft hright hvalue hconormal
  exact ⟨hjets, (contDiff_physicalTransmission r0 hu hv hjets).contDiffOn⟩

end ContinuousFlexibility.Blueprint

#print axioms ContinuousFlexibility.Blueprint.N04Transmission
