import ContinuousFlexibility.Blueprint.Statements
import ContinuousFlexibility.Analysis.N04FlowJetsTarget
import ContinuousFlexibility.Analysis.N04RealizationLeadOptical
import ContinuousFlexibility.Analysis.N04RealizationLeadReference
import ContinuousFlexibility.Analysis.N04RealizationLeadSample
import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentProof
import ContinuousFlexibility.Blueprint.N04Coordinates.Realization.PositiveGeometry
import ContinuousFlexibility.Blueprint.N04Coordinates.Realization.NegativeGeometry
import ContinuousFlexibility.Blueprint.N04Coordinates.Realization.PulledFields
import ContinuousFlexibility.Blueprint.N04Coordinates.Realization.SourceColumns
import ContinuousFlexibility.Blueprint.N04Coordinates.Realization.Principal

/-!
# N04Coordinates: controlled coordinate realization

Use the actual mixed-parameter flow theorem to construct coordinates,
their inverses and height factors on one state neighborhood, retaining
N01–N03 and both qualitative canonical parts. Derive the actual potential
and divided-coefficient estimates and the source-pairing identity.

The same witness also carries the two primitive geometry payloads,
including the radial reference gauge, actual spatial and parameter jets,
and forward chart/height first-jet matching from the transmission domain.

The conclusion is exactly the frozen N04c statement. The witness is the
retained start with the reference-gauged atlas
(`n04Realization_of_obligations`). The optical, reference and sample
obligations are proved; the current obligation is split into the five
subnodes in `Blueprint/N04Coordinates/Realization/`
(`n04Realization_currentObligation_of_split`).

Source: paper/flexible-surface-readable/07-fixed-geometry.tex,
the root, positive-component and uniform-geometry constructions,
in particular lines 1211–1760.
Task: docs/tasks/N04Coordinates-Realization.md; subnodes:
docs/tasks/N04Realization-*.md.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N04CoordinatesRealization
    (hFlowJets : N04FlowJetsTarget) (hN04b : N04bStatement) : N04cStatement :=
  ContinuousFlexibility.Analysis.n04Realization_of_obligations
    ContinuousFlexibility.Analysis.n04Realization_opticalObligation
    ContinuousFlexibility.Analysis.n04Realization_referenceObligation
    (ContinuousFlexibility.Analysis.n04Realization_currentObligation_of_split
      N04RealizationPositiveGeometry N04RealizationNegativeGeometry N04RealizationPulledFields
      N04RealizationSourceColumns N04RealizationPrincipal)
    ContinuousFlexibility.Analysis.n04Realization_sampleObligation

end ContinuousFlexibility.Blueprint

#print axioms ContinuousFlexibility.Blueprint.N04CoordinatesRealization
