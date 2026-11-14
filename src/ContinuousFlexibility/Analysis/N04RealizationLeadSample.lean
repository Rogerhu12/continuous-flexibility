module

public import ContinuousFlexibility.Analysis.N04RealizationLeadAssembly
public import ContinuousFlexibility.Analysis.WholeReferenceGaugeMaterialSamples

/-!
# The sample obligation

The ported sample displacement of the reference-gauged atlas, for the
original typed atlas of the start and any supplied charts and families.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

theorem n04Realization_sampleObligation : N04RealizationSampleObligation := by
  intro W X e Y H τ σ Q N
  have h := n04WholeReferenceGauge_sample_endpointX (e₀ := X.e₀) (e := e)
    (τ := τ) (σ := σ) (Q := Q) (N := N) W.hT W.hS W.through03 W.field X.cell X.cell_mem
    (fun i => positiveReferenceCylinderChart (Y i))
    (fun i => positiveReferenceCylinderInverse (Y i)) (fun i p => H i p.1)
  exact ⟨h.choose, h.choose_spec.1, fun z m p hp => (h.choose_spec.2 z m p hp).2⟩

end ContinuousFlexibility.Analysis
