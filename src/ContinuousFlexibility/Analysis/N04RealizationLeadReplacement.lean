module

public import ContinuousFlexibility.Analysis.PhysicalSpacesAuxiliaryColumn
public import ContinuousFlexibility.Analysis.N04RealizationLeadGauge
public import ContinuousFlexibility.Analysis.N04RealizationSameWitnessCompletion

/-!
# Clauses that survive the auxiliary-column replacement

Replacing the auxiliary column changes only the field `psi` of the physical
spaces. Every clause below refers to the retained fields of the spaces,
geometry, correction and canonical records, so it transfers unchanged.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

variable {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
  (ψ : (S.height (3 / 4 : ℝ)).Space)

theorem cutOperator_replaceAuxiliaryColumn
    (h : CanonicalCutOperatorProperties S C L K base ε) :
    CanonicalCutOperatorProperties (physicalSpacesReplaceAuxiliaryColumn S ψ)
      (geometryReplaceAuxiliaryColumn C ψ) (correctionReplaceAuxiliaryColumn L ψ)
      (canonicalReplaceAuxiliaryColumn K ψ) base ε := h

theorem referenceRadial_replaceAuxiliaryColumn
    (h : CanonicalGeometry.ReferenceRadial S C K) :
    CanonicalGeometry.ReferenceRadial (physicalSpacesReplaceAuxiliaryColumn S ψ)
      (geometryReplaceAuxiliaryColumn C ψ) (canonicalReplaceAuxiliaryColumn K ψ) := h

theorem transmissionGeometry_replaceAuxiliaryColumn
    (h : CanonicalGeometry.TransmissionGeometry D S C K base ε) :
    CanonicalGeometry.TransmissionGeometry D (physicalSpacesReplaceAuxiliaryColumn S ψ)
      (geometryReplaceAuxiliaryColumn C ψ) (canonicalReplaceAuxiliaryColumn K ψ) base ε := h

theorem fieldRegularity_replaceAuxiliaryColumn
    (h : N04bFieldRegularity D S C L base ε) :
    N04bFieldRegularity D (physicalSpacesReplaceAuxiliaryColumn S ψ)
      (geometryReplaceAuxiliaryColumn C ψ) (correctionReplaceAuxiliaryColumn L ψ) base ε where
  smooth_coefficients := h.smooth_coefficients
  periodic_coefficients := h.periodic_coefficients
  positive_a := h.positive_a
  reference_flow := h.reference_flow
  negative_discriminant := h.negative_discriminant

theorem transportQualitative_replaceAuxiliaryColumn
    (h : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∃ τ : PolarPoint → PolarPoint, ∃ q : PolarPoint → ℝ,
        WholeCanonicalTransportQualitative (D := D) C K z τ q) :
    ∀ z ∈ stateNeighborhood (physicalSpacesReplaceAuxiliaryColumn S ψ)
        (geometryReplaceAuxiliaryColumn C ψ) base ε,
      stateSector (physicalSpacesReplaceAuxiliaryColumn S ψ) z.1 →
      ∃ τ : PolarPoint → PolarPoint, ∃ q : PolarPoint → ℝ,
        WholeCanonicalTransportQualitative (D := D) (geometryReplaceAuxiliaryColumn C ψ)
          (canonicalReplaceAuxiliaryColumn K ψ) z τ q := h

theorem sampleShift_replaceAuxiliaryColumn {T : MaterialData}
    (h : ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m x, x ∈ physicalPieceOpen S K z m →
        endpointX 1 (Statements.endpointDistance D (T.sample (K.cell m))) ≤
          endpointX 1 (Statements.endpointDistance D x.1) + B) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ stateNeighborhood (physicalSpacesReplaceAuxiliaryColumn S ψ)
        (geometryReplaceAuxiliaryColumn C ψ) base ε,
      stateSector (physicalSpacesReplaceAuxiliaryColumn S ψ) z.1 →
      ∀ m x, x ∈ physicalPieceOpen (physicalSpacesReplaceAuxiliaryColumn S ψ)
          (canonicalReplaceAuxiliaryColumn K ψ) z m →
        endpointX 1 (Statements.endpointDistance D
          (T.sample ((canonicalReplaceAuxiliaryColumn K ψ).cell m))) ≤
          endpointX 1 (Statements.endpointDistance D x.1) + B := h

end ContinuousFlexibility.Analysis
