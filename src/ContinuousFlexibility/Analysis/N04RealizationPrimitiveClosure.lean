module

public import ContinuousFlexibility.Analysis.N04RealizationPrimitiveDirectionClosure
public import ContinuousFlexibility.Analysis.N04RealizationPrimitiveInitialClosure

/-!
# Collecting the fifteen actual primitive fields

The finite factor certificate controls the nine direction components,
three normalized initial factors, and three reference multipliers on
the same material piece. No new coordinate representative is chosen.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}

/-- Each frozen primitive field is estimated from the proved raw-factor
certificate. Reference source factors are identified as functions before
their derivatives are transferred. -/
theorem n04Realization_primitive_envelopes_of_factors
    {X : Type*} (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hgeom : CanonicalGeometry D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    {W : X → ℝ} (hW : ∀ x, 1 ≤ W x)
    (z : X → AnnularState S × ℝ) (m : X → ℕ) (p : X → PolarPoint)
    (hz : ∀ x, z x ∈ stateNeighborhood S C base ε)
    (hs : ∀ x, stateSector S (z x).1)
    (hp : ∀ x, n07bMaterialRadiusChart T (p x) ∈ physicalPieceOpen S K (z x) (m x))
    (hE : ∀ x, T.E0 (T.radius (p x).1) ≤ W x)
    (hRatio : HasPositiveEnvelope W
      (fun x => T.H (T.radius (p x).1) / T.H (T.sample (K.cell (m x)))))
    (N : ℕ) (H : N04RealizationPrimitiveFactorEnvelopes X T S C K W z m p N) :
    ∀ i : CanonicalPrimitiveIndex, ∀ k : ℕ, k ≤ N → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ k
        (canonicalPrimitiveField D T C K (z x) (m x) i ∘ n07bMaterialRadiusChart T)
        (p x)‖) := by
  intro i k hk
  rcases i with ⟨i, j⟩ | (i | i)
  · exact n04Realization_primitiveDirection_envelopes hT hgeom href hsref hW
      z m p hz hs hp hE N H i j k hk
  · exact n04Realization_primitiveInitial_envelopes hD hT hgeom href hsref hW
      z m p hz hs hp hRatio N H i k hk
  · apply n04Realization_materialReferenceMultiplier_envelope
      hD hT hgeom href hsref hW z m p hz hs hp (fun _ => i) k
    · intro j hj hjk
      exact H.referencePoint j hj (by omega)
    · intro j hj
      apply n04Realization_envelope_jets_congr p
        (fun x y => canonicalSource S K (C.referenceState, 0) (m x) (fun _ => 1)
          (K.chart (z x) (m x) (n07bMaterialRadiusChart T y)))
        (fun x => canonicalReferenceSourceFactor C K (z x) (m x) ∘
          n07bMaterialRadiusChart T) j (H.source true false j (by omega))
      intro x
      exact Eventually.of_forall (fun y =>
        (congrFun (n04Realization_referenceSourceFactor_eq (C := C) (K := K)
          (z := z x) (m x)) (n07bMaterialRadiusChart T y)).symm)

end ContinuousFlexibility.Analysis
