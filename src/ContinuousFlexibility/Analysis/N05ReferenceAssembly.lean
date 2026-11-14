module

public import ContinuousFlexibility.Analysis.N05ReferenceInterface
public import ContinuousFlexibility.Analysis.N05ClosedGraphAssembly

/-!
# Assembling the frozen N05 domain from its analytic inverse and uniqueness

The graph carrier is the original physical relation. Its closedness and the
two inverse identities follow from the separately proved characterization.
All endpoint, material and angular estimates retain the same global inverse.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {V : VolumeModelData S K}
  (G : N05ReferenceInverseData S K V)
  (hR : ∀ u F, ReferenceCanonicalRelation D T S C K V G.weakExponent
    G.sourceMaterial G.outputMaterial G.lossMaterial u
      (V.forget (3 / 4 : ℝ) 0 2 F) ↔ u = G.baseInverse F)

def n05ReferenceDomain : CanonicalDomainData S K V 2 :=
  n05CanonicalDomainOfRelation D T S C K V 2 G.weakExponent
    G.sourceMaterial G.outputMaterial G.lossMaterial G.baseInverse G.globalInverse hR

theorem n05ReferenceDomain_properties (hV : IsVolumeModel T S K V)
    (hG : N05ReferenceInverseBounds D T S C K V G) :
    N05Properties D T S C K V 2 (n05ReferenceDomain G hR) := by
  rcases hG with ⟨hγ, hγβ, hloss, _, hglobal, _, hweights, hnormal⟩
  refine ⟨le_rfl, hV, hγ, hγβ, hloss, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact n05CanonicalDomainOfRelation_closed D T S C K V 2 G.weakExponent
      G.sourceMaterial G.outputMaterial G.lossMaterial G.baseInverse G.globalInverse hR
  · exact n05CanonicalDomainOfRelation_graph D T S C K V 2 G.weakExponent
      G.sourceMaterial G.outputMaterial G.lossMaterial G.baseInverse G.globalInverse hR
  · exact n05RelationInverse_right _ G.baseInverse hR
  · exact n05RelationInverse_left _ G.baseInverse hR
  · exact n05CanonicalDomainOfRelation_global D T S C K V 2 G.weakExponent
      G.sourceMaterial G.outputMaterial G.lossMaterial G.baseInverse G.globalInverse hR hglobal
  · exact n05RelationGraph_norm_bound _ G.baseInverse hR
  · exact hweights
  · obtain ⟨δ, _, _, hbound⟩ := hweights
    exact hbound (3 / 4 : ℝ) (Or.inr (Or.inl rfl))
  · exact hnormal

end ContinuousFlexibility.Statements
