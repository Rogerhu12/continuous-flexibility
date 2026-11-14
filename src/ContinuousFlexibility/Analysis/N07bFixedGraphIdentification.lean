module

public import ContinuousFlexibility.Analysis.N07aBaseInverse
public import ContinuousFlexibility.Analysis.N07bScalarInverseWeak
public import ContinuousFlexibility.Analysis.N07bWeakSourceUniqueness

/-!
# Identifying the actual represented scalar solution

Once the physical field has been placed in the actual reference graph,
N06's physical weak relation determines its current source uniquely. The
two existing inverse identities then identify the entire graph element,
including all three scalar coordinates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S}
  {L : ReturnCorrectionData S} {V : VolumeModelData S K} {b base : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K V b} {P : RelativeInverseData S K V b B}
  {G : ScalarInverseData S}

private theorem n07b_scalarInverse_weak_of_primitive
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hG : ScalarInverseProperties D S C L G base ε)
    (hgeom : CanonicalPrimitiveGeometry D T S C L K base ε)
    (hab : D.a < D.b) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (f : S.Source) {U : CanonicalUnknown S K} {Fseq : CanonicalSequence S K}
    (hrep : HasCanonicalRepresentation D S C K z U Fseq
      (heightPairField S (G.G z f).1) ((S.height (3 / 4 : ℝ)).decode f.val))
    (hμ : U.2.2.1 = (G.G z f).2) (hcompat : U.2.2.2 = 0) :
    PerturbedCanonicalRelation D S C K L z U Fseq := by
  have hphys := hgeom.physicalCoefficients z hz hs
  exact n07b_scalarInverse_perturbedCanonicalRelation hT hS hG hab hz hs f
    hphys.1 hphys.2.1 hphys.2.2.1 hphys.2.2.2.1 hphys.2.2.2.2 hrep hμ hcompat

local instance n07bFixedGraphLevelNormedAddCommGroup :
    NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedAddCommGroup _
local instance n07bFixedGraphLevelNormedSpace :
    NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedSpace _
local instance n07bFixedGraphUnknownNormedAddCommGroup :
    NormedAddCommGroup (CanonicalUnknown S K) := inferInstance
local instance n07bFixedGraphUnknownNormedSpace :
    NormedSpace ℝ (CanonicalUnknown S K) := inferInstance
local instance n07bFixedGraphDomainNormedAddCommGroup :
    NormedAddCommGroup B.Space := Submodule.normedAddCommGroup _
local instance n07bFixedGraphDomainNormedSpace :
    NormedSpace ℝ B.Space := Submodule.normedSpace _

/-- The fixed-domain algebra identifies the whole canonical unknown before
any physical scalar coordinates or representative are projected. -/
theorem n07b_fixedGraph_unknown_eq_of_physical_relation
    (hK : N04PartA D S C K base ε)
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hab : D.a ≤ D.b) (U : CanonicalUnknown S K)
    (F Fref : V.level (3 / 4 : ℝ) 0 b)
    (href : ReferenceCanonicalRelation D T S C K V B.weakExponent
      B.sourceMaterial B.outputMaterial B.lossMaterial U
        (V.forget (3 / 4 : ℝ) 0 b Fref))
    (hweak : PerturbedCanonicalRelation D S C K L z U
      (V.forget (3 / 4 : ℝ) 0 b F)) :
    (B.inverse (P.inverse z F)).val.1 = U := by
  have hmem : (U, Fref) ∈ B.graph := (h05.2.2.2.2.2.2.1 (U, Fref)).mpr href
  let d₀ : B.Space := ⟨(U, Fref), hmem⟩
  have hop : P.operator z d₀ = F :=
    n07b_relativeOperator_eq_of_physical_relation hK h05.2.1 h06 hz hs hab d₀ F hweak
  have hid : n07aBaseInverse B P z F = d₀ :=
    n07aBaseInverse_eq_of_operator h05 h06 hz hs hop
  have hactual : B.inverse (P.inverse z F) = d₀ :=
    (n07aBaseInverse_apply B P z F).symm.trans hid
  exact congrArg (fun d : B.Space => d.val.1) hactual

theorem n07b_fixedGraph_scalarInverse_identification
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hK : N04PartA D S C K base ε)
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (hG : ScalarInverseProperties D S C L G base ε)
    (hgeom : CanonicalPrimitiveGeometry D T S C L K base ε)
    (hab : D.a < D.b) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (f : S.Source) (F Fref : V.level (3 / 4 : ℝ) 0 b)
    (U : CanonicalUnknown S K)
    (href : ReferenceCanonicalRelation D T S C K V B.weakExponent
      B.sourceMaterial B.outputMaterial B.lossMaterial U
        (V.forget (3 / 4 : ℝ) 0 b Fref))
    (hrep : HasCanonicalRepresentation D S C K z U
      (V.forget (3 / 4 : ℝ) 0 b F)
      (heightPairField S (G.G z f).1) ((S.height (3 / 4 : ℝ)).decode f.val))
    (ha : U.2.1 = (G.G z f).1.2)
    (hμ : U.2.2.1 = (G.G z f).2) (hcompat : U.2.2.2 = 0) :
    let d := B.inverse (P.inverse z F)
    d.val.1.2.2.2 = 0 ∧
      d.val.1.2.1 = (G.G z f).1.2 ∧ d.val.1.2.2.1 = (G.G z f).2 ∧
      HasCanonicalRepresentation D S C K z d.val.1
        (V.forget (3 / 4 : ℝ) 0 b F)
        (heightPairField S (G.G z f).1) ((S.height (3 / 4 : ℝ)).decode f.val) := by
  have hweak : PerturbedCanonicalRelation D S C K L z U
      (V.forget (3 / 4 : ℝ) 0 b F) :=
    n07b_scalarInverse_weak_of_primitive (Fseq := V.forget (3 / 4 : ℝ) 0 b F)
      hT hS hG hgeom hab hz hs f hrep hμ hcompat
  have hU : (B.inverse (P.inverse z F)).val.1 = U :=
    n07b_fixedGraph_unknown_eq_of_physical_relation hK h05 h06 hz hs hab.le U F Fref
      href hweak
  dsimp only
  rw [hU]
  exact ⟨hcompat, ha, hμ, hrep⟩

end ContinuousFlexibility.Analysis
