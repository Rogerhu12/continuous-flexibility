import ContinuousFlexibility.Analysis.N06CurrentFiniteGreenRelation
import ContinuousFlexibility.Analysis.N06PrimitiveFiniteGreenAssembly
import ContinuousFlexibility.Analysis.N06PrimitiveLeftColumnPairing
import ContinuousFlexibility.Analysis.N06PrimitivePhysicalClosure

/-!
# True finite Green data give the original physical relation

The primitive reference jets provide local finiteness on the same atlas.
The actual left-column identity removes the affine defect.  The original
graph core is dense and the named physical residual is closed there, so
the genuine finite identities pass to every element of the same graph.
No physical equation or operator bound is an input to the finite data.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory CanonicalGeometry
open ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K V b} {z : AnnularState S × ℝ}

/-- All local endpoint and source identities give the full original weak
equation. Positive regularity follows from the actual primitive fields. -/
theorem n06_namedPhysicalWeakRelation_of_primitiveFiniteGreen
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (u : B.Space) (F : V.level (3 / 4 : ℝ) 0 b)
    (hdata : ∀ φ, RadialTest D φ → Nonempty (N06CurrentFiniteGreenData D S C L K z
      u.val.1 (V.forget (3 / 4 : ℝ) 0 b F) φ)) :
    N06NamedPhysicalWeakRelation D C L B z u F := by
  intro φ hφ
  obtain ⟨P⟩ := hdata φ hφ
  have he := n06_primitive_finiteGreen_assembly hT hS h01 h03 h04 href hz hs
    u.val.1 (V.forget (3 / 4 : ℝ) 0 b F) hφ P.test P.value P.radialCoefficient P.reverse
    P.regular P.represents P.endpointCircles P.green P.matching
  have hpositive := fun m (_ : K.positive m = true) =>
    n06_primitive_current_principal_smooth h01 h04 href hcur hz hs m
  rw [n06_primitive_currentLeftColumn_full_pairing hT hS h01 h03 h04 href
    hz hs hpositive hφ, sub_self, mul_zero] at he
  exact sub_eq_zero.mp he

/-- Actual finite-core local data imply the unchanged relation on the
entire original graph. The dense core, normalization, test integrability
and periodic representatives all belong to the retained K, V and B. -/
theorem n06_perturbedCanonicalRelation_of_primitiveFiniteGreenCore
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hradial : ReferenceRadial S C K) (hAux : AuxiliaryColumnGauge S K)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (P : B.Space →L[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (hdata : ∀ u ∈ n06CanonicalGraphFiniteAngularCore B,
      ∀ φ, RadialTest D φ → Nonempty (N06CurrentFiniteGreenData D S C L K z
        u.val.1 (V.forget (3 / 4 : ℝ) 0 b (P u)) φ)) :
    ∀ u : B.Space, PerturbedCanonicalRelation D S C K L z u.val.1
      (V.forget (3 / 4 : ℝ) 0 b (P u)) := by
  apply n06_perturbedCanonicalRelation_of_primitiveFiniteGraphCore
    hT hS h hradial hAux href hz hs P
  intro u hu
  exact n06_namedPhysicalWeakRelation_of_primitiveFiniteGreen hT hS h.1.1.1.1
    h.1.1.2 h.1.2.2.2.2.1 href hcur hz hs u (P u) (hdata u hu)

end ContinuousFlexibility.Statements
