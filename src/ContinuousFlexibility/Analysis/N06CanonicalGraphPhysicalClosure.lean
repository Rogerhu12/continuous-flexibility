import ContinuousFlexibility.Analysis.N06CanonicalGraphFourierCore
import ContinuousFlexibility.Analysis.N06ClosedPhysicalTests

/-!
# Physical identification reduces to the actual finite-height graph core

A continuous source operator on the original graph is physically identified
once its equation is established for genuine finite angular heights in that
graph. The named reconstruction, actual test pairings and finite test support
supply closedness; the original inverse supplies the dense approximants.
No assertion of convergence of boundary traces is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {base loss b : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K V b}

/-- The named weak equation is closed along the continuous operator on
the original graph, and the genuine finite-height core is dense there. -/
theorem n06_namedPhysicalWeakRelation_of_finiteGraphCore
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    (P : B.Space →L[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (hcore : ∀ u ∈ n06CanonicalGraphFiniteAngularCore B,
      N06NamedPhysicalWeakRelation D C L B z u (P u)) :
    ∀ u : B.Space, N06NamedPhysicalWeakRelation D C L B z u (P u) := by
  have hclosed := (n06_namedPhysicalWeakRelation_isClosed
    (B := B) hT hS h.1 h.2.2.1 hcoordinates hz hs).preimage
      (continuous_id.prodMk P.continuous)
  have hsubset : n06CanonicalGraphFiniteAngularCore B ⊆
      {u : B.Space | N06NamedPhysicalWeakRelation D C L B z u (P u)} := hcore
  have hclosure := closure_minimal hsubset hclosed
  exact fun u => hclosure (n06CanonicalGraphFiniteAngularCore_dense hT hS h hcoordinates u)

/-- The original physical relation, including its normalization row,
follows for every graph element from the finite-height weak equations. -/
theorem n06_perturbedCanonicalRelation_of_finiteGraphCore
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    (P : B.Space →L[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (hcore : ∀ u ∈ n06CanonicalGraphFiniteAngularCore B,
      N06NamedPhysicalWeakRelation D C L B z u (P u)) :
    ∀ u : B.Space, PerturbedCanonicalRelation D S C K L z u.val.1
      (V.forget (3 / 4 : ℝ) 0 b (P u)) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  have hab : D.a ≤ D.b := h01.1.1.choose_spec.1.2.1.le
  intro u
  exact n06_namedPhysicalWeakRelation_implies hab h04 h.2 href hsector hz hs u (P u)
    (n06_namedPhysicalWeakRelation_of_finiteGraphCore hT hS h hcoordinates hz hs P hcore u)

end ContinuousFlexibility.Statements
