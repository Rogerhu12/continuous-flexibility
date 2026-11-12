import ContinuousFlexibility.Analysis.N06PrimitiveActualOperator
import ContinuousFlexibility.Analysis.N06PrimitiveRelativePhysicalRelation
import ContinuousFlexibility.Analysis.N06PrimitiveRelativeFamily

/-!
# Canonical relative operators from the retained primitive geometry

The actual principal, potential and scalar sources produce a bounded
endomorphism on the original N05 source level. The actual finite Green
identities and their closure give its physical equation on the original
graph. The family selection then gives exactly the inner existence
conclusion of `N06CanonicalRelativeStatement`.

The primitive construction facts remain explicit inputs here. This leaf
does not alter a frozen statement or replace K, V, B, or the neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis CanonicalGeometry

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K V b}

local instance n06PrimitiveCanonicalRelativeLevelGroup :
    NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) := Submodule.normedAddCommGroup _
local instance n06PrimitiveCanonicalRelativeLevelSpace :
    NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) := Submodule.normedSpace _
local instance n06PrimitiveCanonicalRelativeGraphGroup : NormedAddCommGroup B.Space :=
  Submodule.normedAddCommGroup _
local instance n06PrimitiveCanonicalRelativeGraphSpace : NormedSpace ℝ B.Space :=
  Submodule.normedSpace _

/-- The exact internal canonical-relative conclusion on the retained
N05 construction, from the raw primitive construction properties. -/
theorem n06_exists_canonicalRelative_of_primitiveGeometry
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hgeometry : PrimitiveGeometryProperties D T S C L K base ε) :
    ∃ P : AnnularState S × ℝ → B.Space →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
      ∃ order : ℕ, ∃ M : ℝ, 0 ≤ M ∧
        (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
          ∀ u : B.Space, PerturbedCanonicalRelation D S C K L z u.val.1
            (V.forget (3 / 4 : ℝ) 0 b (P z u))) ∧
        (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
          ‖n06RelativeOperator P z‖ ≤
            M * (stateGrading S order (z.1 - C.referenceState) + |z.2|)) := by
  obtain ⟨hradial, hprincipal, href, hcur, hAux, htransmission⟩ := hgeometry
  obtain ⟨order, Q, hQ, hsourcePackage⟩ :=
    n06_primitiveActual_relative_source_package hT hS h href hcur hprincipal hradial hAux
  have hstate : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∃ M : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
        ‖M‖ ≤ Q * (stateGrading S order (z.1 - C.referenceState) + |z.2|) ∧
        ∀ u : B.Space, PerturbedCanonicalRelation D S C K L z u.val.1
          (V.forget (3 / 4 : ℝ) 0 b (n06OperatorFromRelative B M u)) := by
    intro z hz hs
    obtain ⟨Mc, Mp, columns, M, _hM, hnorm, hweak, hnegative, hsource⟩ :=
      hsourcePackage z hz hs
    refine ⟨M, hnorm, ?_⟩
    exact n06_primitiveRelative_operator_physical hT hS h hradial hAux href hcur
      hprincipal htransmission hz hs Mc M hweak hnegative hsource
  obtain ⟨P, hphysical, hrelative, _houtside⟩ :=
    n06_exists_primitiveRelativeFamily h order Q hstate
  exact ⟨P, order, Q, hQ, hphysical, hrelative⟩

end ContinuousFlexibility.Statements
