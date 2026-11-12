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

/- Only abstract propositions occur in the motives of these eliminators. -/
private theorem n06_canonicalRelative_bind_budget
    {X Y : Type*} (P : X → Y → Prop) (Goal : Prop)
    (h : ∃ x y, P x y) (hnext : ∀ x y, P x y → Goal) : Goal :=
  h.elim (fun x hx => hx.elim (fun y hy => hnext x y hy))

private theorem n06_canonicalRelative_bind_source
    {X Y Z W : Type*} (P : X → Y → Z → W → Prop) (Goal : Prop)
    (h : ∃ x y z w, P x y z w) (hnext : ∀ x y z w, P x y z w → Goal) : Goal :=
  h.elim (fun x hx => hx.elim (fun y hy => hy.elim (fun z hz =>
    hz.elim (fun w hw => hnext x y z w hw))))

private theorem n06_canonicalRelative_finish_family
    {X I J : Type*} (A : J → Prop) (P : X → Prop)
    (Q : X → I → J → Prop) (R : X → Prop) (i : I) (j : J) (hj : A j)
    (h : ∃ x, P x ∧ Q x i j ∧ R x) :
    ∃ x, ∃ i, ∃ j, A j ∧ P x ∧ Q x i j :=
  h.elim (fun x hx => ⟨x, i, j, hj, hx.1, hx.2.1⟩)

private def N06CanonicalRelativeSourceFields
    (order : ℕ) (Q : ℝ) (z : AnnularState S × ℝ)
    (Mc Mp : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b)
    (M : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b) : Prop :=
  M = n06ActualRelativeMap B Mc Mp columns ∧
  ‖M‖ ≤ Q * (stateGrading S order (z.1 - C.referenceState) + |z.2|) ∧
  (∀ F m, K.positive m = true → ∀ φ, CanonicalTest S K m φ →
    (∫ p, V.forget (3 / 4 : ℝ) 0 b (Mc F) m p * φ p ∂canonicalMeasure S K m) =
      ∫ p, (B.inverse F).val.1.1 m p * divergenceOperator
        (n06CubicCoefficients (fun q => (q.1 - K.left m) * (K.right m - q.1))
          (K.dividedDifference z m).a (K.dividedDifference z m).b
          (K.dividedDifference z m).c) φ p ∂canonicalMeasure S K m) ∧
  (∀ F m, K.positive m ≠ true → V.forget (3 / 4 : ℝ) 0 b (Mc F) m = 0) ∧
  (∀ F m,
    (V.forget (3 / 4 : ℝ) 0 b (F + M F) m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m]
        n06CurrentRelativeSourceField D S C L K z (B.inverse F).val.1
          (V.forget (3 / 4 : ℝ) 0 b F) (V.forget (3 / 4 : ℝ) 0 b (Mc F)) m)

private def N06CanonicalRelativeSourceBudget (order : ℕ) (Q : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∃ Mc Mp : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
    ∃ columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b,
    ∃ M : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
      N06CanonicalRelativeSourceFields (D := D) (C := C) (L := L) (B := B)
        order Q z Mc Mp columns M

private def N06CanonicalRelativeState (order : ℕ) (Q : ℝ)
    (z : AnnularState S × ℝ) : Prop :=
  ∃ M : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
    ‖M‖ ≤ Q * (stateGrading S order (z.1 - C.referenceState) + |z.2|) ∧
    ∀ u : B.Space, PerturbedCanonicalRelation D S C K L z u.val.1
      (V.forget (3 / 4 : ℝ) 0 b (n06OperatorFromRelative B M u))

private def N06CanonicalRelativeConclusion : Prop :=
  ∃ P : AnnularState S × ℝ → B.Space →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
    ∃ order : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        ∀ u : B.Space, PerturbedCanonicalRelation D S C K L z u.val.1
          (V.forget (3 / 4 : ℝ) 0 b (P z u))) ∧
      (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        ‖n06RelativeOperator P z‖ ≤
          M * (stateGrading S order (z.1 - C.referenceState) + |z.2|))

set_option diagnostics true in
private theorem n06_canonicalRelative_physical_state
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hradial : ReferenceRadial S C K) (hprincipal : ReferencePrincipal T S C K)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hAux : AuxiliaryColumnGauge S K) (htransmission : TransmissionGeometry D S C K base ε)
    (order : ℕ) (Q : ℝ) (z : AnnularState S × ℝ)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hsource : ∃ Mc Mp : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
      ∃ columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b,
      ∃ M : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
        N06CanonicalRelativeSourceFields (D := D) (C := C) (L := L) (B := B)
          order Q z Mc Mp columns M) :
    N06CanonicalRelativeState (D := D) (C := C) (L := L) (B := B) order Q z := by
  exact n06_canonicalRelative_bind_source
    (N06CanonicalRelativeSourceFields (D := D) (C := C) (L := L) (B := B) order Q z)
    (N06CanonicalRelativeState (D := D) (C := C) (L := L) (B := B) order Q z)
    hsource (fun Mc _Mp _columns M hfields => ⟨M, hfields.2.1,
      n06_primitiveRelative_operator_physical
        (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
        (K := K) (V := V) (b := b) (B := B)
        (base := base) (loss := loss) (ε := ε) (z := z)
        hT hS h hradial hAux href hcur hprincipal htransmission hz hs Mc M
        hfields.2.2.1 hfields.2.2.2.1 hfields.2.2.2.2⟩)

set_option diagnostics true in
private theorem n06_canonicalRelative_from_fixed_budget
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hradial : ReferenceRadial S C K) (hprincipal : ReferencePrincipal T S C K)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hAux : AuxiliaryColumnGauge S K) (htransmission : TransmissionGeometry D S C K base ε)
    (order : ℕ) (Q : ℝ) (hQ : 0 ≤ Q)
    (hsource : N06CanonicalRelativeSourceBudget (D := D) (C := C) (L := L) (B := B)
      (base := base) (ε := ε) order Q) :
    N06CanonicalRelativeConclusion (D := D) (C := C) (L := L) (B := B)
      (base := base) (ε := ε) := by
  have hstate : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      N06CanonicalRelativeState (D := D) (C := C) (L := L) (B := B) order Q z :=
    fun z hz hs => n06_canonicalRelative_physical_state
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
      (K := K) (V := V) (b := b) (B := B)
      (base := base) (loss := loss) (ε := ε)
      hT hS h hradial hprincipal href hcur hAux htransmission order Q z hz hs
      (hsource z hz hs)
  exact n06_canonicalRelative_finish_family (fun Q : ℝ => 0 ≤ Q)
    (fun P : AnnularState S × ℝ → B.Space →L[ℝ] V.level (3 / 4 : ℝ) 0 b =>
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        ∀ u : B.Space, PerturbedCanonicalRelation D S C K L z u.val.1
          (V.forget (3 / 4 : ℝ) 0 b (P z u)))
    (fun P order Q => ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ‖n06RelativeOperator P z‖ ≤ Q *
        (stateGrading S order (z.1 - C.referenceState) + |z.2|))
    (fun P => ∀ z, ¬(z ∈ stateNeighborhood S C base ε ∧ stateSector S z.1) →
      n06RelativeOperator P z = 0)
    order Q hQ
    (n06_exists_primitiveRelativeFamily
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
      (K := K) (V := V) (b := b) (B := B)
      (base := base) (loss := loss) (ε := ε) h order Q hstate)

set_option diagnostics true in
private theorem n06_canonicalRelative_uniform
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hradial : ReferenceRadial S C K) (hprincipal : ReferencePrincipal T S C K)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hAux : AuxiliaryColumnGauge S K) (htransmission : TransmissionGeometry D S C K base ε) :
    N06CanonicalRelativeConclusion (D := D) (C := C) (L := L) (B := B)
      (base := base) (ε := ε) := by
  exact n06_canonicalRelative_bind_budget
    (fun (order : ℕ) (Q : ℝ) => 0 ≤ Q ∧
      N06CanonicalRelativeSourceBudget (D := D) (C := C) (L := L) (B := B)
        (base := base) (ε := ε) order Q)
    (N06CanonicalRelativeConclusion (D := D) (C := C) (L := L) (B := B)
      (base := base) (ε := ε))
    (n06_primitiveActual_relative_source_package
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
      (K := K) (V := V) (b := b) (B := B)
      (base := base) (loss := loss) (ε := ε)
      hT hS h href hcur hprincipal hradial hAux)
    (fun order Q hbudget => n06_canonicalRelative_from_fixed_budget
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
      (K := K) (V := V) (b := b) (B := B)
      (base := base) (loss := loss) (ε := ε)
      hT hS h hradial hprincipal href hcur hAux htransmission order Q hbudget.1 hbudget.2)

set_option diagnostics true in
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
  exact n06_canonicalRelative_uniform
    (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
    (K := K) (V := V) (b := b) (B := B)
    (base := base) (loss := loss) (ε := ε) hT hS h
    hgeometry.1 hgeometry.2.1 hgeometry.2.2.1 hgeometry.2.2.2.1
    hgeometry.2.2.2.2.1 hgeometry.2.2.2.2.2

end ContinuousFlexibility.Statements
