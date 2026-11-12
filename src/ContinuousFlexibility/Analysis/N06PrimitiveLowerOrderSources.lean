import ContinuousFlexibility.Analysis.N06PrimitiveScalarSources
import ContinuousFlexibility.Analysis.N06PrimitiveActualJetBounds

/-!
# Uniform lower-order source operators from the actual primitive jets

The potential multiplier and all three scalar columns are constructed in
the original source level. Their constants and one state seminorm are
chosen before the state. No common-domain or physical-equation conclusion
is used to construct these sources.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis

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

local instance n06PrimitiveLowerLevelGroup {S : PhysicalSpacesData} {K : CanonicalData S}
    (V : VolumeModelData S K) (b : ℕ) : NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedAddCommGroup _
local instance n06PrimitiveLowerLevelSpace {S : PhysicalSpacesData} {K : CanonicalData S}
    (V : VolumeModelData S K) (b : ℕ) : NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedSpace _
local instance n06PrimitiveLowerGraphGroup {S : PhysicalSpacesData} {K : CanonicalData S}
    {V : VolumeModelData S K} {b : ℕ} (B : CanonicalDomainData S K V b) :
    NormedAddCommGroup B.Space := Submodule.normedAddCommGroup _
local instance n06PrimitiveLowerGraphSpace {S : PhysicalSpacesData} {K : CanonicalData S}
    {V : VolumeModelData S K} {b : ℕ} (B : CanonicalDomainData S K V b) :
    NormedSpace ℝ B.Space := Submodule.normedSpace _

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K V b}

private def N06PrimitiveLowerInputJets
    (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (b base : ℕ) (ε : ℝ) (order : ℕ) (A Cjet : ℝ) : Prop :=
  0 < A ∧ 0 < Cjet ∧
    ∀ I : Finset ℕ, ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      N06ActualRelativeJetBounds D T S C L K b A I
        (Cjet * (stateGrading S order (z.1 - C.referenceState) + |z.2|)) z

private def N06PrimitiveLowerStateSources
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (K : CanonicalData S)
    (V : VolumeModelData S K) (b : ℕ) (B : CanonicalDomainData S K V b)
    (Qp Qcol ρ : ℝ) (z : AnnularState S × ℝ) : Prop :=
  ∃ Mp : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
    ∃ columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b,
      ‖Mp‖ ≤ Qp * ρ ∧ (∀ i, ‖columns i‖ ≤ Qcol * ρ) ∧
      (∀ F m,
        (V.forget (3 / 4 : ℝ) 0 b (Mp F) m : PolarPoint → ℝ)
          =ᵐ[canonicalMeasure S K m] fun p =>
            (if K.positive m then (-1 : ℝ) else 1) *
              (K.potential z m p - K.potential (C.referenceState, 0) m p) *
                (B.inverse F).val.1.1 m p) ∧
      ∀ i m,
        (V.forget (3 / 4 : ℝ) 0 b (columns i) m : PolarPoint → ℝ)
          =ᵐ[canonicalMeasure S K m]
            n06ActualCanonicalColumnDifference D S C L K z i m

private def N06PrimitiveLowerSourceFamily
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (K : CanonicalData S)
    (V : VolumeModelData S K) (b : ℕ) (B : CanonicalDomainData S K V b)
    (base : ℕ) (ε : ℝ) (order : ℕ) (Qp Qcol : ℝ) : Prop :=
  0 ≤ Qp ∧ 0 ≤ Qcol ∧
    ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      N06PrimitiveLowerStateSources D S C L K V b B Qp Qcol
        (stateGrading S order (z.1 - C.referenceState) + |z.2|) z

private def N06PrimitiveLowerPotentialFamily
    (T : MaterialData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (V : VolumeModelData S K) (b : ℕ)
    (B : CanonicalDomainData S K V b) (base : ℕ) (ε A Q : ℝ) : Prop :=
  0 ≤ Q ∧ ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∀ δ : ℝ, 0 ≤ δ →
    (∀ m j, j ≤ b → ∀ p ∈ canonicalOpen S K m,
      |mixedDerivative 0 j
        (fun q => K.potential z m q - K.potential (C.referenceState, 0) m q) p| ≤
        δ * T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (K.cell m)) ^ A) →
    ∃ P : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
      ‖P‖ ≤ Q * δ ∧ ∀ F m,
      (V.forget (3 / 4 : ℝ) 0 b (P F) m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        fun p => (if K.positive m then (-1 : ℝ) else 1) *
          (K.potential z m p - K.potential (C.referenceState, 0) m p) *
            (B.inverse F).val.1.1 m p

private theorem n06_primitive_lower_potential_input
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε) (A : ℝ) :
    ∃ P : ℝ, N06PrimitiveLowerPotentialFamily T S C K V b B base ε A P :=
  n06N05_primitiveActualSignedPotentialDifference_multiplier hT hS h A

private theorem n06_primitive_lower_fixed_state
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    {A P Cjet ρ : ℝ} (hCjet : 0 < Cjet) (hρ : 0 ≤ ρ)
    (hpotential : N06PrimitiveLowerPotentialFamily T S C K V b B base ε A P)
    (I : Finset ℕ) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hzero : ∀ i : Fin 3, ∀ m, m ∉ I → ∀ p ∈ canonicalOpen S K m,
      n06ActualCanonicalColumnDifference D S C L K z i m p = 0)
    (hj : N06ActualRelativeJetBounds D T S C L K b A I (Cjet * ρ) z) :
    N06PrimitiveLowerStateSources D S C L K V b B (P * Cjet)
      ((n06WeakAngularMultiplierCost b * n06FiniteSourceCost T S K (3 / 4 : ℝ) 0 b I) * Cjet)
      ρ z := by
  have hδ : 0 ≤ Cjet * ρ := mul_nonneg hCjet.le hρ
  obtain ⟨Mp, hMp, hMpfield⟩ := hpotential.2 z hz hs (Cjet * ρ) hδ hj.potential
  obtain ⟨columns, hcolumns, hcolumnnorm⟩ := n06_primitiveActual_columnDifferences_sources
    (B := B) hT hS h hz hs I hzero hδ hj.columns
  refine ⟨Mp, columns, hMp.trans_eq (mul_assoc P Cjet ρ).symm, ?_, hMpfield, hcolumns⟩
  intro i
  exact (hcolumnnorm i).trans_eq
    (mul_assoc (n06WeakAngularMultiplierCost b *
      n06FiniteSourceCost T S K (3 / 4 : ℝ) 0 b I) Cjet ρ).symm

private theorem n06_primitive_lower_fixed_family
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    {order : ℕ} {A Cjet P : ℝ}
    (hjets : N06PrimitiveLowerInputJets D T S C L K b base ε order A Cjet)
    (hpotential : N06PrimitiveLowerPotentialFamily T S C K V b B base ε A P)
    (I : Finset ℕ)
    (hI : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ i : Fin 3, ∀ m, m ∉ I → ∀ p ∈ canonicalOpen S K m,
        n06ActualCanonicalColumnDifference D S C L K z i m p = 0) :
    N06PrimitiveLowerSourceFamily D S C L K V b B base ε order (P * Cjet)
      ((n06WeakAngularMultiplierCost b * n06FiniteSourceCost T S K (3 / 4 : ℝ) 0 b I) * Cjet) := by
  have hCcol : 0 ≤ n06WeakAngularMultiplierCost b *
      n06FiniteSourceCost T S K (3 / 4 : ℝ) 0 b I :=
    mul_nonneg (n06WeakAngularMultiplierCost_nonneg b)
      (n06FiniteSourceCost_nonneg T S K (3 / 4 : ℝ) 0 b I)
  refine ⟨mul_nonneg hpotential.1 hjets.2.1.le, mul_nonneg hCcol hjets.2.1.le,
    fun z hz hs => ?_⟩
  exact n06_primitive_lower_fixed_state (B := B) hT hS h hjets.2.1
    (add_nonneg (apply_nonneg (stateGrading S order) (z.1 - C.referenceState))
      (abs_nonneg z.2)) hpotential I hz hs (hI z hz hs) (hjets.2.2 I z hz hs)

private theorem n06_primitive_lower_family_of_jets
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    {order : ℕ} {A Cjet : ℝ}
    (hjets : N06PrimitiveLowerInputJets D T S C L K b base ε order A Cjet) :
    ∃ Qp Qcol : ℝ, N06PrimitiveLowerSourceFamily D S C L K V b B base ε order Qp Qcol := by
  exact (n06_primitiveActual_columnDifferences_finiteSupport hT hS h href).elim
    (fun I hI => (n06_primitive_lower_potential_input (B := B) hT hS h A).elim
      (fun P hp => ⟨P * Cjet,
        (n06WeakAngularMultiplierCost b * n06FiniteSourceCost T S K (3 / 4 : ℝ) 0 b I) * Cjet,
        n06_primitive_lower_fixed_family (B := B) hT hS h hjets hp I hI⟩))

private theorem n06_primitive_lower_bind_orders
    {I X Y U W : Type*} (P : I → X → Y → Prop) (Q : I → U → W → Prop)
    (h : ∃ n, ∃ x y, P n x y)
    (hmap : ∀ n x y, P n x y → ∃ u w, Q n u w) :
    ∃ n, ∃ u w, Q n u w :=
  h.elim (fun n hn => hn.elim (fun x hx => hx.elim (fun y hy =>
    (hmap n x y hy).elim (fun u hu => hu.elim (fun w hw => ⟨n, u, w, hw⟩)))))

theorem n06_primitiveActual_lowerOrder_sources
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {V : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
    {B : CanonicalDomainData S K V b}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε) :
    ∃ order : ℕ, ∃ Qp Qcol : ℝ, 0 ≤ Qp ∧ 0 ≤ Qcol ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        ∃ Mp : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
        ∃ columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b,
          ‖Mp‖ ≤ Qp * (stateGrading S order (z.1 - C.referenceState) + |z.2|) ∧
          (∀ i, ‖columns i‖ ≤
            Qcol * (stateGrading S order (z.1 - C.referenceState) + |z.2|)) ∧
          (∀ F m,
            (V.forget (3 / 4 : ℝ) 0 b (Mp F) m : PolarPoint → ℝ)
              =ᵐ[canonicalMeasure S K m] fun p =>
                (if K.positive m then (-1 : ℝ) else 1) *
                  (K.potential z m p - K.potential (C.referenceState, 0) m p) *
                    (B.inverse F).val.1.1 m p) ∧
          ∀ i m,
            (V.forget (3 / 4 : ℝ) 0 b (columns i) m : PolarPoint → ℝ)
              =ᵐ[canonicalMeasure S K m]
                n06ActualCanonicalColumnDifference D S C L K z i m := by
  exact n06_primitive_lower_bind_orders
    (N06PrimitiveLowerInputJets D T S C L K b base ε)
    (N06PrimitiveLowerSourceFamily D S C L K V b B base ε)
    (n06_exists_actualRelativeJetBounds_of_primitive hT hS
      h.1.1.1.1 h.1.1.2 h.1.2.2.2.2.1 href hcur b)
    (fun order A Cjet hjets => n06_primitive_lower_family_of_jets
      (B := B) (order := order) (A := A) (Cjet := Cjet) hT hS h href hjets)

end ContinuousFlexibility.Statements
