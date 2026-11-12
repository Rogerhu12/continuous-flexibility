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
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h03 : N03Properties D T S C R L base ε := h.1.1.2
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  obtain ⟨order, A, Cjet, _, hCjet, hjets⟩ :=
    n06_exists_actualRelativeJetBounds_of_primitive hT hS h01 h03 h04 href hcur b
  obtain ⟨I, hI⟩ := n06_primitiveActual_columnDifferences_finiteSupport hT hS h href
  obtain ⟨P, hP, hpotential⟩ :=
    n06N05_primitiveActualSignedPotentialDifference_multiplier hT hS h A
  let Ccol := n06WeakAngularMultiplierCost b *
    n06FiniteSourceCost T S K (3 / 4 : ℝ) 0 b I
  have hCcol : 0 ≤ Ccol := mul_nonneg (n06WeakAngularMultiplierCost_nonneg b)
    (n06FiniteSourceCost_nonneg T S K (3 / 4 : ℝ) 0 b I)
  refine ⟨order, P * Cjet, Ccol * Cjet,
    mul_nonneg hP hCjet.le, mul_nonneg hCcol hCjet.le, ?_⟩
  intro z hz hs
  let ρ := stateGrading S order (z.1 - C.referenceState) + |z.2|
  have hρ : 0 ≤ ρ := add_nonneg (apply_nonneg _ _) (abs_nonneg _)
  have hδ : 0 ≤ Cjet * ρ := mul_nonneg hCjet.le hρ
  have hj := hjets I z hz hs
  obtain ⟨Mp, hMp, hMpfield⟩ := hpotential z hz hs (Cjet * ρ) hδ hj.potential
  obtain ⟨columns, hcolumns, hcolumnnorm⟩ := n06_primitiveActual_columnDifferences_sources
    hT hS h hz hs I (hI z hz hs) hδ hj.columns
  refine ⟨Mp, columns, ?_, ?_, hMpfield, hcolumns⟩
  · exact hMp.trans_eq (by dsimp only [ρ]; ring)
  · intro i
    exact (hcolumnnorm i).trans_eq (by dsimp only [Ccol, ρ]; ring)

end ContinuousFlexibility.Statements
