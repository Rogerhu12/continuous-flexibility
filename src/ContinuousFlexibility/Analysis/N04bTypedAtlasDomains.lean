import ContinuousFlexibility.Analysis.N04bTypedAtlasData

/-!
# Domain and normalization fields of the concrete typed atlas

All reference metadata are the optical-cut metadata, and every current
domain is the actual travel half or fixed positive subdivision. These
proofs are independent of the later choice of negative chart extensions.
The chart normalization follows because every negative piece misses the
normalization region and every positive chart and height is fixed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
  (e : ℕ ≃ N04PieceIndex D)
  (F : (AnnularState S × ℝ) → ℕ → Bool → PolarPoint → PolarPoint)
  (h : (AnnularState S × ℝ) → ℕ → Bool → PolarPoint → ℝ)
  (J : (AnnularState S × ℝ) → ℕ → Bool → PolarPoint → PolarPoint)

theorem n04bTypedAtlasData_normalization
    (hC : controlGeometryConditions D S C) (cut : ℕ → ℝ)
    (z : AnnularState S × ℝ) (m : ℕ) :
    let K := n04bTypedAtlasData D S C L cut e F h J
    physicalPieceOpen S K z m ∩ (K.normalizationRegion ×ˢ univ) =
      physicalPieceOpen S K (C.referenceState, 0) m ∩ (K.normalizationRegion ×ˢ univ) ∧
    ∀ p ∈ physicalPieceOpen S K z m, p.1 ∈ K.normalizationRegion →
      K.chart z m p = K.chart (C.referenceState, 0) m p ∧
      K.height z m p = K.height (C.referenceState, 0) m p := by
  constructor
  · exact n04b_typed_normalization_inter hC
      (n04bActualTravelChart S C L z)
      (n04bActualTravelChart S C L (C.referenceState, 0)) (e m)
  · intro p hp hn
    change p.1 ∈ n04bNormalizationRegion D at hn
    cases hi : e m with
    | inl i =>
      have hp' : p ∈ n04bTypedPhysicalDomain C (n04bActualTravelChart S C L z) (.inl i) := by
        simpa only [n04bTypedAtlasData_physicalPieceOpen, hi] using hp
      exact (n04b_not_mem_normalizationRegion_of_negative
        (n04b_typed_domain_negative hC (.inl i) rfl hp') hn).elim
    | inr i =>
      simp only [n04bTypedAtlasData_chart, n04bTypedAtlasData_height, hi,
        n04bTypedAtlasChart, n04bTypedAtlasHeight, and_self]

theorem n04bTypedAtlasData_referenceBounds
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C)
    (cut : ℕ → ℝ) (hcut : ∀ m, cut m ∈ Ioo (C.left m) (C.right m)) (m : ℕ) :
    let K := n04bTypedAtlasData D S C L cut e F h J
    K.physicalLeft m < K.physicalRight m ∧ K.left m < K.right m ∧
      Ioo (K.physicalLeft m) (K.physicalRight m) ⊆ Ioo D.a D.b := by
  have hb := (n04bReferencePieces_geometry hD hC hcut e).1 m
  refine ⟨hb.2.1, ?_, ?_⟩
  · rw [n04bTypedAtlasData_left, n04bTypedAtlasData_right]
    cases hi : e m with
    | inl i =>
      exact n04bRootCutRadius_pos (n04b_referenceTravel_pos hD hC i.1)
    | inr i => exact zero_lt_one
  · intro r hr
    exact ⟨hb.1.trans hr.1, hr.2.trans hb.2.2⟩

theorem n04bTypedAtlasData_referencePositive
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C)
    (cut : ℕ → ℝ) (hcut : ∀ m, cut m ∈ Ioo (C.left m) (C.right m)) :
    let K := n04bTypedAtlasData D S C L cut e F h J
    ∀ m, K.positive m = true →
      ∀ r ∈ Ioo (K.physicalLeft m) (K.physicalRight m), 0 < deriv D.w r :=
  (n04bReferencePieces_geometry hD hC hcut e).2.1

theorem n04bTypedAtlasData_referenceNegative
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C)
    (cut : ℕ → ℝ) (hcut : ∀ m, cut m ∈ Ioo (C.left m) (C.right m)) :
    let K := n04bTypedAtlasData D S C L cut e F h J
    ∀ m, K.positive m = false →
      ∀ r ∈ Ioo (K.physicalLeft m) (K.physicalRight m), deriv D.w r < 0 :=
  (n04bReferencePieces_geometry hD hC hcut e).2.2.1

theorem n04bTypedAtlasData_referencePartition
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C)
    (cut : ℕ → ℝ) (hcut : ∀ m, cut m ∈ Ioo (C.left m) (C.right m)) :
    let K := n04bTypedAtlasData D S C L cut e F h J
    ∃ E : Set ℝ, volume E = 0 ∧ ∀ r ∈ Ioo D.a D.b \ E,
      ∃! m, r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) := by
  obtain ⟨E, hE, hcover⟩ := (n04bReferencePieces_geometry hD hC hcut e).2.2.2
  exact ⟨E, hE.measure_zero volume, hcover⟩

/-- The reference domains are proved from the actual reference flow;
the radial endpoint fields merely record their optical-cut intervals. -/
theorem n04bTypedAtlasData_referenceDomain
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C)
    (href : referenceStateConditions D S C)
    {base : ℕ} {ε : ℝ} (hfield : N04bFieldRegularity D S C L base ε) (m : ℕ) :
    let K := n04bTypedAtlasData D S C L (n04bReferenceTravelCut hD hC) e F h J
    physicalPieceOpen S K (C.referenceState, 0) m = referencePhysicalPieceOpen S K m :=
  n04b_reference_typed_domain hD hC href hfield (e m)

theorem n04bTypedAtlasData_domains
    {T : MaterialData} {R : ReturnEquationData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    let K := n04bTypedAtlasData D S C L (n04bReferenceTravelCut hD hC) e F h J
    let Ω := physicalPieceOpen S K z m
    IsOpen Ω ∧ Ω.Nonempty ∧ Ω ⊆ annularOpen D ∧
      (∀ p : PolarPoint, p + (0, Real.pi) ∈ Ω ↔ p ∈ Ω) ∧
      (∀ p : PolarPoint, (p.1, -p.2) ∈ Ω ↔ p ∈ Ω) ∧
      (K.positive m = true → Ω = referencePhysicalPieceOpen S K m) ∧
      (∀ p ∈ Ω, K.positive m = true → 0 < deriv D.w p.1) ∧
      (∀ p ∈ Ω, K.positive m = false → deriv D.w p.1 < 0) := by
  obtain ⟨hopen, hne, ha, hp, hr, hfixed, hpos, hneg⟩ :=
    n04b_actual_typed_domain_fields hT hS h03 hfield hz hs (e m)
  refine ⟨hopen, hne, ha, hp, hr, ?_, hpos, hneg⟩
  intro hpositive
  exact (hfixed hpositive).trans
    (n04b_reference_typed_domain hD hC h03.1.1.2.2.1 hfield (e m))

theorem n04bTypedAtlasData_partition
    {T : MaterialData} {R : ReturnEquationData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (cut : ℕ → ℝ) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) :
    let K := n04bTypedAtlasData D S C L cut e F h J
    ∃ E : Set PolarPoint, volume E = 0 ∧ ∀ p ∈ annularOpen D \ E,
      ∃! m, p ∈ physicalPieceOpen S K z m :=
  n04b_actual_enumerated_domain_partition hT hS h03 hfield hz hs e

/-- Both negative indices and their canonical radius are those of the
same actual reference metadata constructor. -/
theorem n04bTypedAtlasData_referenceCutPairs
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C)
    (cut : ℕ → ℝ) :
    CanonicalReferenceCutPairs S C (n04bTypedAtlasData D S C L cut e F h J) :=
  n04bReferenceMetadata_cutPairs C cut e C.travel
    (n04CanonicalAtlas D S C L (n04bReferencePieces C cut e))
    (n04b_referenceTravel_pos hD hC)

end ContinuousFlexibility.Analysis
