module

public import ContinuousFlexibility.Analysis.N06ActualRelativeJetBounds
public import ContinuousFlexibility.Analysis.N06PrimitiveFiniteSupport
public import ContinuousFlexibility.Analysis.N06LeftColumnSources
public import ContinuousFlexibility.Analysis.N06ActualPotentialMultiplier
public import ContinuousFlexibility.Analysis.N06FiniteLocalSourceColumns

/-!
# Actual scalar and potential differences on the retained N05 graph

All columns are the original transformed physical fields. Primitive
reference jets provide their finite common support envelope; their
ordinary angular jet bounds then construct sources in the same level.
The signed potential multiplier uses the actual reference inverse.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K V b}

theorem n06_primitiveActual_scalarFields_commonSupport
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε) :
    ∃ J : Set ℝ, IsCompact J ∧ J ⊆ radialCore D ∧
      ∀ z : AnnularState S × ℝ, ∀ i : Fin 3, ∀ r, r ∉ J → ∀ θ,
        n06CurrentScalarField D S C L z i (r, θ) = 0 := by
  obtain ⟨Jχ, hJχ, hχD, _, hχzero⟩ :=
    n06_currentLeftColumns_commonSupport (L := L) hS
  obtain ⟨hJν, hνD, hνzero⟩ := n06_nuColumns_common_radialSupport hT hS h01
  obtain ⟨Jψ, hJψ, hψD, hψzero⟩ := hS.2.2.2.2.2.2.2.2.1
  refine ⟨(Jχ ∪ tsupport D.chi) ∪ Jψ, (hJχ.union hJν).union hJψ, ?_, ?_⟩
  · intro r hr
    rcases hr with (hr | hr) | hr
    · exact hχD hr
    · exact hνD hr
    · exact hψD hr
  · intro z i r hr θ
    have hrχ : r ∉ Jχ := fun h => hr (Or.inl (Or.inl h))
    have hrν : r ∉ tsupport D.chi := fun h => hr (Or.inl (Or.inr h))
    have hrψ : r ∉ Jψ := fun h => hr (Or.inr h)
    fin_cases i
    · exact hχzero z r hrχ θ
    · exact hνzero z r hrν θ
    · exact hψzero r hrψ θ

/-- The finite envelope is selected before the state. Moving cuts are
included by their actual original negative components. -/
theorem n06_primitiveActual_columnDifferences_finiteSupport
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hjets : CanonicalGeometry.ReferenceJets D T S C L K) :
    ∃ I : Finset ℕ, ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ i : Fin 3, ∀ m, m ∉ I → ∀ p ∈ canonicalOpen S K m,
        n06ActualCanonicalColumnDifference D S C L K z i m p = 0 := by
  classical
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  obtain ⟨Jc, hJc, hJcD, hcurrent⟩ :=
    n06_primitiveActual_scalarFields_commonSupport (L := L) hT hS h01
  obtain ⟨Jr, hJr, hJrD, hreference⟩ :=
    n06_referenceScalarFields_commonSupport hS h01.1.2.2.2.1
  let J : Set ℝ := Jc ∪ Jr
  have hJ : IsCompact J := hJc.union hJr
  have hJD : J ⊆ radialCore D := fun _ hr =>
    hr.elim (fun hc => hJcD hc) (fun hr => hJrD hr)
  have hfinite := n06_cutSaturatedSupport_finite_of_primitive h01.1.1 hT h01.2.2.2.1 h04 hjets hJ hJD
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hsref := n05_referenceState_sector h01.2.2.1
  refine ⟨hfinite.toFinset, ?_⟩
  intro z hz hs i m hm p hp
  have hmiss (w : AnnularState S × ℝ)
      (hw : w ∈ stateNeighborhood S C base ε) (hws : stateSector S w.1) :
      m ∉ n06PhysicalSupportPieces K w J := by
    intro hmeet
    exact hm (hfinite.mem_toFinset.mpr
      (n06_physicalSupportPieces_subset_cutSaturatedSupport h01.2.2.2.1 h04 hw hws J hmeet))
  have hcur := n06_canonicalTransforms_zero_off_physicalSupport h04 hz hs
    (J := J) (φ := n06CurrentScalarField D S C L z i)
    (fun r hr θ => hcurrent z i r (fun hc => hr (Or.inl hc)) θ)
    (hmiss z hz hs)
  have hrefzero := n06_canonicalTransforms_zero_off_physicalSupport h04 href hsref
    (J := J) (φ := n06ReferenceScalarField D S i)
    (fun r hr θ => hreference i r (fun hr' => hr (Or.inr hr')) θ)
    (hmiss (C.referenceState, 0) href hsref)
  change canonicalSource S K z m (n06CurrentScalarField D S C L z i) p -
    canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S i) p = 0
  rw [hcur.2 hp, hrefzero.2 hp, sub_self]

theorem n06_primitiveActual_columnDifference_regular
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (i : Fin 3) (m : ℕ) :
    ContDiffOn ℝ ∞ (n06ActualCanonicalColumnDifference D S C L K z i m)
      (canonicalOpen S K m) ∧
    (∀ p ∈ canonicalOpen S K m,
      n06ActualCanonicalColumnDifference D S C L K z i m (p + (0, Real.pi)) =
        n06ActualCanonicalColumnDifference D S C L K z i m p) ∧
    (∀ p ∈ canonicalOpen S K m,
      n06ActualCanonicalColumnDifference D S C L K z i m (p.1, Real.pi - p.2) =
        n06ActualCanonicalColumnDifference D S C L K z i m p) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h03 : N03Properties D T S C R L base ε := h.1.1.2
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hsref := n05_referenceState_sector h01.2.2.1
  have heven : ∀ p : PolarPoint,
      n06CurrentScalarField D S C L z i (p.1, -p.2) =
        n06CurrentScalarField D S C L z i p := by
    fin_cases i
    · exact n06_currentLeftColumn_even hT hS h01 h03 hz hs
    · exact n06_nuColumn_even hT hS h01 z
    · exact fun p => ((hS.1 (3 / 4 : ℝ)).2.2.2.1 S.psi).2.1 p.1 p.2
  refine ⟨(n06_canonicalSource_contDiffOn h04.1 hz hs
    (n06_currentScalarField_contDiff hT hS h01 h03 hz hs i).contDiffOn m).sub
      (n06_canonicalSource_contDiffOn h04.1 href hsref
        (n06_referenceScalarField_contDiff h01.1.1 hT hS h01.1.2.2.2.1 i).contDiffOn m),
    ?_, ?_⟩
  · intro p hp
    exact congrArg₂ (fun x y : ℝ => x - y)
      (n06_canonicalSource_periodicOn h04.1 hz hs
        (fun q _ => n06_currentScalarField_periodic hT hS h01 h03 hz hs i q) m hp)
      (n06_canonicalSource_periodicOn h04.1 href hsref
        (fun q _ => n06_referenceScalarField_periodic hS i q) m hp)
  · intro p hp
    exact congrArg₂ (fun x y : ℝ => x - y)
      (n06_canonicalSource_reflectionOn h04.1 hz hs
        (fun q _ => n06_currentScalarField_periodic hT hS h01 h03 hz hs i q)
        (fun q _ => heven q) m hp)
      (n06_canonicalSource_reflectionOn h04.1 href hsref
        (fun q _ => n06_referenceScalarField_periodic hS i q)
        (fun q _ => n06_referenceScalarField_even hS i q) m hp)

theorem n06_primitiveActual_columnDifferences_sources
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (I : Finset ℕ)
    (hzero : ∀ i : Fin 3, ∀ m, m ∉ I → ∀ p ∈ canonicalOpen S K m,
      n06ActualCanonicalColumnDifference D S C L K z i m p = 0)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hjets : ∀ i : Fin 3, ∀ m ∈ I, ∀ j, j ≤ b → ∀ p ∈ canonicalOpen S K m,
      |mixedDerivative 0 j (n06ActualCanonicalColumnDifference D S C L K z i m) p| ≤ δ) :
    ∃ columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b,
      (∀ i m, (V.forget (3 / 4 : ℝ) 0 b (columns i) m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m] n06ActualCanonicalColumnDifference D S C L K z i m) ∧
      ∀ i, ‖columns i‖ ≤
        (n06WeakAngularMultiplierCost b * n06FiniteSourceCost T S K (3 / 4 : ℝ) 0 b I) * δ := by
  classical
  have hex (i : Fin 3) := n06Volume_exists_finite_local_source h.1.1.1.1.1.1 hT h.2.2.1
    (3 / 4 : ℝ) 0 b I (n06ActualCanonicalColumnDifference D S C L K z i)
    (fun m => (n06_primitiveActual_columnDifference_regular hT hS h hz hs i m).1)
    (fun m => (n06_primitiveActual_columnDifference_regular hT hS h hz hs i m).2.1)
    (fun m => (n06_primitiveActual_columnDifference_regular hT hS h hz hs i m).2.2)
    (hzero i) hδ (hjets i)
  choose columns hcolumns hnorm using hex
  exact ⟨columns, hcolumns, hnorm⟩

/-- The sign belongs to the actual canonical operator: positive pieces
contribute minus the potential difference, negative pieces contribute plus. -/
theorem n06N05_primitiveActualSignedPotentialDifference_multiplier
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε) (A : ℝ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
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
              (B.inverse F).val.1.1 m p := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h03 : N03Properties D T S C R L base ε := h.1.1.2
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hsref := n05_referenceState_sector h01.2.2.1
  obtain ⟨Q, hQ, hmult⟩ := n06N05_potentialMultiplier h01.1.1 hT h.2 A
  refine ⟨Q, hQ, ?_⟩
  intro z hz hs δ hδ hsmall
  apply hmult δ hδ (fun m p => (if K.positive m then (-1 : ℝ) else 1) *
    (K.potential z m p - K.potential (C.referenceState, 0) m p))
  · intro m
    exact contDiffOn_const.mul
      ((n06_canonicalPotential_contDiffOn hT hS h01 h03 h04 hz hs m).sub
        (n06_canonicalPotential_contDiffOn hT hS h01 h03 h04 href hsref m))
  · intro m p hp
    rw [n06_canonicalPotential_periodicOn hT hS h03 h04 hz hs m hp,
      n06_canonicalPotential_periodicOn hT hS h03 h04 href hsref m hp]
  · intro m p hp
    rw [n06_canonicalPotential_reflectionOn hT hS h03 h04 hz hs m hp,
      n06_canonicalPotential_reflectionOn hT hS h03 h04 href hsref m hp]
  · intro m j hj p hp
    rw [spaces_mixedDerivative_const_mul, abs_mul]
    have hsign : |(if K.positive m then (-1 : ℝ) else 1)| = 1 := by
      split <;> norm_num
    rw [hsign, one_mul]
    exact hsmall m j hj p hp

end ContinuousFlexibility.Statements
