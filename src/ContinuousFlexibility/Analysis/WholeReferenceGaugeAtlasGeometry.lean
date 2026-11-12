import ContinuousFlexibility.Analysis.WholeReferenceGaugeAtlasData

/-!
# Geometry of the same atlas after the fixed reference gauge

The physical domains, partitions and normalization set remain those of
the already constructed whole atlas. The positive reference range
certificate composes with the actual relative maps. Normalization follows
from the original equality of the current and reference relative fields,
so the fixed reference map is not required to be the identity there.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem PositiveChartRangeGeometry.open_fields
    {F G : PolarPoint → PolarPoint} {h : PolarPoint → ℝ} {l r u v : ℝ}
    (H : PositiveChartRangeGeometry F G h l r u v) :
    MapsTo F (Ioo l r ×ˢ (univ : Set ℝ)) (Ioo u v ×ˢ (univ : Set ℝ)) ∧
    MapsTo G (Ioo u v ×ˢ (univ : Set ℝ)) (Ioo l r ×ˢ (univ : Set ℝ)) ∧
    (∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ), G (F p) = p) ∧
    (∀ p ∈ Ioo u v ×ˢ (univ : Set ℝ), F (G p) = p) ∧
    ContDiffOn ℝ ∞ F (Ioo l r ×ˢ (univ : Set ℝ)) ∧
    ContDiffOn ℝ ∞ G (Ioo u v ×ˢ (univ : Set ℝ)) ∧
    ContDiffOn ℝ ∞ h (Ioo l r ×ˢ (univ : Set ℝ)) ∧
    (∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ),
      0 < h p ∧ planeJacobian F p ≠ 0 ∧
      F (p + (0, Real.pi)) = F p + (0, Real.pi) ∧ h (p + (0, Real.pi)) = h p) :=
  ⟨H.maps_open, H.inverse_maps_open, fun p _ => H.left_inverse p,
    fun p _ => H.right_inverse p, H.chart_smooth.contDiffOn,
    H.inverse_smooth.contDiffOn, H.height_smooth.contDiffOn,
    fun p _ => ⟨H.height_positive p, (H.jacobian_positive p).ne',
      H.period_add p, H.height_period p⟩⟩

theorem n04WholeReferenceGaugeAtlasData_geometry
    {D : ReferenceData} {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (ψ χ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (h₀ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (τ σ : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (N : Set ℝ) {base : ℕ} {ε : ℝ}
    (hW : CanonicalGeometry D S C
      (n04WholeCanonicalAtlasData C L K e cell σ τ Q N) base ε)
    (hreference : ∀ i, PositiveChartRangeGeometry (ψ i) (χ i) (h₀ i)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1)
    {c d : N04PositiveComponent D.a D.b (deriv D.w) → ℝ}
    (hrelative : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ i,
      WholePositiveChartGeometry (σ z i) (τ z i) (wholePositiveChartHeight (σ z i) (Q z i))
        (n04PositiveLeft i) (n04PositiveRight i) (c i) (d i)) :
    CanonicalGeometry D S C
      (n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N) base ε := by
  have hpositive (z : AnnularState S × ℝ) (hz : z ∈ stateNeighborhood S C base ε)
      (hs : stateSector S z.1) (i : N04PositiveComponent D.a D.b (deriv D.w)) :
      PositiveChartRangeGeometry
        (wholePositiveReferenceGaugeChart (ψ i) (σ z i))
        (wholePositiveReferenceGaugeInverse (τ z i) (χ i))
        (wholePositiveReferenceGaugeHeight (h₀ i) (σ z i) (Q z i))
        (n04PositiveLeft i) (n04PositiveRight i) 0 1 :=
    wholePositiveReferenceGauge_geometry (hreference i) (hrelative z hz hs i)
  refine {
    normalizationOpen := hW.normalizationOpen
    normalizationSupport := hW.normalizationSupport
    normalization := ?_
    referenceBounds := ?_
    referencePositive := hW.referencePositive
    referenceNegative := hW.referenceNegative
    referencePartition := hW.referencePartition
    referenceDomain := hW.referenceDomain
    domains := hW.domains
    partition := hW.partition
    charts := ?_
    boundary := ?_
    reflection := ?_
    inverseReflection := ?_ }
  · intro z hz hs m
    have hn := hW.normalization z hz hs m
    refine ⟨hn.1, ?_⟩
    intro p hp hpn
    have hv := hn.2 p hp hpn
    cases hi : e m with
    | inl j =>
        simpa only [n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, hi] using hv
    | inr i =>
        have hσ : σ z i p = σ (C.referenceState, 0) i p := by
          simpa only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision, hi] using hv.1
        have hh : wholePositiveChartHeight (σ z i) (Q z i) p =
            wholePositiveChartHeight (σ (C.referenceState, 0) i)
              (Q (C.referenceState, 0) i) p := by
          simpa only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision, hi] using hv.2
        have hF : wholePositiveReferenceGaugeChart (ψ i) (σ z i) p =
            wholePositiveReferenceGaugeChart (ψ i) (σ (C.referenceState, 0) i) p :=
          congrArg (ψ i) hσ
        have hH : wholePositiveReferenceGaugeHeight (h₀ i) (σ z i) (Q z i) p =
            wholePositiveReferenceGaugeHeight (h₀ i) (σ (C.referenceState, 0) i)
              (Q (C.referenceState, 0) i) p := by
          simp only [wholePositiveReferenceGaugeHeight, hσ, hh]
        simpa only [n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, hi] using And.intro hF hH
  · intro m
    have hb := hW.referenceBounds m
    refine ⟨hb.1, ?_, hb.2.2⟩
    cases hi : e m with
    | inl j =>
        simpa only [n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, hi] using hb.2.1
    | inr i =>
        simp only [n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, hi, zero_lt_one]
  · intro z hz hs m
    cases hi : e m with
    | inl j =>
        simpa only [n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, physicalPieceOpen, canonicalOpen, hi] using
          hW.charts z hz hs m
    | inr i =>
        simpa only [n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, physicalPieceOpen, canonicalOpen, hi] using
          (hpositive z hz hs i).open_fields
  · intro z hz hs m
    cases hi : e m with
    | inl j =>
        simpa only [n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, physicalPieceOpen, physicalPieceClosed, canonicalClosed,
          canonicalOpen, hi] using hW.boundary z hz hs m
    | inr i =>
        have hbounds := (hW.referenceBounds m).1
        have hlr : n04PositiveLeft i < n04PositiveRight i := by
          simpa only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision, hi] using hbounds
        simpa only [n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, physicalPieceOpen, physicalPieceClosed, canonicalClosed,
          hi] using (hpositive z hz hs i).boundary_fields hlr
  · intro z hz hs m
    cases hi : e m with
    | inl j =>
        simpa only [n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, physicalPieceOpen, hi] using hW.reflection z hz hs m
    | inr i =>
        intro p hp
        simpa only [n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, hi] using And.intro ((hpositive z hz hs i).reflect p)
            ⟨(hpositive z hz hs i).height_even p, (hpositive z hz hs i).jacobian_even p⟩
  · intro z hz hs m
    cases hi : e m with
    | inl j =>
        simpa only [n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, canonicalOpen, hi] using hW.inverseReflection z hz hs m
    | inr i =>
        intro p hp
        simpa only [n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, hi] using (hpositive z hz hs i).inverse_reflect p

end ContinuousFlexibility.Analysis
