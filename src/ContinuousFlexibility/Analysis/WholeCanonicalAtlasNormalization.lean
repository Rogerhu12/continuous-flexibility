import ContinuousFlexibility.Analysis.WholeCanonicalAtlasData
import ContinuousFlexibility.Analysis.WholePositiveNormalizationGeometry

/-!
# Normalization of the single whole-component atlas

Restrict the old normalization set to the reference-only buffered set.
The negative fields are unchanged; each positive normalization point lies
in the actual identity middle for both the current and reference maps.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

theorem n04WholeCanonicalAtlasData_normalization
    {D : ReferenceData} {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (F G : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    {U : Set ℝ} (B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) U)
    {base : ℕ} {ε : ℝ} (hK : CanonicalGeometry D S C K base ε)
    (hf : Continuous (deriv D.w)) (hN : B.region ⊆ K.normalizationRegion)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε ∧
      stateSector S C.referenceState)
    (hpositive : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ i,
      WholePositiveChartGeometry (F z i) (G z i)
        (wholePositiveChartHeight (F z i) (Q z i))
        (n04PositiveLeft i) (n04PositiveRight i) (B.centerLeft i) (B.centerRight i))
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    let W := n04WholeCanonicalAtlasData C L K e cell F G Q B.region
    physicalPieceOpen S W z m ∩ (W.normalizationRegion ×ˢ univ) =
      physicalPieceOpen S W (C.referenceState, 0) m ∩ (W.normalizationRegion ×ˢ univ) ∧
    ∀ p ∈ physicalPieceOpen S W z m, p.1 ∈ W.normalizationRegion →
      W.chart z m p = W.chart (C.referenceState, 0) m p ∧
      W.height z m p = W.height (C.referenceState, 0) m p := by
  cases hi : e m with
  | inl j =>
      let k := if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1
      have hbase := hK.normalization z hz hs k
      have hprod : B.region ×ˢ (univ : Set ℝ) ⊆ K.normalizationRegion ×ˢ univ :=
        fun _ hp => ⟨hN hp.1, hp.2⟩
      have hinter : (K.normalizationRegion ×ˢ (univ : Set ℝ)) ∩
          (B.region ×ˢ univ) = B.region ×ˢ univ := inter_eq_right.mpr hprod
      have heq := congrArg (fun A : Set PolarPoint => A ∩ (B.region ×ˢ univ)) hbase.1
      have hrestricted :
          physicalPieceOpen S K z k ∩ (B.region ×ˢ univ) =
          physicalPieceOpen S K (C.referenceState, 0) k ∩ (B.region ×ˢ univ) := by
        simpa only [inter_assoc, hinter] using heq
      have hvalues : ∀ p ∈ physicalPieceOpen S K z k, p.1 ∈ B.region →
          K.chart z k p = K.chart (C.referenceState, 0) k p ∧
          K.height z k p = K.height (C.referenceState, 0) k p :=
        fun p hp hn => hbase.2 p hp (hN hn)
      simpa only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
        physicalPieceOpen, hi, k] using And.intro hrestricted hvalues
  | inr i =>
      have hvalues :
          ∀ p ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ),
          p.1 ∈ B.region →
          F z i p = F (C.referenceState, 0) i p ∧
          wholePositiveChartHeight (F z i) (Q z i) p =
            wholePositiveChartHeight (F (C.referenceState, 0) i)
              (Q (C.referenceState, 0) i) p := by
        intro p hp hn
        exact B.chart_height_normalization hf i (hpositive z hz hs i)
          (hpositive (C.referenceState, 0) href.1 href.2 i) hp hn
      have hdomain :
          (Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ)) ∩
            (B.region ×ˢ univ) =
          (Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ)) ∩
            (B.region ×ˢ univ) := rfl
      simpa only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
        physicalPieceOpen, hi] using And.intro hdomain hvalues

end ContinuousFlexibility.Analysis
