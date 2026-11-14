module

public import ContinuousFlexibility.Analysis.N04bReferencePieces
public import ContinuousFlexibility.Analysis.N04bRootTravelCharts

/-!
# Canonical reference metadata for arbitrary interior negative cuts

This constructor fills the reference fields from the parameterized piece
data and gives each negative pair its actual root radius. Positive
canonical intervals and all physical domains, charts and heights are
retained from the supplied data.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements

variable {D : ReferenceData} {S : PhysicalSpacesData}

def n04bReferenceMetadata (C : NonlinearGeometryData S) (cut : ℕ → ℝ)
    (e : ℕ ≃ N04PieceIndex D) (travel : ℕ → ℝ)
    (K : CanonicalData S) : CanonicalData S :=
  { K with
    physicalLeft := (n04bReferencePieces C cut e).left
    physicalRight := (n04bReferencePieces C cut e).right
    cell := (n04bReferencePieces C cut e).cell
    positive := (n04bReferencePieces C cut e).positive
    cutPair := (n04bReferencePieces C cut e).cutPair
    cutRadius := fun m => n04bRootCutRadius (travel m)
    left := fun i => match e i with
      | .inl _ => 0
      | .inr _ => K.left i
    right := fun i => match e i with
      | .inl j => n04bRootCutRadius (travel j.1)
      | .inr _ => K.right i }

/-- Every reference cut-pair field is computed by the actual metadata
constructor; in particular both physical halves meet at cut(m). -/
theorem n04bReferenceMetadata_cutPairs
    (C : NonlinearGeometryData S) (cut : ℕ → ℝ)
    (e : ℕ ≃ N04PieceIndex D) (travel : ℕ → ℝ) (K : CanonicalData S)
    (hT : ∀ m, 0 < travel m) :
    CanonicalReferenceCutPairs S C (n04bReferenceMetadata C cut e travel K) := by
  intro m
  simp [n04bReferenceMetadata, n04bReferencePieces, n04TypedPiecePositive,
    n04bReferenceTypedLeft, n04bReferenceTypedRight, n04bNegativeLeft,
    n04bNegativeRight, n04bRootCutRadius_pos (hT m)]

/-- The reference radial partition has one countable null exceptional set
and the same natural-number indexing as the future moving domains. -/
theorem n04bReferenceMetadata_referencePartition
    {C : NonlinearGeometryData S} {cut : ℕ → ℝ}
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C)
    (hcut : ∀ m, cut m ∈ Ioo (C.left m) (C.right m))
    (e : ℕ ≃ N04PieceIndex D) (travel : ℕ → ℝ) (K : CanonicalData S) :
    ∃ E : Set ℝ, volume E = 0 ∧ ∀ r ∈ Ioo D.a D.b \ E,
      ∃! i, r ∈ Ioo
        ((n04bReferenceMetadata C cut e travel K).physicalLeft i)
        ((n04bReferenceMetadata C cut e travel K).physicalRight i) := by
  obtain ⟨E, hE, hcover⟩ :=
    (n04bReferencePieces_geometry hD hC hcut e).2.2.2
  exact ⟨E, hE.measure_zero volume, hcover⟩

theorem n04bReferenceMetadata_positive_intervals
    (C : NonlinearGeometryData S) (cut : ℕ → ℝ)
    (e : ℕ ≃ N04PieceIndex D) (travel : ℕ → ℝ) (K : CanonicalData S)
    (i : N04PositivePieceIndex D) :
    (n04bReferenceMetadata C cut e travel K).left (e.symm (.inr i)) =
        K.left (e.symm (.inr i)) ∧
      (n04bReferenceMetadata C cut e travel K).right (e.symm (.inr i)) =
        K.right (e.symm (.inr i)) := by
  simp [n04bReferenceMetadata]

end ContinuousFlexibility.Analysis
