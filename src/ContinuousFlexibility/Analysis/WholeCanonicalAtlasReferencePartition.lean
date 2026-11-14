module

public import ContinuousFlexibility.Analysis.WholeCanonicalAtlasCurrentPartition
public import ContinuousFlexibility.Analysis.N04PositiveNormalizationBuffer

/-!
# The actual reference partition and buffered normalization inclusion

The old optical cut supplies the exact negative reference radii. Whole
positive components supply the remaining intervals. Their already proved
countable reference exception gives the radial null-set partition.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hfield : N04bFieldRegularity D S C L base ε)
  (e₀ : ℕ ≃ N04PieceIndex D) (e : ℕ ≃ N04WholePieceIndex D)
  (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
  (F G : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
  (Q : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
  (N : Set ℝ)

theorem n04WholeCanonicalAtlasData_actual_reference_radii (m : ℕ) :
    let W := n04WholeCanonicalAtlasData C L
      (n04bActualTypedAtlas hT hS hN hfield e₀) e cell F G Q N
    W.physicalLeft m = n04WholePieceLeft C (n04bActualReferenceCut hN) (e m) ∧
      W.physicalRight m = n04WholePieceRight C (n04bActualReferenceCut hN) (e m) := by
  cases hi : e m with
  | inl j =>
      rcases j with ⟨j, side⟩
      cases side <;> simp only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
        n04bActualTypedAtlas, n04bTypedAtlasData, n04bCanonicalOperatorData,
        n04bReferenceMetadata, n04bReferencePieces, n04bReferenceTypedLeft,
        n04bReferenceTypedRight, n04WholePieceLeft, n04WholePieceRight, hi,
        Equiv.apply_symm_apply, Bool.false_eq_true, ite_false, ite_true, and_self]
  | inr i =>
      simp only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
        n04WholePieceLeft, n04WholePieceRight, hi, and_self]

theorem n04WholeCanonicalAtlasData_actual_referencePartition :
    let W := n04WholeCanonicalAtlasData C L
      (n04bActualTypedAtlas hT hS hN hfield e₀) e cell F G Q N
    ∃ E : Set ℝ, volume E = 0 ∧ ∀ r ∈ Ioo D.a D.b \ E,
      ∃! m, r ∈ Ioo (W.physicalLeft m) (W.physicalRight m) := by
  have hD := n04b_profileGeometry_of_through03 hN
  have hf : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
  have hC : controlGeometryConditions D S C := hN.1.1.2.2.2.1
  have hcut : ∀ m, n04bActualReferenceCut hN m ∈ Ioo (C.left m) (C.right m) :=
    n04bActualReferenceCut_mem hN
  refine ⟨n04WholePieceExceptional D (n04bActualReferenceCut hN),
    (n04WholePieceExceptional_countable hD).measure_zero volume, ?_⟩
  intro r hr
  obtain ⟨i, hi, hu⟩ := n04WholePiece_cover hf hC hcut hr
  refine ⟨e.symm i, ?_, ?_⟩
  · have hrad := n04WholeCanonicalAtlasData_actual_reference_radii
      hT hS hN hfield e₀ e cell F G Q N (e.symm i)
    dsimp only
    rw [hrad.1, hrad.2, Equiv.apply_symm_apply]
    exact hi
  · intro n hn
    apply e.injective
    rw [Equiv.apply_symm_apply]
    apply hu
    have hrad := n04WholeCanonicalAtlasData_actual_reference_radii
      hT hS hN hfield e₀ e cell F G Q N n
    rwa [hrad.1, hrad.2] at hn

theorem n04PositiveNormalizationBuffer_region_subset_actualNormalization
    {U : Set ℝ} (B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) U)
    (hf : Continuous (deriv D.w)) :
    B.region ⊆ (n04bActualTypedAtlas hT hS hN hfield e₀).normalizationRegion := by
  change B.region ⊆ n04bNormalizationRegion D
  have hclosed : closure {r : ℝ | deriv D.w r < 0} ⊆ {r : ℝ | deriv D.w r ≤ 0} :=
    closure_minimal (by
      intro x hx
      change deriv D.w x ≤ 0
      exact (show deriv D.w x < 0 from hx).le) (isClosed_le hf continuous_const)
  intro r hr
  exact fun hneg => (not_le_of_gt (B.region_subset_positive hf hr).2) (hclosed hneg)

end ContinuousFlexibility.Analysis
