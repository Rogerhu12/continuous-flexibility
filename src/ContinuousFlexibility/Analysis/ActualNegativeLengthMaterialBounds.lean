import ContinuousFlexibility.Analysis.ActualNegativeLengthRadialBounds
import ContinuousFlexibility.Analysis.MaterialPointRadialPolynomial
import ContinuousFlexibility.Analysis.ActualNegativeMaterialSamples

/-!
# Actual negative length costs at the stored atlas sample

The optical half midpoint belongs to the original return-margin host.
Its actual pointwise material model first absorbs that host's radial
power. The proved full-component comparison then transfers the cost to
the original cell sample stored by this very half of the typed atlas.
No equality or uniqueness of the two host cells is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

theorem n04bActualTypedAtlas_negative_length_material_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ k m side, e k = .inl (m, side) →
      (K.physicalRight k - K.physicalLeft k)⁻¹ ≤ B * T.E0 (T.sample (K.cell k)) ^ A ∧
      K.physicalRight k - K.physicalLeft k ≤ B * T.E0 (T.sample (K.cell k)) ^ A ∧
      (K.right k - K.left k)⁻¹ ≤ B * T.E0 (T.sample (K.cell k)) ^ A ∧
      K.right k - K.left k ≤ B * T.E0 (T.sample (K.cell k)) ^ A := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let cut := n04bActualReferenceCut hN
  obtain ⟨B, A, hB, hA, hradial⟩ := n04b_actual_negative_radial_length_bounds hN
  obtain ⟨K₀, P₀, hK₀, hP₀, hpoint⟩ :=
    materialCell_radialE_power_bound hT hN.1.1.1.1 hA
  obtain ⟨K₁, P₁, hK₁, hP₁, hsample⟩ :=
    n04bActualTypedAtlas_negative_material_sample_weights hT hS hN hfield e 0 0 P₀ hP₀
  refine ⟨B * K₀ * K₁, P₁, mul_pos (mul_pos hB hK₀) hK₁, hP₁, ?_⟩
  intro k m side hk
  obtain ⟨j, hhost, hradial⟩ := hradial m
  let a := n04bNegativeLeft C cut (m, side)
  let b := n04bNegativeRight C cut (m, side)
  let t := (a + b) / 2
  have hhalf : D.a < a ∧ a < b ∧ b < D.b :=
    n04b_negativeHalf_bounds hN.1.1.2.2.2.1 (n04bActualReferenceCut_mem hN) (m, side)
  have ht : t ∈ Ioo a b := by
    dsimp only [t]
    constructor <;> linarith only [hhalf.2.1]
  have htwhole : t ∈ Ioo (C.left m) (C.right m) :=
    n04b_negativeHalf_subset (n04bActualReferenceCut_mem hN) (m, side) ht
  have htj : t ∈ D.cells j := hhost htwhole
  have hshift : T.E0 t ^ P₀ ≤ K₁ * T.E0 (T.sample (K.cell k)) ^ P₁ := by
    simpa only [Real.rpow_zero, one_mul] using
      hsample k m side hk t ⟨htwhole.1.le, htwhole.2.le⟩
  have hcost : B * radialE (D.cellIndex j) ^ A ≤
      (B * K₀ * K₁) * T.E0 (T.sample (K.cell k)) ^ P₁ := by
    calc
      _ ≤ B * (K₀ * T.E0 t ^ P₀) :=
        mul_le_mul_of_nonneg_left (hpoint j t htj) hB.le
      _ ≤ B * (K₀ * (K₁ * T.E0 (T.sample (K.cell k)) ^ P₁)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hshift hK₀.le) hB.le
      _ = _ := by ring
  have hleft : K.physicalLeft k = a := by
    change n04bReferenceTypedLeft C cut (e k) = a
    rw [hk]
    rfl
  have hright : K.physicalRight k = b := by
    change n04bReferenceTypedRight C cut (e k) = b
    rw [hk]
    rfl
  have hphysical : K.physicalRight k - K.physicalLeft k = b - a := by
    rw [hleft, hright]
  have hcanonical : K.right k - K.left k = n04bRootCutRadius (C.travel m) := by
    simp only [K, n04bActualTypedAtlas, n04bTypedAtlasData_right,
      n04bTypedAtlasData_left, hk, sub_zero]
  have hh := hradial side
  rw [hphysical, hcanonical]
  exact ⟨hh.1.trans hcost, hh.2.1.trans hcost,
    hh.2.2.1.trans hcost, hh.2.2.2.trans hcost⟩

end ContinuousFlexibility.Analysis
