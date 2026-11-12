import ContinuousFlexibility.Analysis.CanonicalNegativeMaterialTransport
import ContinuousFlexibility.Analysis.MaterialOneSidedEndpointComparison
import ContinuousFlexibility.Analysis.MaterialSampleBounds

/-!
# The actual negative atlas samples

The cell stored by the actual typed atlas contains the midpoint of its
reference half. It need not be the control cell or a host of the entire
negative component. Its sample nevertheless stays a uniformly bounded
endpoint-coordinate distance from every point of that closed component.
All comparisons below retain this exact stored sample and material data.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hfield : N04bFieldRegularity D S C L base ε)
  (e : ℕ ≃ N04PieceIndex D)

/-- A single bound compares the real stored sample with both closed
halves, including their true roots and optical cut. -/
theorem n04bActualTypedAtlas_negative_sample_endpointX :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    ∃ A : ℝ, 0 ≤ A ∧ ∀ k m side, e k = .inl (m, side) → ∀ r,
      r ∈ Icc (C.left m) (C.right m) →
      |endpointX 1 (Statements.endpointDistance D (T.sample (K.cell k))) -
        endpointX 1 (Statements.endpointDistance D r)| ≤ A := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e
  obtain ⟨A, hA, hosc⟩ := n01_negativeComponent_endpointX_oscillation hT hN.1.1
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsample, _, hcompare⟩ := hdata
  obtain ⟨B, P, hB, _, hindex⟩ := hcompare
  refine ⟨2 * B + A, add_nonneg (mul_nonneg (by norm_num) hB.le) hA, ?_⟩
  intro k m side hk r hr
  let cut := n04bActualReferenceCut hN
  let a := n04bNegativeLeft C cut (m, side)
  let b := n04bNegativeRight C cut (m, side)
  let t := (a + b) / 2
  have hhalf : D.a < a ∧ a < b ∧ b < D.b :=
    n04b_negativeHalf_bounds hN.1.1.2.2.2.1 (n04bActualReferenceCut_mem hN) (m, side)
  have ht : t ∈ Ioo a b := by
    dsimp only [t]
    constructor <;> linarith only [hhalf.2.1]
  have htcore : t ∈ radialCore D :=
    ⟨hhalf.1.trans ht.1, ht.2.trans hhalf.2.2⟩
  have htwhole : t ∈ Ioo (C.left m) (C.right m) :=
    n04b_negativeHalf_subset (n04bActualReferenceCut_mem hN) (m, side) ht
  have hcell : K.cell k = n04CellAt D t := by
    change n04CellAt D
      ((n04bReferenceTypedLeft C cut (e k) + n04bReferenceTypedRight C cut (e k)) / 2) = _
    rw [hk]
    rfl
  have htcell : t ∈ D.cells (K.cell k) := by
    rw [hcell]
    exact n04_cell_at_mem hN.1.1.1.1.choose_spec.2.1 htcore
  have hs := (hindex (K.cell k) (T.sample (K.cell k)) (hsample (K.cell k))).1
  have hm := (hindex (K.cell k) t htcell).1
  have htr := hosc m t r ⟨htwhole.1.le, htwhole.2.le⟩ hr
  have hslo := (abs_le.mp hs).1
  have hshi := (abs_le.mp hs).2
  have hmlo := (abs_le.mp hm).1
  have hmhi := (abs_le.mp hm).2
  have htrlo := (abs_le.mp htr).1
  have htrhi := (abs_le.mp htr).2
  apply abs_le.mpr
  constructor <;> linarith only [hslo, hshi, hmlo, hmhi, htrlo, htrhi]

/-- Every prescribed real height/material power transfers to the exact
negative-piece sample; its coefficient loss is measured at that sample. -/
theorem n04bActualTypedAtlas_negative_material_sample_weights
    (γ η P : ℝ) (hP : 0 ≤ P) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ k m side, e k = .inl (m, side) → ∀ r,
      r ∈ Icc (C.left m) (C.right m) →
      T.H r ^ γ * T.M r ^ η * T.E0 r ^ P ≤
        B * (T.H (T.sample (K.cell k)) ^ γ *
          T.M (T.sample (K.cell k)) ^ η * T.E0 (T.sample (K.cell k)) ^ A) := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e
  obtain ⟨A₀, hA₀, hdist⟩ :=
    n04bActualTypedAtlas_negative_sample_endpointX hT hS hN hfield e
  obtain ⟨B, A, hB, hA, hbound⟩ :=
    material_global_H_M_E0_rpow_bounded_X_shift hT hN.1.1.1.1 γ η hP hA₀
  refine ⟨B, A, hB, hA, ?_⟩
  intro k m side hk r hr
  have hb := hN.1.1.2.2.2.1.1 m
  have hrcore : r ∈ Ioo D.a D.b :=
    ⟨hb.1.trans_le hr.1, hr.2.trans_lt hb.2.2⟩
  exact hbound r (T.sample (K.cell k)) hrcore
    (materialSample_mem_interval hN.1.1.1.1 hT (K.cell k))
    (by simpa only [abs_sub_comm] using hdist k m side hk r hr)

/-- Pointwise normalizers and sample coefficient powers have a common
bound before all negative components, halves and physical points. -/
theorem n04bActualTypedAtlas_negative_material_sample_comparison
    (P : ℝ) (hP : 0 ≤ P) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    ∃ BH AH BE AE : ℝ, 0 < BH ∧ 0 ≤ AH ∧ 0 < BE ∧ 0 ≤ AE ∧
      ∀ k m side, e k = .inl (m, side) → ∀ r,
      r ∈ Icc (C.left m) (C.right m) →
      T.H r / T.H (T.sample (K.cell k)) ≤ BH * T.E0 r ^ AH ∧
        T.E0 (T.sample (K.cell k)) ^ P ≤ BE * T.E0 r ^ AE := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e
  obtain ⟨A₀, hA₀, hdist⟩ :=
    n04bActualTypedAtlas_negative_sample_endpointX hT hS hN hfield e
  obtain ⟨BH, AH, BE, AE, hBH, hAH, hBE, hAE, hbound⟩ :=
    material_oneSided_endpoint_comparison hT hN.1.1.1.1 hP hA₀
  refine ⟨BH, AH, BE, AE, hBH, hAH, hBE, hAE, ?_⟩
  intro k m side hk r hr
  have hb := hN.1.1.2.2.2.1.1 m
  have hrcore : r ∈ Ioo D.a D.b :=
    ⟨hb.1.trans_le hr.1, hr.2.trans_lt hb.2.2⟩
  have hshift : endpointX 1 (Statements.endpointDistance D (T.sample (K.cell k))) ≤
      endpointX 1 (Statements.endpointDistance D r) + A₀ := by
    linarith only [(abs_le.mp (hdist k m side hk r hr)).2]
  exact hbound r (T.sample (K.cell k)) hrcore
    (materialSample_mem_interval hN.1.1.1.1 hT (K.cell k)) hshift

end ContinuousFlexibility.Analysis
