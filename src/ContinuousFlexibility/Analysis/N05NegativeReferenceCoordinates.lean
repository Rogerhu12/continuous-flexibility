import ContinuousFlexibility.Analysis.N05NegativePieceCount
import ContinuousFlexibility.Radial.ReferenceCellL2

/-!
# Controlled coordinates on the actual negative reference pieces

The actual optical lower certificate and an interior point for each assigned
cell give the negative part of the reference coordinate specification. The
radial identities, cell association, finite fibers and five first coefficient
bounds all concern the same N04 data. One positive constant controls every
quantitative conclusion; no chart estimate is assumed as an input.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Radial

/-- The negative pieces satisfy the literal conjunction in the reference
coordinate specification, with the piece quantifiers and index fibers
restricted to `K.positive i = false`. -/
theorem n05_negative_reference_coordinates
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hoptical : N05ActualCarrierOpticalLower D C)
    (hlabels : N05NegativePieceCellLabels D S K) :
    (∀ i, K.positive i = false → ∀ p, p ∈ physicalPieceOpen S K i →
      K.chart (C.referenceState, 0) i p =
        ((K.chart (C.referenceState, 0) i (p.1, 0)).1, p.2) ∧
      K.height (C.referenceState, 0) i p =
        K.height (C.referenceState, 0) i (p.1, 0)) ∧
    ∃ B : ℝ, 0 < B ∧
      (∀ i, K.positive i = false → ∀ r,
        r ∈ Ioo (K.physicalLeft i) (K.physicalRight i) →
        ∃ j, r ∈ D.cells j ∧
          |(D.cellIndex j : ℝ) - (D.cellIndex (K.cell i) : ℝ)| ≤ B) ∧
      (∀ n : ℕ,
        {i | K.positive i = false ∧ D.cellIndex (K.cell i) = n}.Finite ∧
        ({i | K.positive i = false ∧ D.cellIndex (K.cell i) = n}.ncard : ℝ) ≤
          B * radialE n ^ B) ∧
      (∀ i, K.positive i = false → ∀ r,
        r ∈ Ioo (K.physicalLeft i) (K.physicalRight i) →
        |K.height (C.referenceState, 0) i (r, 0)| +
        |(K.height (C.referenceState, 0) i (r, 0))⁻¹| +
        |deriv (fun t => K.height (C.referenceState, 0) i (t, 0)) r| +
        |deriv (fun t => (K.chart (C.referenceState, 0) i (t, 0)).1) r| +
        |(deriv (fun t => (K.chart (C.referenceState, 0) i (t, 0)).1) r)⁻¹| ≤
          B * radialE (D.cellIndex (K.cell i)) ^ B) := by
  obtain ⟨C₀, A₀, window, hC₀, hA₀, hwindow, hgeometry⟩ :=
    n05_negative_reference_geometry_at_selected_cells hD hT hS h hoptical hlabels
  obtain ⟨C₁, hC₁, hcount⟩ := n05_negativePieceIndex_count hD hT hS h hlabels
  let B : ℝ := C₀ + A₀ + window + C₁ + 1
  have hB : 0 < B := by dsimp only [B]; linarith
  have hC₀B : C₀ ≤ B := by dsimp only [B]; linarith
  have hA₀B : A₀ ≤ B := by dsimp only [B]; linarith
  have hwindowB : window ≤ B := by dsimp only [B]; linarith
  have hC₁B : C₁ ≤ B := by dsimp only [B]; linarith
  have henlarge (n : ℕ) {c a : ℝ} (hc : c ≤ B) (ha : a ≤ B) :
      c * radialE n ^ a ≤ B * radialE n ^ B := by
    have hE : 0 < radialE n := Real.exp_pos _
    have hE1 : 1 ≤ radialE n := Real.one_le_exp_iff.mpr (radialQ_nonneg n)
    exact mul_le_mul hc (Real.rpow_le_rpow_of_exponent_le hE1 ha)
      (Real.rpow_nonneg hE.le a) hB.le
  refine ⟨?_, B, hB, ?_, ?_, ?_⟩
  · rintro i hi ⟨r, θ⟩ hp
    exact ⟨n05_negative_reference_chart_radial hT hS h hi
      (Ioo_subset_Icc_self hp.1) θ,
      n05_negative_reference_height_radial_open hT hS h hi hp.1 θ⟩
  · intro i hi r hr
    have hpart : RadialPartition D := hD.1.choose_spec.2.1
    have h04 := h.2.2.2.2
    have hcore : r ∈ radialCore D := (h04.2.2.2.1 i).2.2 hr
    obtain ⟨j, hj⟩ := hpart.exists_localizer_ne_zero hcore
    have hrj : r ∈ D.cells j := hpart.2.2.1 j hj
    exact ⟨j, hrj, ((hgeometry i hi).1 j r hr hrj).trans hwindowB⟩
  · intro n
    exact ⟨(hcount n).1, (hcount n).2.trans (henlarge n hC₁B hC₁B)⟩
  · intro i hi r hr
    have hrclosed := Ioo_subset_Icc_self hr
    have hH : 0 < K.height (C.referenceState, 0) i (r, 0) :=
      (n05_negative_reference_root_slices hT hS h hi hrclosed 0).2.2.1
    have hJ : planeJacobian (K.chart (C.referenceState, 0) i) (r, 0) =
        deriv (fun t => (K.chart (C.referenceState, 0) i (t, 0)).1) r :=
      (n05_negative_reference_density_closed hT hS h hi hrclosed 0).1
    calc
      _ = n05NegativeReferenceFirstSize S C K i r 0 := by
        simp only [n05NegativeReferenceFirstSize, hJ, abs_of_pos hH,
          abs_of_pos (inv_pos.mpr hH)]
      _ ≤ C₀ * radialE (D.cellIndex (K.cell i)) ^ A₀ :=
        (hgeometry i hi).2 r hrclosed 0
      _ ≤ B * radialE (D.cellIndex (K.cell i)) ^ B :=
        henlarge (D.cellIndex (K.cell i)) hC₀B hA₀B

end ContinuousFlexibility.Statements
