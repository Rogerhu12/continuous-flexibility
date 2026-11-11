import ContinuousFlexibility.Analysis.N05ReferencePieceIndexBounds
import ContinuousFlexibility.Analysis.N05ReferenceSourceWeightGap
import ContinuousFlexibility.Analysis.N05CanonicalPhysicalChange
import ContinuousFlexibility.Analysis.N05CanonicalEmbeddings

/-!
# The source multiplier at the actual controlled reference coordinates

The source transformation has the Jacobian divided by height. Its squared
physical density after change of variables is therefore the absolute
Jacobian divided by height squared. The actual coordinate bounds and the
strict endpoint gap control this density uniformly on every physical piece
and every reference cell containing the same radius.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

theorem n05_referenceCanonicalHeight_density_piece_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m p, p ∈ physicalPieceOpen S K m →
      |planeJacobian (K.chart (C.referenceState, 0) m) p| *
        (K.height (C.referenceState, 0) m p)⁻¹ ^ 2 ≤
          B * radialE (D.cellIndex (K.cell m)) ^ A := by
  obtain ⟨A, hA, _, _, hcoordinatesBound⟩ := hcoordinates.2
  refine ⟨A ^ 3, 3 * A, by positivity, by positivity, fun m p hp => ?_⟩
  let E : ℝ := radialE (D.cellIndex (K.cell m))
  let J : ℝ := planeJacobian (K.chart (C.referenceState, 0) m) p
  let H : ℝ := K.height (C.referenceState, 0) m p
  have hE : 0 < E := Real.exp_pos _
  have hJ : |J| ≤ A * E ^ A := by
    dsimp only [J]
    rw [n05_reference_planeJacobian_radial h hcoordinates m hp]
    have hb := hcoordinatesBound m p.1 hp.1
    dsimp only [E]
    linarith only [hb,
      abs_nonneg (K.height (C.referenceState, 0) m (p.1, 0)),
      abs_nonneg ((K.height (C.referenceState, 0) m (p.1, 0))⁻¹),
      abs_nonneg (deriv (fun r => K.height (C.referenceState, 0) m (r, 0)) p.1),
      abs_nonneg ((deriv (fun r => (K.chart (C.referenceState, 0) m (r, 0)).1) p.1)⁻¹)]
  have hH : |H⁻¹| ≤ A * E ^ A := by
    dsimp only [H]
    rw [(hcoordinates.1 m p hp).2]
    have hb := hcoordinatesBound m p.1 hp.1
    dsimp only [E]
    linarith only [hb,
      abs_nonneg (K.height (C.referenceState, 0) m (p.1, 0)),
      abs_nonneg (deriv (fun r => K.height (C.referenceState, 0) m (r, 0)) p.1),
      abs_nonneg (deriv (fun r => (K.chart (C.referenceState, 0) m (r, 0)).1) p.1),
      abs_nonneg ((deriv (fun r => (K.chart (C.referenceState, 0) m (r, 0)).1) p.1)⁻¹)]
  have hHsq : H⁻¹ ^ 2 ≤ (A * E ^ A) ^ 2 := by
    calc
      _ = |H⁻¹| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) hH 2
  have hpower : (A * E ^ A) * (A * E ^ A) ^ 2 = A ^ 3 * E ^ (3 * A) := by
    calc
      _ = A ^ 3 * (E ^ A * E ^ A * E ^ A) := by ring
      _ = A ^ 3 * E ^ (A + A + A) := by
        rw [← Real.rpow_add hE, ← Real.rpow_add hE]
      _ = _ := by congr 2 <;> ring
  have hcoefficient : |J| * H⁻¹ ^ 2 ≤ A ^ 3 * E ^ (3 * A) :=
    (mul_le_mul hJ hHsq (sq_nonneg _) (by positivity)).trans_eq hpower
  exact hcoefficient

theorem n05_referenceCanonicalSource_weight_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {γw γ : ℝ} (hγw : 0 ≤ γw) (hgap : γw < γ) (t M : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m j p, p ∈ physicalPieceOpen S K m → p.1 ∈ D.cells j →
      Real.exp (2 * M * radialQ (D.cellIndex j) + 2 * γw * radialS (D.cellIndex j)) *
        |planeJacobian (K.chart (C.referenceState, 0) m) p| *
        (K.height (C.referenceState, 0) m p)⁻¹ ^ 2 *
        n05CanonicalSampleWeight T S K γ t m ^ 2 ≤ B := by
  obtain ⟨C0, A, hC0, hA, hcoefficient⟩ :=
    n05_referenceCanonicalHeight_density_piece_bound h hcoordinates
  obtain ⟨window, hwindow, hindex⟩ := n05_referencePiece_cell_index_bound hT hcoordinates
  obtain ⟨B, hB, hweight⟩ := n05_referenceSourceWeight_sample_gap_bound hD hT
    hwindow.le hγw hgap hA.le t M
  refine ⟨C0 * B, mul_pos hC0 hB, fun m j p hp hrj => ?_⟩
  let E : ℝ := radialE (D.cellIndex (K.cell m))
  let J : ℝ := planeJacobian (K.chart (C.referenceState, 0) m) p
  let H : ℝ := K.height (C.referenceState, 0) m p
  let w : ℝ := n05CanonicalSampleWeight T S K γ t m
  let e : ℝ := Real.exp
    (2 * M * radialQ (D.cellIndex j) + 2 * γw * radialS (D.cellIndex j))
  have hc : |J| * H⁻¹ ^ 2 ≤ C0 * E ^ A := hcoefficient m p hp
  have hs : e * E ^ A * w ^ 2 ≤ B :=
    hweight (K.cell m) (D.cellIndex j) (hindex m j p.1 hp.1 hrj)
  change e * |J| * H⁻¹ ^ 2 * w ^ 2 ≤ _
  calc
    _ = e * (|J| * H⁻¹ ^ 2) * w ^ 2 := by ring
    _ ≤ e * (C0 * E ^ A) * w ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le) (sq_nonneg _)
    _ = C0 * (e * E ^ A * w ^ 2) := by ring
    _ ≤ C0 * B := mul_le_mul_of_nonneg_left hs hC0.le

/-- The same bound in the form used before applying the actual Jacobian
change of variables to a localized physical source square. -/
theorem n05_referenceCanonicalSource_square_density_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {γw γ : ℝ} (hγw : 0 ≤ γw) (hgap : γw < γ) (t M : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m j p, p ∈ physicalPieceOpen S K m → p.1 ∈ D.cells j →
      Real.exp (2 * M * radialQ (D.cellIndex j) + 2 * γw * radialS (D.cellIndex j)) *
        (|planeJacobian (K.chart (C.referenceState, 0) m) p| /
          K.height (C.referenceState, 0) m p) ^ 2 *
        n05CanonicalSampleWeight T S K γ t m ^ 2 ≤
          B * |planeJacobian (K.chart (C.referenceState, 0) m) p| := by
  obtain ⟨B, hB, hb⟩ := n05_referenceCanonicalSource_weight_bound hD hT h hcoordinates hγw hgap t M
  refine ⟨B, hB, fun m j p hp hrj => ?_⟩
  have hmul := mul_le_mul_of_nonneg_right (hb m j p hp hrj)
    (abs_nonneg (planeJacobian (K.chart (C.referenceState, 0) m) p))
  convert hmul using 1 <;> simp only [div_eq_mul_inv] <;> ring

end ContinuousFlexibility.Statements
