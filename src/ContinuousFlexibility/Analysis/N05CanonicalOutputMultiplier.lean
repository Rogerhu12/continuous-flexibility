import ContinuousFlexibility.Analysis.N05ReferencePieceIndexBounds
import ContinuousFlexibility.Analysis.N05ReferencePieceCoefficients
import ContinuousFlexibility.Analysis.N05PhysicalPieces
import ContinuousFlexibility.Radial.R11bPhysicalMultiplier

/-!
# Actual piecewise constant physical coefficient multipliers

The genuine open physical pieces are disjoint. Their constant majorants
therefore form a measurable field with exactly one active value on each
piece. The real cell-index association then allows the existing physical
partition estimate to absorb every fixed coefficient power.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial

/-- A constant on every actual physical piece, and zero off their union. -/
def n05PhysicalPieceConstant (S : PhysicalSpacesData) (K : CanonicalData S)
    (c : ℕ → ℝ) : ℝ → ℝ :=
  fun r => ∑' m, (Ioo (K.physicalLeft m) (K.physicalRight m)).indicator
    (fun _ => c m) r

theorem n05PhysicalPieceConstant_measurable
    (S : PhysicalSpacesData) (K : CanonicalData S) (c : ℕ → ℝ) :
    Measurable (n05PhysicalPieceConstant S K c) :=
  Measurable.tsum (fun _ => measurable_const.indicator measurableSet_Ioo)

theorem n05PhysicalPieceConstant_eq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    (c : ℕ → ℝ) {m : ℕ} {r : ℝ}
    (hr : r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)) :
    n05PhysicalPieceConstant S K c r = c m := by
  classical
  have hz : ∀ n, n ≠ m →
      (Ioo (K.physicalLeft n) (K.physicalRight n)).indicator (fun _ => c n) r = 0 := by
    intro n hnm
    apply indicator_of_notMem
    intro hn
    exact Set.disjoint_left.mp (n05_physicalPieces_pairwise_disjoint h04 hnm) hn hr
  exact (tsum_eq_single m hz).trans (indicator_of_mem hr _)

theorem n05PhysicalPieceConstant_eq_zero
    (S : PhysicalSpacesData) (K : CanonicalData S) (c : ℕ → ℝ) {r : ℝ}
    (hr : ¬ ∃ m, r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)) :
    n05PhysicalPieceConstant S K c r = 0 := by
  classical
  have hz (m : ℕ) :
      (Ioo (K.physicalLeft m) (K.physicalRight m)).indicator (fun _ => c m) r = 0 :=
    indicator_of_notMem (fun hm => hr ⟨m, hm⟩) _
  simp only [n05PhysicalPieceConstant, hz, tsum_zero]

/-- The square root of a fixed coefficient envelope on the actual pieces. -/
def n05CanonicalOutputMajorant (D : ReferenceData) (S : PhysicalSpacesData)
    (K : CanonicalData S) (B A : ℝ) : PolarPoint → ℝ :=
  fun p => n05PhysicalPieceConstant S K
    (fun m => Real.sqrt (B * radialE (D.cellIndex (K.cell m)) ^ A)) p.1

theorem n05CanonicalOutputMajorant_measurable
    (D : ReferenceData) (S : PhysicalSpacesData) (K : CanonicalData S) (B A : ℝ) :
    Measurable (n05CanonicalOutputMajorant D S K B A) :=
  (n05PhysicalPieceConstant_measurable S K _).comp measurable_fst

theorem n05CanonicalOutputMajorant_sq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {B A : ℝ} (hB : 0 ≤ B) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ physicalPieceOpen S K m) :
    n05CanonicalOutputMajorant D S K B A p ^ 2 =
      B * radialE (D.cellIndex (K.cell m)) ^ A := by
  change n05PhysicalPieceConstant S K _ p.1 ^ 2 = _
  rw [n05PhysicalPieceConstant_eq h04 _ hp.1]
  exact Real.sq_sqrt (mul_nonneg hB (Real.rpow_nonneg (Real.exp_pos _).le _))

/-- The actual piece coefficient is bounded on every active reference
cell. No multiplicity count is needed for this physical multiplier. -/
theorem n05CanonicalOutputMajorant_cell_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {B A : ℝ} (hB : 0 < B) (hA : 0 ≤ A) :
    ∃ C0 L0 : ℝ, 0 < C0 ∧ 0 < L0 ∧ ∀ j p,
      D.localizer j p.1 ≠ 0 →
        |n05CanonicalOutputMajorant D S K B A p| ^ 2 ≤
          C0 * Real.exp (L0 * radialQ (D.cellIndex j)) := by
  classical
  obtain ⟨window, _, hindex⟩ := n05_referencePiece_cell_index_bound hT hcoordinates
  obtain ⟨C0, hC0, hweight⟩ := n05_radialE_power_index_window A window hA
  refine ⟨B * C0, C0, mul_pos hB hC0, hC0, fun j p hpj => ?_⟩
  have hrj : p.1 ∈ D.cells j := hD.choose_spec.2.1.2.2.1 j hpj
  by_cases hp : ∃ m, p.1 ∈ Ioo (K.physicalLeft m) (K.physicalRight m)
  · obtain ⟨m, hm⟩ := hp
    rw [sq_abs, n05CanonicalOutputMajorant_sq h04 hB.le m ⟨hm, mem_univ _⟩]
    have hwindow : |(D.cellIndex (K.cell m) : ℝ) - (D.cellIndex j : ℝ)| ≤ window := by
      rw [abs_sub_comm]
      exact hindex m j p.1 hm hrj
    calc
      _ ≤ B * (C0 * radialE (D.cellIndex j) ^ C0) :=
        mul_le_mul_of_nonneg_left
          (hweight (D.cellIndex (K.cell m)) (D.cellIndex j) hwindow) hB.le
      _ = _ := by
        rw [radialE, ← Real.exp_mul]
        rw [mul_comm (radialQ (D.cellIndex j)) C0]
        ring
  · have hz : n05CanonicalOutputMajorant D S K B A p = 0 :=
      n05PhysicalPieceConstant_eq_zero S K _ hp
    rw [hz, abs_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    positivity

/-- Positive attenuation gives the physical L² bound for every actual
piecewise coefficient envelope, uniformly over the represented field. -/
theorem n05CanonicalOutputMajorant_memLp
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {B A γ : ℝ} (hB : 0 < B) (hA : 0 ≤ A) (hγ : 0 < γ) (M : ℝ) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ f : PolarPoint → ℝ,
      RadialCellIntegrable D f → Summable (outputCellSquare D γ M f) →
      MemLp (fun p => n05CanonicalOutputMajorant D S K B A p * f p) 2
        (radialPhysicalMeasure D) ∧
      (∫ p, (n05CanonicalOutputMajorant D S K B A p * f p) ^ 2
        ∂radialPhysicalMeasure D) ≤ C0 * ∑' m, outputCellSquare D γ M f m := by
  obtain ⟨C0, L0, hC0, _, hbound⟩ :=
    n05CanonicalOutputMajorant_cell_bound hD hT h04 hcoordinates hB hA
  exact r11b_cell_multiplier_L2_bound hD.choose_spec.2.1 hD.choose_spec.1.2.1.le
    (n05CanonicalOutputMajorant D S K B A)
    (n05CanonicalOutputMajorant_measurable D S K B A).aestronglyMeasurable
    C0 L0 (-2 * M) γ hC0.le hγ
    (fun j => Eventually.of_forall (hbound j))

end ContinuousFlexibility.Statements
