module

public import ContinuousFlexibility.Analysis.N05CanonicalGeometryAccess
public import ContinuousFlexibility.Analysis.N05CanonicalPhysicalChange
public import ContinuousFlexibility.Analysis.N05CanonicalPhysicalWeight
public import ContinuousFlexibility.Analysis.N05ReferencePieceCoefficients

/-!
# The actual canonical height multiplier controls the physical endpoint weight

The genuine chart, height and reciprocal-profile bounds combine into one
coefficient power. The actual material sample weights absorb that power
uniformly over every piece and every fixed material order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

/-- The exact multiplier required to transfer a forgotten canonical height
to the physical inverse-square-root profile class is uniformly bounded. -/
theorem n05_referenceCanonicalHeight_physical_weight_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {γ : ℝ} (hγ : 0 < γ) (t : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m p, p ∈ referencePhysicalPieceOpen S K m →
      (D.w p.1)⁻¹ * K.height (C.referenceState, 0) m p ^ 2 *
        (n05CanonicalSampleWeight T S K γ t m) ^ 2 ≤
          B * |planeJacobian (K.chart (C.referenceState, 0) m) p| := by
  obtain ⟨Cw, Aw, hCw, hAw, hw⟩ :=
    n05_referenceReciprocal_piece_bound hD hcoordinates
  obtain ⟨A, hA, _, _, hcoeff⟩ := hcoordinates.2
  obtain ⟨B, hB, hsample⟩ := n05_canonicalSample_coefficient_square_bound
    hD hT S K hγ (show 0 ≤ Aw + 3 * A by positivity) t
  refine ⟨Cw * A ^ 3 * B, by positivity, fun m p hp => ?_⟩
  let E : ℝ := radialE (D.cellIndex (K.cell m))
  let H : ℝ := K.height (C.referenceState, 0) m p
  let J : ℝ := planeJacobian (K.chart (C.referenceState, 0) m) p
  let w : ℝ := n05CanonicalSampleWeight T S K γ t m
  have hE : 0 < E := Real.exp_pos _
  have hheight : |H| ≤ A * E ^ A := by
    have hb := hcoeff m p.1 hp.1
    have hh := (hcoordinates.1 m p hp).2
    dsimp only [H]
    rw [hh]
    dsimp only [E]
    linarith only [hb,
      abs_nonneg ((K.height (C.referenceState, 0) m (p.1, 0))⁻¹),
      abs_nonneg (deriv (fun r => K.height (C.referenceState, 0) m (r, 0)) p.1),
      abs_nonneg (deriv (fun r => (K.chart (C.referenceState, 0) m (r, 0)).1) p.1),
      abs_nonneg ((deriv (fun r => (K.chart (C.referenceState, 0) m (r, 0)).1) p.1)⁻¹)]
  have hJinv : |J|⁻¹ ≤ A * E ^ A := by
    rw [← abs_inv]
    dsimp only [J]
    rw [n05_reference_planeJacobian_radial h hcoordinates m hp]
    have hb := hcoeff m p.1 hp.1
    dsimp only [E]
    linarith only [hb,
      abs_nonneg (K.height (C.referenceState, 0) m (p.1, 0)),
      abs_nonneg ((K.height (C.referenceState, 0) m (p.1, 0))⁻¹),
      abs_nonneg (deriv (fun r => K.height (C.referenceState, 0) m (r, 0)) p.1),
      abs_nonneg (deriv (fun r => (K.chart (C.referenceState, 0) m (r, 0)).1) p.1)]
  have hh2 : H ^ 2 ≤ (A * E ^ A) ^ 2 := by
    calc
      _ = |H| ^ 2 := (sq_abs H).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg H) hheight 2
  have hpower : (Cw * E ^ Aw) * (A * E ^ A) ^ 2 * (A * E ^ A) =
      Cw * A ^ 3 * E ^ (Aw + 3 * A) := by
    calc
      _ = (Cw * A ^ 3) * (E ^ Aw * E ^ A * E ^ A * E ^ A) := by ring
      _ = (Cw * A ^ 3) * E ^ (Aw + A + A + A) := by
        rw [← Real.rpow_add hE, ← Real.rpow_add hE, ← Real.rpow_add hE]
      _ = _ := by congr 2 <;> ring
  have hcoefficient : (D.w p.1)⁻¹ * H ^ 2 * |J|⁻¹ ≤
      Cw * A ^ 3 * E ^ (Aw + 3 * A) := by
    calc
      _ ≤ (Cw * E ^ Aw) * (A * E ^ A) ^ 2 * (A * E ^ A) :=
        mul_le_mul
          (mul_le_mul (hw m p.1 hp.1) hh2 (sq_nonneg H) (by positivity))
          hJinv (inv_nonneg.mpr (abs_nonneg J)) (by positivity)
      _ = _ := hpower
  have hbound : ((D.w p.1)⁻¹ * H ^ 2 * |J|⁻¹) * w ^ 2 ≤ Cw * A ^ 3 * B := by
    calc
      _ ≤ (Cw * A ^ 3 * E ^ (Aw + 3 * A)) * w ^ 2 :=
        mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg w)
      _ = (Cw * A ^ 3) * (E ^ (Aw + 3 * A) * w ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsample m) (by positivity)
  have h01 := h.1.1.1
  have h04 := h.2.2.2.2.1
  have hcharts := n05_reference_charts h04
  have hnonzero := (hcharts
    (n05_referenceState_mem h01.2.1)
    (n05_referenceState_sector h01.2.2.1) m).2.2.2.2.2.2.2 p hp
  have hJ : |J| ≠ 0 := abs_ne_zero.mpr hnonzero.2.1
  have hcancel : (((D.w p.1)⁻¹ * H ^ 2 * |J|⁻¹) * w ^ 2) * |J| =
      (D.w p.1)⁻¹ * H ^ 2 * w ^ 2 := by
    calc
      _ = ((D.w p.1)⁻¹ * H ^ 2 * w ^ 2) * (|J|⁻¹ * |J|) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hJ, mul_one]
  have hm := mul_le_mul_of_nonneg_right hbound (abs_nonneg J)
  rw [hcancel] at hm
  exact hm

end ContinuousFlexibility.Statements
