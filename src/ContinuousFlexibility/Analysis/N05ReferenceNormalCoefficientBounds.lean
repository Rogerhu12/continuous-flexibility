module

public import ContinuousFlexibility.Analysis.N05CanonicalGeometryAccess
public import ContinuousFlexibility.Analysis.N05ReferenceNormalCoefficients

/-!
# Fixed material bounds for the genuine radial derivative coefficients

The selected coordinate bounds control the inverse Jacobian and the
height correction simultaneously. The resulting cell exponent is fixed
before choosing any source, material level, or angular derivative order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)

include hcoordinates

theorem n05_referenceNormalLeading_piece_bound :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m r,
      r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) →
        |(deriv (fun t => (K.chart (C.referenceState, 0) m (t, 0)).1) r)⁻¹| ^ 2 ≤
          B * radialE (D.cellIndex (K.cell m)) ^ A := by
  obtain ⟨A, hA, _, _, hb⟩ := hcoordinates.2
  refine ⟨A ^ 2, 2 * A, by positivity, by positivity, fun m r hr => ?_⟩
  let E : ℝ := radialE (D.cellIndex (K.cell m))
  have hE : 0 < E := Real.exp_pos _
  have hJ : |(deriv (fun t => (K.chart (C.referenceState, 0) m (t, 0)).1) r)⁻¹| ≤
      A * E ^ A := by
    have hbound := hb m r hr
    dsimp only [E]
    linarith only [hbound,
      abs_nonneg (K.height (C.referenceState, 0) m (r, 0)),
      abs_nonneg ((K.height (C.referenceState, 0) m (r, 0))⁻¹),
      abs_nonneg (deriv (fun t => K.height (C.referenceState, 0) m (t, 0)) r),
      abs_nonneg (deriv (fun t => (K.chart (C.referenceState, 0) m (t, 0)).1) r)]
  calc
    _ ≤ (A * E ^ A) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hJ 2
    _ = A ^ 2 * (E ^ A * E ^ A) := by ring
    _ = A ^ 2 * E ^ (A + A) := by rw [← Real.rpow_add hE]
    _ = _ := by congr 2 <;> ring

theorem n05_referenceNormalDrift_piece_bound :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m r,
      r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) →
        |deriv (fun t => K.height (C.referenceState, 0) m (t, 0)) r /
          K.height (C.referenceState, 0) m (r, 0) /
            deriv (fun t => (K.chart (C.referenceState, 0) m (t, 0)).1) r| ^ 2 ≤
          B * radialE (D.cellIndex (K.cell m)) ^ A := by
  obtain ⟨A, hA, _, _, hb⟩ := hcoordinates.2
  refine ⟨A ^ 6, 6 * A, by positivity, by positivity, fun m r hr => ?_⟩
  let E : ℝ := radialE (D.cellIndex (K.cell m))
  let H : ℝ := K.height (C.referenceState, 0) m (r, 0)
  let H' : ℝ := deriv (fun t => K.height (C.referenceState, 0) m (t, 0)) r
  let J : ℝ := deriv (fun t => (K.chart (C.referenceState, 0) m (t, 0)).1) r
  have hE : 0 < E := Real.exp_pos _
  have hbound : |H| + |H⁻¹| + |H'| + |J| + |J⁻¹| ≤ A * E ^ A := hb m r hr
  have hH : |H⁻¹| ≤ A * E ^ A := by
    linarith only [hbound, abs_nonneg H, abs_nonneg H', abs_nonneg J, abs_nonneg J⁻¹]
  have hH' : |H'| ≤ A * E ^ A := by
    linarith only [hbound, abs_nonneg H, abs_nonneg H⁻¹, abs_nonneg J, abs_nonneg J⁻¹]
  have hJ : |J⁻¹| ≤ A * E ^ A := by
    linarith only [hbound, abs_nonneg H, abs_nonneg H⁻¹, abs_nonneg H', abs_nonneg J]
  have hp : |H' / H / J| ≤ (A * E ^ A) * (A * E ^ A) * (A * E ^ A) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul hH' hH (abs_nonneg _) (by positivity))
      hJ (abs_nonneg _) (by positivity)
  change |H' / H / J| ^ 2 ≤ _
  calc
    _ ≤ ((A * E ^ A) * (A * E ^ A) * (A * E ^ A)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hp 2
    _ = A ^ 6 * (E ^ A * E ^ A * E ^ A * E ^ A * E ^ A * E ^ A) := by ring
    _ = A ^ 6 * E ^ (A + A + A + A + A + A) := by
      rw [← Real.rpow_add hE, ← Real.rpow_add hE, ← Real.rpow_add hE,
        ← Real.rpow_add hE, ← Real.rpow_add hE]
    _ = _ := by congr 2 <;> ring

theorem n05ReferenceNormal_coefficients_cell_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ j p, D.localizer j p.1 ≠ 0 →
      |n05ReferenceNormalLeading S C K p| ^ 2 ≤ B * Real.exp (A * radialQ (D.cellIndex j)) ∧
      |n05ReferenceNormalDrift S C K p| ^ 2 ≤ B * Real.exp (A * radialQ (D.cellIndex j)) := by
  obtain ⟨B₁, A₁, hB₁, hA₁, hb₁⟩ := n05_referenceNormalLeading_piece_bound hcoordinates
  obtain ⟨B₀, A₀, hB₀, hA₀, hb₀⟩ := n05_referenceNormalDrift_piece_bound hcoordinates
  obtain ⟨C₁, L₁, hC₁, hL₁, hc₁⟩ :=
    n05PhysicalPieceRadialMultiplier_cell_bound hD hT h.2.2.2.2.1 hcoordinates hB₁ hA₁.le hb₁
  obtain ⟨C₀, L₀, hC₀, hL₀, hc₀⟩ :=
    n05PhysicalPieceRadialMultiplier_cell_bound hD hT h.2.2.2.2.1 hcoordinates hB₀ hA₀.le hb₀
  refine ⟨C₁ + C₀, L₁ + L₀, add_pos hC₁ hC₀, add_pos hL₁ hL₀, fun j p hp => ?_⟩
  have hQ := radialQ_nonneg (D.cellIndex j)
  have he₁ : Real.exp (L₁ * radialQ (D.cellIndex j)) ≤
      Real.exp ((L₁ + L₀) * radialQ (D.cellIndex j)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hL₀.le) hQ)
  have he₀ : Real.exp (L₀ * radialQ (D.cellIndex j)) ≤
      Real.exp ((L₁ + L₀) * radialQ (D.cellIndex j)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hL₁.le) hQ)
  exact ⟨(hc₁ j p hp).trans (mul_le_mul (le_add_of_nonneg_right hC₀.le) he₁
      (Real.exp_pos _).le (add_pos hC₁ hC₀).le),
    (hc₀ j p hp).trans (mul_le_mul (le_add_of_nonneg_left hC₁.le) he₀
      (Real.exp_pos _).le (add_pos hC₁ hC₀).le)⟩

end ContinuousFlexibility.Statements
