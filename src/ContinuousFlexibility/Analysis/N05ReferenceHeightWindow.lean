module

public import ContinuousFlexibility.Analysis.N05ReferenceE0Weights
public import ContinuousFlexibility.Analysis.N05ReferenceEndpointWeights

/-!
# Cubic reference windows from actual height ratios

A coefficient bound for the two actual material-height ratios controls
the difference of cubic endpoint exponents. The coefficient error on the
active cell is absorbed using slow variation of Q relative to S. No fixed
bound for the difference of the cell indices is asserted or used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

theorem n05_abs_log_sub_le_log_of_ratios {a b U : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hU : 0 < U)
    (hab : a / b ≤ U) (hba : b / a ≤ U) :
    |Real.log a - Real.log b| ≤ Real.log U := by
  have h₁ := Real.log_le_log (div_pos ha hb) hab
  have h₂ := Real.log_le_log (div_pos hb ha) hba
  rw [Real.log_div ha.ne' hb.ne'] at h₁
  rw [Real.log_div hb.ne' ha.ne'] at h₂
  exact abs_le.mpr ⟨by linarith only [h₂], h₁⟩

/-- Actual two-sided material-height ratios on the reference pieces imply
the cubic window needed by the canonical reference inverse. -/
theorem n05_reference_cubic_window_of_height_ratios
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {K : CanonicalData S}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {B : ℝ} (hB : 0 < B)
    (hratio : ∀ m r, r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) →
      T.H r / T.H (T.sample (K.cell m)) ≤ B * T.E0 (T.sample (K.cell m)) ^ B ∧
      T.H (T.sample (K.cell m)) / T.H r ≤ B * T.E0 (T.sample (K.cell m)) ^ B) :
    ∃ A : ℝ, 0 < A ∧ ∀ m j r,
      r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) → r ∈ D.cells j →
        |radialS (D.cellIndex j) - radialS (D.cellIndex (K.cell m))| ≤
          A * (radialQ (D.cellIndex (K.cell m)) + 1) := by
  obtain ⟨F, hF, hlogH⟩ := n05_material_reference_logH_bound hD hT
  obtain ⟨E, hE, hlogE⟩ := n05_material_reference_logE0_upper hD hT
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsample, _, _⟩ := hdata
  let R : ℝ := |Real.log B| + B * E
  have hR : 0 < R := add_pos_of_nonneg_of_pos (abs_nonneg _) (mul_pos hB hE)
  let η : ℝ := (2 * F)⁻¹
  have hη : 0 < η := inv_pos.mpr (by positivity)
  obtain ⟨L, hslow⟩ := Radial.radialQ_sub_le η hη
  let A : ℝ := 2 * (2 * F + R) + 2 * F * |L| + 1
  have hA : 0 < A := by dsimp only [A]; positivity
  have hhalf : F * η = (1 / 2 : ℝ) := by
    dsimp only [η]
    field_simp [hF.ne']
  refine ⟨A, hA, fun m j r hr hrj => ?_⟩
  let n : ℕ := D.cellIndex (K.cell m)
  let i : ℕ := D.cellIndex j
  let s : ℝ := T.sample (K.cell m)
  have hrCore : r ∈ radialCore D := hD.choose_spec.2.1.2.2.2.1 j hrj
  have hsCore : s ∈ radialCore D := hD.choose_spec.2.1.2.2.2.1 _ (hsample _)
  have hHr : 0 < T.H r := (hT.2.1 r hrCore).2.1
  have hHs : 0 < T.H s := (hT.2.1 s hsCore).2.1
  have hEs : 0 < T.E0 s := (hT.2.1 s hsCore).2.2.1
  have hQn : 0 ≤ radialQ n := Radial.radialQ_nonneg n
  have hQi : 0 ≤ radialQ i := Radial.radialQ_nonneg i
  have hlogRatio : |Real.log (T.H r) - Real.log (T.H s)| ≤
      R * (radialQ n + 1) := by
    have hrat := hratio m r hr
    have hlog := n05_abs_log_sub_le_log_of_ratios hHr hHs
      (mul_pos hB (Real.rpow_pos_of_pos hEs B)) hrat.1 hrat.2
    have hsampleLog := hlogE (K.cell m) _ (hsample _)
    rw [Real.log_mul hB.ne' (Real.rpow_pos_of_pos hEs B).ne',
      Real.log_rpow hEs] at hlog
    have hmul := mul_le_mul_of_nonneg_left hsampleLog hB.le
    have hlogB := le_abs_self (Real.log B)
    have hlogBQ := mul_nonneg (abs_nonneg (Real.log B)) hQn
    dsimp only [R, n, s] at *
    nlinarith only [hlog, hmul, hlogB, hlogBQ]
  have hHrLog := hlogH j r hrj
  have hHsLog := hlogH (K.cell m) s (hsample _)
  have hraw : |radialS i - radialS n| ≤
      F * (radialQ i + 1) + (F + R) * (radialQ n + 1) := by
    have htriangle : |radialS i - radialS n| ≤
        |Real.log (T.H r) + radialS i| +
        |Real.log (T.H s) + radialS n| +
        |Real.log (T.H r) - Real.log (T.H s)| := by
      calc
        _ = |((Real.log (T.H r) + radialS i) -
              (Real.log (T.H s) + radialS n)) -
            (Real.log (T.H r) - Real.log (T.H s))| := by congr 1; ring
        _ ≤ |(Real.log (T.H r) + radialS i) -
              (Real.log (T.H s) + radialS n)| +
            |Real.log (T.H r) - Real.log (T.H s)| := abs_sub _ _
        _ ≤ _ := add_le_add (abs_sub _ _) (le_refl _)
    dsimp only [i, n] at *
    nlinarith only [htriangle, hHrLog, hHsLog, hlogRatio]
  have hqdiff : radialQ i - radialQ n ≤
      η * |radialS i - radialS n| + |L| :=
    (le_abs_self _).trans ((hslow i n).trans (add_le_add (le_refl _) (le_abs_self L)))
  have hq := mul_le_mul_of_nonneg_left hqdiff hF.le
  rw [mul_add, ← mul_assoc F η, hhalf] at hq
  have hALQ := mul_nonneg (mul_nonneg hF.le (abs_nonneg L)) hQn
  change |radialS i - radialS n| ≤ A * (radialQ n + 1)
  dsimp only [A]
  nlinarith only [hraw, hq, hALQ, hQn, hF, hR]

end ContinuousFlexibility.Statements
