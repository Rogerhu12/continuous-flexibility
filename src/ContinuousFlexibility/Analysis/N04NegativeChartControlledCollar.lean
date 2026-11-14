module

public import ContinuousFlexibility.Analysis.N04NegativeChartFullHalfFields
public import ContinuousFlexibility.Analysis.N04NegativeChartInwardPower
public import ContinuousFlexibility.Analysis.MaterialPointRadialPolynomial

/-!
# A material collar for the literal corrected chart

The one radius uses the retained cutoff width and both actual optical
halves. Its reciprocal has a sampled material bound. The cutoff is
constant on a neighborhood of every collar point, so the original
factored field is exactly the corrected field there. Outside the smaller
overlap collar the same reciprocal pays both physical endpoint distances.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

variable (W : N04RealizationStart)

def negativeMaterialCollar (m : ℕ) : ℝ :=
  (1 + 2 * (W.cutoff.width m)⁻¹ +
    2 * (W.negativeOpticalWidth m false)⁻¹ + 2 * (W.negativeOpticalWidth m true)⁻¹)⁻¹

/-- The radius is common to the two ends and precedes every state. -/
theorem negativeMaterialCollar_bounds (m : ℕ) :
    0 < W.negativeMaterialCollar m ∧ W.negativeMaterialCollar m ≤ 1 ∧
      W.negativeMaterialCollar m ≤ W.cutoff.width m / 2 ∧
      ∀ side, W.negativeMaterialCollar m ≤ W.negativeOpticalWidth m side / 2 := by
  let D : ℝ := 1 + 2 * (W.cutoff.width m)⁻¹ +
    2 * (W.negativeOpticalWidth m false)⁻¹ + 2 * (W.negativeOpticalWidth m true)⁻¹
  have hw := inv_pos.mpr (W.cutoff.width_pos m)
  have hl := inv_pos.mpr (W.negativeOpticalWidth_pos m false)
  have hr := inv_pos.mpr (W.negativeOpticalWidth_pos m true)
  have hD : 1 ≤ D := by dsimp only [D]; linarith
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hhalf (r : ℝ) (h : 0 < r) (hd : 2 * r⁻¹ ≤ D) : D⁻¹ ≤ r / 2 := by
    have hh : 2 ≤ r * D := calc
      2 = r * (2 * r⁻¹) := by rw [mul_left_comm, mul_inv_cancel₀ h.ne', mul_one]
      _ ≤ r * D := mul_le_mul_of_nonneg_left hd h.le
    have hh' := mul_le_mul_of_nonneg_right hh (inv_nonneg.mpr hDp.le)
    rw [mul_assoc, mul_inv_cancel₀ hDp.ne', mul_one] at hh'
    linarith only [hh']
  refine ⟨inv_pos.mpr hDp, inv_le_one_of_one_le₀ hD,
    hhalf _ (W.cutoff.width_pos m) (by dsimp only [D]; linarith), ?_⟩
  intro side
  cases side
  · exact hhalf _ (W.negativeOpticalWidth_pos m false) (by dsimp only [D]; linarith)
  · exact hhalf _ (W.negativeOpticalWidth_pos m true) (by dsimp only [D]; linarith)

private theorem negativeCutoff_inverse_material (e : ℕ ≃ N04PieceIndex W.D) :
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ m side,
      (W.cutoff.width m)⁻¹ ≤ B * W.T.E0 (W.negativeHalfSample e m side) ^ A := by
  obtain ⟨C₀, A₀, hC₀, hA₀, hrad⟩ := materialSample_radialE_power_bound
    W.hT W.radial.1 W.cutoff.widthPower_pos.le
  obtain ⟨C₁, A₁, hC₁, hA₁, hsample⟩ :=
    n04bActualTypedAtlas_negative_host_sample_E0_power
      W.hT W.hS W.through03 W.field e A₀ hA₀
  refine ⟨W.cutoff.widthConstant * C₀ * C₁, A₁,
    mul_pos (mul_pos W.cutoff.widthConstant_pos hC₀) hC₁, hA₁, fun m side => ?_⟩
  calc
    _ ≤ W.cutoff.widthConstant * radialE (W.D.cellIndex (W.cutoff.cell m)) ^
        W.cutoff.widthPower := W.cutoff.inverse_width_bound m
    _ ≤ W.cutoff.widthConstant * (C₀ * W.T.E0 (W.T.sample (W.cutoff.cell m)) ^ A₀) :=
      mul_le_mul_of_nonneg_left (hrad _) W.cutoff.widthConstant_pos.le
    _ ≤ W.cutoff.widthConstant * (C₀ *
        (C₁ * W.T.E0 (W.negativeHalfSample e m side) ^ A₁)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (hsample (e.symm (.inl (m, side))) m side (e.apply_symm_apply _)
          (W.cutoff.cell m) (W.cutoff.component_cell m)) hC₀.le) W.cutoff.widthConstant_pos.le
    _ = _ := by ring

/-- Every radial unscaling cost is paid at the exact selected half sample. -/
theorem negativeMaterialCollar_inverse_material (e : ℕ ≃ N04PieceIndex W.D) :
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ m side,
      (W.negativeMaterialCollar m)⁻¹ ≤
        B * W.T.E0 (W.negativeHalfSample e m side) ^ A := by
  obtain ⟨Bw, Aw, hBw, hAw, hw⟩ := W.negativeCutoff_inverse_material e
  obtain ⟨Bh, Ah, hBh, hAh, hh⟩ :=
    n04bActualTypedAtlas_negative_allHalf_inverse_material W.hT W.hS W.through03 W.field e
  refine ⟨1 + 2 * Bw + 4 * Bh, Aw + Ah, by positivity, add_nonneg hAw hAh,
    fun m side => ?_⟩
  let E : ℝ := W.T.E0 (W.negativeHalfSample e m side)
  have hE : 1 ≤ E := W.floor _
  have hw' : (W.cutoff.width m)⁻¹ ≤ Bw * E ^ (Aw + Ah) :=
    (hw m side).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hE (le_add_of_nonneg_right hAh)) hBw.le)
  have hh' (other : Bool) : (W.negativeOpticalWidth m other)⁻¹ ≤ Bh * E ^ (Aw + Ah) :=
    (hh (e.symm (.inl (m, side))) m side (e.apply_symm_apply _) other).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hE (le_add_of_nonneg_left hAw)) hBh.le)
  have hb := add_le_add (add_le_add (add_le_add
    (Real.one_le_rpow hE (add_nonneg hAw hAh))
    (mul_le_mul_of_nonneg_left hw' (by norm_num : (0 : ℝ) ≤ 2)))
    (mul_le_mul_of_nonneg_left (hh' false) (by norm_num : (0 : ℝ) ≤ 2)))
    (mul_le_mul_of_nonneg_left (hh' true) (by norm_num : (0 : ℝ) ≤ 2))
  simp only [negativeMaterialCollar, inv_inv]
  exact hb.trans_eq (by ring)

/-- The constant value holds on a genuine open germ at every collar point. -/
theorem negativeMaterialCollar_cutoff_germ (m : ℕ) (side : Bool) {x : ℝ}
    (hx : x ≤ W.negativeMaterialCollar m) :
    W.cutoff.cutoff m =ᶠ[𝓝 (inwardComponentPoint (W.C.left m) (W.C.right m) side x)]
      (fun _ => if side then (1 : ℝ) else 0) := by
  have hw := (W.negativeMaterialCollar_bounds m).2.2.1
  have hwp := W.cutoff.width_pos m
  rw [W.cutoff.cutoff_eq m]
  cases side <;> simp only [inwardComponentPoint, Bool.false_eq_true, ↓reduceIte]
  · exact returnOpticalCutoff_eventually_zero hwp
      (by linarith only [hx, hw, W.cutoff.buffer_left m, hwp])
  · exact returnOpticalCutoff_eventually_one hwp
      (by linarith only [hx, hw, W.cutoff.buffer_right m, hwp])

/-- The stored flow has the original radial flow germ, with the retained
constant terminal relabeling at the right endpoint. -/
theorem negativeMaterialCollar_flow_germ (z : AnnularState W.S × ℝ)
    (m : ℕ) (side : Bool) {x : ℝ} (hx : x ≤ W.negativeMaterialCollar m) :
    (fun r => W.L.minusFlow z m r) =ᶠ[
      𝓝 (inwardComponentPoint (W.C.left m) (W.C.right m) side x)]
      (fun r θ => W.C.minusFlow z m r
        (if side then returnCorrectionInitialMap W.S W.C z m θ else θ)) := by
  filter_upwards [W.negativeMaterialCollar_cutoff_germ m side hx] with r hr
  funext θ
  rw [W.minusFlow_eq, returnCorrectedMinusFlow_apply, hr]
  cases side <;> simp only [Bool.false_eq_true, ↓reduceIte,
    returnInterpolation_zero, returnInterpolation_one]

/-- The actual physical half-gap reconstruction is inactive on this
collar for every state, not only at the reference state. -/
theorem negativeMaterialCollar_minus_speed (z : AnnularState W.S × ℝ)
    (m : ℕ) (side : Bool) {p : PolarPoint}
    (hp : p.1 ∈ Ioc (0 : ℝ) (W.negativeMaterialCollar m)) :
    minusCharacteristicSpeed (W.L.coefficients z) (W.negativeInwardPoint m side p) =
      minusCharacteristicSpeed (originalCoefficients W.D W.S W.C z)
        (W.negativeInwardPoint m side p) := by
  have hhalf := (W.negativeMaterialCollar_bounds m).2.2.2 side
  have hwidth := W.negativeOpticalWidth_pos m side
  have hx : p.1 < W.C.right m - W.C.left m :=
    (show p.1 < W.negativeOpticalWidth m side by linarith only [hp.2, hhalf, hwidth]).trans_le
      (W.negativeOpticalWidth_le_component m side)
  have hpoint : (W.negativeInwardPoint m side p).1 ∈ Ioo (W.C.left m) (W.C.right m) := by
    cases side <;> simp only [negativeInwardPoint, inwardComponentPoint,
      Bool.false_eq_true, ↓reduceIte] <;> constructor <;> linarith only [hp.1, hx]
  have hd : deriv (W.cutoff.cutoff m) (W.negativeInwardPoint m side p).1 = 0 := by
    simpa only [negativeInwardPoint, deriv_const] using
      (W.negativeMaterialCollar_cutoff_germ m side hp.2).deriv.eq_of_nhds
  have he := returnCorrectedCoefficients_eq_original_at_of_deriv_zero (D := W.D)
    W.through03.1.1.2.2.2.1.2.2.1 W.cutoff.cutoff z m
    (W.negativeInwardPoint m side p) hpoint hd
  rw [W.coefficients_eq]
  simp only [minusCharacteristicSpeed, returnCorrectedCoefficients_a, he.1, he.2]

namespace NegativeOpticalFactors

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}
  (F : NegativeOpticalFactors W e)

/-- These are precisely the two coefficients used by the actual
corrected root ODE on the material collar. -/
theorem fullHalfFields_corrected_minus_speed {z : AnnularState W.S × ℝ}
    (hz : z ∈ stateNeighborhood W.S W.C W.base (W.ε / 2))
    (m : ℕ) (side : Bool) {p : PolarPoint}
    (hp : p.1 ∈ Ioc (0 : ℝ) (W.negativeMaterialCollar m)) :
    n01ComponentRootOrientation side *
        minusCharacteristicSpeed (W.L.coefficients z) (W.negativeInwardPoint m side p) =
      F.fullHalfDrift z m side p - n01ComponentRootOrientation side *
        Real.sqrt p.1 * F.fullHalfSpeed z m side p := by
  rw [W.negativeMaterialCollar_minus_speed z m side hp]
  exact F.fullHalfFields_minus_speed hz m side ⟨hp.1,
    (hp.2.trans ((W.negativeMaterialCollar_bounds m).2.2.2 side)).trans
      (by linarith only [W.negativeOpticalWidth_pos m side])⟩

end NegativeOpticalFactors

/-- The interior overlap pays both endpoint denominators with this same
material radius, independently of the selected half. -/
theorem negativeMaterialCollar_interior_distance (m : ℕ) (side : Bool) {x : ℝ}
    (hx : x ∈ Icc (W.negativeMaterialCollar m / 2) (W.negativeOpticalWidth m side)) :
    (min (inwardComponentPoint (W.C.left m) (W.C.right m) side x - W.C.left m)
      (W.C.right m - inwardComponentPoint (W.C.left m) (W.C.right m) side x))⁻¹ ≤
        2 * (W.negativeMaterialCollar m)⁻¹ := by
  have hd := (W.negativeMaterialCollar_bounds m).1
  have hl := (W.negativeMaterialCollar_bounds m).2.2.2 false
  have hr := (W.negativeMaterialCollar_bounds m).2.2.2 true
  have hmin : W.negativeMaterialCollar m / 2 ≤
      min (inwardComponentPoint (W.C.left m) (W.C.right m) side x - W.C.left m)
        (W.C.right m - inwardComponentPoint (W.C.left m) (W.C.right m) side x) := by
    cases side <;> simp only [negativeOpticalWidth, n04bNegativeRight, n04bNegativeLeft,
      inwardComponentPoint, Bool.false_eq_true, ↓reduceIte] at hx hl hr ⊢
      <;> apply le_min <;> linarith only [hx.1, hx.2, hl, hr, hd]
  have hi := inv_anti₀ (half_pos hd) hmin
  rw [inv_div, div_eq_mul_inv] at hi
  exact hi

end ContinuousFlexibility.Analysis.N04RealizationStart

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeMaterialCollar_inverse_material' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeMaterialCollar_inverse_material

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.fullHalfFields_corrected_minus_speed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.fullHalfFields_corrected_minus_speed
