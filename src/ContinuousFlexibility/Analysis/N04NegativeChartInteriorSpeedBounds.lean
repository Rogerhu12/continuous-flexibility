import ContinuousFlexibility.Analysis.N04NegativeChartControlledCollar
import ContinuousFlexibility.Analysis.N01cCommonWholeSpeedBounds
import ContinuousFlexibility.Analysis.SectorParameterGeometry

/-!
# The actual original speed on the material interior

The original endpoint power estimate is retained with its exact spatial
interpolation exponent. The common material collar pays the endpoint
denominator at the actual selected half sample. The affine sector lift
preserves every low and high parameter seminorm exactly.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable (W : N04RealizationStart)

theorem negativeInteriorRadius_component (ρ : ℕ → Bool → ℝ) (hρ : ∀ m side, 0 < ρ m side)
    (m : ℕ) (side : Bool) {x : ℝ}
    (hx : x ∈ Icc (ρ m side / 2) (W.negativeOpticalWidth m side)) :
    inwardComponentPoint (W.C.left m) (W.C.right m) side x ∈
      Ioo (W.C.left m) (W.C.right m) := by
  have hxpos := (half_pos (hρ m side)).trans_le hx.1
  have hxwidth := hx.2.trans_lt (W.negativeOpticalWidth_lt_component m side)
  cases side <;> simp only [inwardComponentPoint, Bool.false_eq_true, ↓reduceIte]
    <;> constructor <;> linarith only [hxpos, hxwidth]

theorem negativeMaterialCollar_interior_component (m : ℕ) (side : Bool) {x : ℝ}
    (hx : x ∈ Icc (W.negativeMaterialCollar m / 2) (W.negativeOpticalWidth m side)) :
    inwardComponentPoint (W.C.left m) (W.C.right m) side x ∈
      Ioo (W.C.left m) (W.C.right m) :=
  W.negativeInteriorRadius_component (fun m _ => W.negativeMaterialCollar m)
    (fun m _ => (W.negativeMaterialCollar_bounds m).1) m side hx

theorem negativeInteriorRadius_distance (ρ : ℕ → Bool → ℝ)
    (hρ : ∀ m side, 0 < ρ m side ∧ ρ m side ≤ W.negativeMaterialCollar m)
    (m : ℕ) (side : Bool) {x : ℝ}
    (hx : x ∈ Icc (ρ m side / 2) (W.negativeOpticalWidth m side)) :
    (min (inwardComponentPoint (W.C.left m) (W.C.right m) side x - W.C.left m)
      (W.C.right m - inwardComponentPoint (W.C.left m) (W.C.right m) side x))⁻¹ ≤
        2 * (ρ m side)⁻¹ := by
  have hl := (hρ m side).2.trans ((W.negativeMaterialCollar_bounds m).2.2.2 false)
  have hr := (hρ m side).2.trans ((W.negativeMaterialCollar_bounds m).2.2.2 true)
  have hρpos : 0 < ρ m side := (hρ m side).1
  have hmin : ρ m side / 2 ≤ min
      (inwardComponentPoint (W.C.left m) (W.C.right m) side x - W.C.left m)
      (W.C.right m - inwardComponentPoint (W.C.left m) (W.C.right m) side x) := by
    cases side <;> simp only [negativeOpticalWidth, n04bNegativeRight, n04bNegativeLeft,
      inwardComponentPoint, Bool.false_eq_true, ↓reduceIte] at hx hl hr ⊢
      <;> apply le_min <;> linarith only [hx.1, hx.2, hl, hr, hρpos]
  have hi := inv_anti₀ (half_pos hρpos) hmin
  rw [inv_div, div_eq_mul_inv] at hi
  exact hi

private theorem interior_host_parameter_weights
    (e : ℕ ≃ N04PieceIndex W.D) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C P : ℝ, 1 ≤ C ∧ 0 ≤ P ∧ ∀ m side k,
      W.T.E0 (W.T.sample (W.C.cell m)) ^ A *
          parameterHeightWeight (W.T.H (W.T.sample (W.C.cell m)) ^ (3 / 4 : ℝ)) k ≤
        C * W.T.E0 (W.negativeHalfSample e m side) ^ P *
          parameterHeightWeight (W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)) k := by
  obtain ⟨C₀, P₀, hC₀, hP₀, hb₀⟩ :=
    n04bActualTypedAtlas_negative_host_sample_E0_power W.hT W.hS W.through03 W.field e A hA
  obtain ⟨C₁, P₁, hC₁, hP₁, hb₁⟩ :=
    n04bActualTypedAtlas_negative_host_sample_weights W.hT W.hS W.through03 W.field
      e (3 / 4 : ℝ) 0 A hA
  let C : ℝ := 1 + C₀ + C₁
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hC₀, hC₁]
  refine ⟨C, P₀ + P₁, hC, add_nonneg hP₀ hP₁, fun m side k => ?_⟩
  have hE := W.floor (W.negativeHalfSample e m side)
  have hH : 0 ≤ W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (W.hT.2.1 _
      (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)).2.1.le _
  by_cases hk : k = 0
  · have hh := hb₀ (e.symm (.inl (m, side))) m side (e.apply_symm_apply _)
      (W.C.cell m) (W.host m)
    simpa only [parameterHeightWeight, if_pos hk, mul_one] using hh.trans
      (mul_le_mul (show C₀ ≤ C by dsimp only [C]; linarith only [hC₁])
        (Real.rpow_le_rpow_of_exponent_le hE (le_add_of_nonneg_right hP₁))
        (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hC))
  · have hh : W.T.H (W.T.sample (W.C.cell m)) ^ (3 / 4 : ℝ) *
        W.T.E0 (W.T.sample (W.C.cell m)) ^ A ≤
          C₁ * (W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ) *
            W.T.E0 (W.negativeHalfSample e m side) ^ P₁) := by
      simpa only [Real.rpow_zero, mul_one] using
        hb₁ (e.symm (.inl (m, side))) m side (e.apply_symm_apply _)
          (W.C.cell m) (W.host m)
    have he := mul_le_mul
      (show C₁ ≤ C by dsimp only [C]; linarith only [hC₀])
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hE (le_add_of_nonneg_left hP₀)) hH)
      (mul_nonneg hH (Real.rpow_nonneg (zero_le_one.trans hE) _))
      (zero_le_one.trans hC)
    simpa only [parameterHeightWeight, if_neg hk, mul_assoc, mul_left_comm, mul_comm]
      using hh.trans he

private theorem inverse_endpoint_power_material
    (e : ℕ ≃ N04PieceIndex W.D) (ρ : ℕ → Bool → ℝ)
    (hρ : ∀ m side, 0 < ρ m side ∧ ρ m side ≤ W.negativeMaterialCollar m)
    (hρb : ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ m side,
      (ρ m side)⁻¹ ≤ B * W.T.E0 (W.negativeHalfSample e m side) ^ A) (s : ℕ) :
    ∃ C P : ℝ, 1 ≤ C ∧ 0 ≤ P ∧ ∀ m side x,
      x ∈ Icc (ρ m side / 2) (W.negativeOpticalWidth m side) →
      ∀ a : ℕ, a ≤ s →
      ((min (inwardComponentPoint (W.C.left m) (W.C.right m) side x - W.C.left m)
        (W.C.right m - inwardComponentPoint (W.C.left m) (W.C.right m) side x))⁻¹) ^ a ≤
          C * W.T.E0 (W.negativeHalfSample e m side) ^ P := by
  obtain ⟨B, A, hB, hA, hb⟩ := hρb
  let C : ℝ := max 1 (2 * B)
  have hC : 1 ≤ C := le_max_left _ _
  refine ⟨C ^ s, A * s, one_le_pow₀ hC, mul_nonneg hA (Nat.cast_nonneg _),
    fun m side x hx a ha => ?_⟩
  let E : ℝ := W.T.E0 (W.negativeHalfSample e m side)
  have hE : 1 ≤ E := W.floor _
  have hr := W.negativeInteriorRadius_component ρ (fun m side => (hρ m side).1) m side hx
  have hd : 0 ≤ (min
      (inwardComponentPoint (W.C.left m) (W.C.right m) side x - W.C.left m)
      (W.C.right m - inwardComponentPoint (W.C.left m) (W.C.right m) side x))⁻¹ :=
    inv_nonneg.mpr (le_min (sub_nonneg.mpr hr.1.le) (sub_nonneg.mpr hr.2.le))
  have hb' := (W.negativeInteriorRadius_distance ρ hρ m side hx).trans
    (mul_le_mul_of_nonneg_left (hb m side) (by norm_num : (0 : ℝ) ≤ 2))
  have hdC : (min
      (inwardComponentPoint (W.C.left m) (W.C.right m) side x - W.C.left m)
      (W.C.right m - inwardComponentPoint (W.C.left m) (W.C.right m) side x))⁻¹ ≤ C * E ^ A :=
    hb'.trans ((by ring : 2 * (B * E ^ A) = (2 * B) * E ^ A).trans_le
      (mul_le_mul_of_nonneg_right (le_max_right 1 (2 * B))
        (Real.rpow_nonneg (zero_le_one.trans hE) A)))
  have hone : 1 ≤ C * E ^ A := one_le_mul_of_one_le_of_one_le hC (Real.one_le_rpow hE hA)
  calc
    _ ≤ (C * E ^ A) ^ a := pow_le_pow_left₀ hd hdC a
    _ ≤ (C * E ^ A) ^ s := pow_le_pow_right₀ hone ha
    _ = _ := by rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hE)]

/-- The raw speed estimate at the actual physical point of either
reference half. Both the spatial fraction and the positive state weight
are exactly those of the original endpoint power control. -/
theorem negativeInterior_speed_power_bounds
    (e : ℕ ≃ N04PieceIndex W.D) (ρ : ℕ → Bool → ℝ)
    (hρ : ∀ m side, 0 < ρ m side ∧ ρ m side ≤ W.negativeMaterialCollar m)
    (hρb : ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ m side,
      (ρ m side)⁻¹ ≤ B * W.T.E0 (W.negativeHalfSample e m side) ^ A)
    {base loss : ℕ} {ε : ℝ}
    (G : WholeCharacteristicSpeedPowerControl W.D W.T W.S W.C base loss ε)
    (K s : ℕ) :
    ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧ ∀ m side (p : PolarPoint),
      p.1 ∈ Icc (ρ m side / 2) (W.negativeOpticalWidth m side) →
      ∀ k : ℕ, k ≤ K → ∀ a b : ℕ, a + b ≤ s →
      ∀ J : SmoothDirections (stateNeighborhood W.S W.C base ε)
        (fun z => mixedDerivative a b
          (minusCharacteristicSpeed (originalCoefficients W.D W.S W.C z))
          (W.negativeInwardPoint m side p)),
      ∀ z ∈ stateNeighborhood W.S W.C base ε,
      pairGrading (stateGrading W.S) realGrading base (z - (W.C.referenceState, 0)) ≤ 1 →
      ∀ v : Fin k → AnnularState W.S × ℝ,
      (∀ i, pairGrading (stateGrading W.S) realGrading base (v i) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (stateGrading W.S) realGrading (s + loss) (z - (W.C.referenceState, 0)) ≤ R →
      (∀ i, pairGrading (stateGrading W.S) realGrading (s + loss) (v i) ≤ R) →
      ‖J.D k z v‖ ≤ C * W.T.E0 (W.negativeHalfSample e m side) ^ A *
        parameterHeightWeight (W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)) k *
          R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  obtain ⟨C₀, A₀, hC₀, hA₀, hraw⟩ := G.bounds K s
  obtain ⟨C₁, A₁, hC₁, hA₁, hhost⟩ := W.interior_host_parameter_weights e A₀ hA₀
  obtain ⟨C₂, A₂, hC₂, hA₂, hdist⟩ := W.inverse_endpoint_power_material e ρ hρ hρb s
  refine ⟨C₀ * C₁ * C₂, A₁ + A₂,
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC₀ hC₁) hC₂,
    add_nonneg hA₁ hA₂, ?_⟩
  intro m side p hp k hk a b hab J z hz hlow v hv R hR hhigh hvhigh
  let q : PolarPoint := W.negativeInwardPoint m side p
  have hq : q ∈ Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ) :=
    ⟨W.negativeInteriorRadius_component ρ (fun m side => (hρ m side).1) m side hp, mem_univ _⟩
  let d : ℝ := min (q.1 - W.C.left m) (W.C.right m - q.1)
  have hd : 0 < d := lt_min (sub_pos.mpr hq.1.1) (sub_pos.mpr hq.1.2)
  let E : ℝ := W.T.E0 (W.negativeHalfSample e m side)
  let H : ℝ := parameterHeightWeight
    (W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)) k
  let Q : ℝ := R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1))
  have hE : 0 < E := zero_lt_one.trans_le (W.floor _)
  have hH : 0 ≤ H := parameterHeightWeight_nonneg
    (Real.rpow_nonneg (W.hT.2.1 _
      (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)).2.1.le _) k
  have hQ : 0 ≤ Q := Real.rpow_nonneg (zero_le_one.trans hR) _
  have hh := hraw m k hk a b hab q hq J z hz hlow v hv R hR hhigh hvhigh
  have hc : d ^ a * ‖J.D k z v‖ ≤ C₀ * (C₁ * E ^ A₁ * H) * Q :=
    hh.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hhost m side k) (zero_le_one.trans hC₀)) hQ)
  have hcancel : d⁻¹ ^ a * (d ^ a * ‖J.D k z v‖) = ‖J.D k z v‖ := by
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hd.ne', one_pow, one_mul]
  calc
    _ = d⁻¹ ^ a * (d ^ a * ‖J.D k z v‖) := hcancel.symm
    _ ≤ d⁻¹ ^ a * (C₀ * (C₁ * E ^ A₁ * H) * Q) :=
      mul_le_mul_of_nonneg_left hc (pow_nonneg (inv_nonneg.mpr hd.le) _)
    _ ≤ (C₂ * E ^ A₂) * (C₀ * (C₁ * E ^ A₁ * H) * Q) :=
      mul_le_mul_of_nonneg_right (hdist m side p.1 hp a (by omega))
        (by positivity)
    _ = _ := by rw [Real.rpow_add hE]; ring

end ContinuousFlexibility.Analysis.N04RealizationStart

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeInterior_speed_power_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeInterior_speed_power_bounds
