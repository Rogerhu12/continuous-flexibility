import ContinuousFlexibility.Analysis.N04PositiveGeometryCoordinateNormalization

/-!
# Scalar budgets for the unit coordinate sample estimates

The interval geometry, pure-slot conversion and material arithmetic are
proved without an atlas in context. The actual coordinate consumers
only instantiate these estimates with their retained fields and sample.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

theorem n04PositiveGeometry_coordinate_span_bound
    {a b l r : ℝ} (hl : a ≤ l) (hlr : l < r) (hr : r ≤ b) :
    |r - l| ≤ max 1 (b - a) :=
  (abs_of_nonneg (sub_nonneg.mpr hlr.le)).trans_le
    ((sub_le_sub hr hl).trans (le_max_right _ _))

theorem n04PositiveGeometry_coordinate_unitPoint_mem
    {l r : ℝ} (hlr : l < r) {q : PolarPoint} (hq : q ∈ unitStrip) :
    (l + (r - l) * q.1, q.2) ∈ Ioo l r ×ˢ (univ : Set ℝ) := by
  refine ⟨⟨lt_add_of_pos_right _ (mul_pos (sub_pos.mpr hlr) hq.1.1), ?_⟩, mem_univ _⟩
  calc
    l + (r - l) * q.1 < l + (r - l) :=
      add_lt_add_left (mul_lt_of_lt_one_right (sub_pos.mpr hlr) hq.1.2) l
    _ = r := by ring

/-- Convert the separate slot conditions and enlarge the two seminorms
before applying the original scalar word bound. -/
theorem n04PositiveGeometry_coordinate_separated_norm_bound
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} (w : StateAngleWord n) (T : (Fin n → E × PolarPoint) → ℝ)
    (p₀ p q₀ q : Seminorm ℝ E) (hp : ∀ x, p₀ x ≤ p x) (hq : ∀ x, q₀ x ≤ q x)
    {M R : ℝ}
    (hraw : ∀ u : Fin n → E × PolarPoint,
      (∀ j, if w.isState j then (u j).2 = 0 else (u j).1 = 0) →
      (∀ j, p₀ (u j).1 ≤ 1 ∧ q₀ (u j).1 ≤ R ∧ ‖(u j).2‖ ≤ 1) → |T u| ≤ M)
    (u : Fin n → E × PolarPoint)
    (huL : ∀ j, p (u j).1 ≤ 1) (huH : ∀ j, q (u j).1 ≤ R)
    (huS : ∀ j, ‖(u j).2‖ ≤ 1)
    (hu0 : ∀ j, w.isState j = false → (u j).1 = 0)
    (hu1 : ∀ j, w.isState j = true → (u j).2 = 0) : ‖T u‖ ≤ M := by
  have hpure (j : Fin n) : if w.isState j then (u j).2 = 0 else (u j).1 = 0 := by
    cases hj : w.isState j
    · exact hu0 j hj
    · exact hu1 j hj
  exact (Real.norm_eq_abs _).trans_le (hraw u hpure
    (fun j => ⟨(hp _).trans (huL j), (hq _).trans (huH j), huS j⟩))

/-- The finite affine cost enlarges only the material constant. The
original denominator and positive-parameter height factor are retained. -/
theorem n04PositiveGeometry_coordinate_affine_sample_pack
    {C A E H R : ℝ} {n N κ k β s shift : ℕ}
    (hC : 1 ≤ C) (hA : 1 ≤ A) (hE : 1 ≤ E) (hH : 0 ≤ H) (hR : 1 ≤ R)
    (hn : n ≤ N) (hk : 0 < k) (hκ : κ = k) :
    C ^ n * (A * E ^ A * parameterHeightWeight H κ *
        (R ^ (1 / (((s + shift * k : ℕ) : ℝ) + 1))) ^ (β + shift * κ)) ≤
      max A (C ^ N * A) * E ^ max A (C ^ N * A) * H *
        R ^ (((β + shift * k : ℕ) : ℝ) / (((s + shift * k : ℕ) : ℝ) + 1)) := by
  subst κ
  let B := max A (C ^ N * A)
  have hB : 1 ≤ B := hA.trans (le_max_left _ _)
  have hpack : C ^ n * (A * E ^ A) ≤ B * E ^ B := by
    have hcoef : C ^ n * A ≤ B :=
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC hn) (zero_le_one.trans hA)).trans
        (le_max_right _ _)
    calc
      _ = (C ^ n * A) * E ^ A := by ring
      _ ≤ _ := mul_le_mul hcoef
        (Real.rpow_le_rpow_of_exponent_le hE (le_max_left _ _))
        (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
  have hweight : parameterHeightWeight H k = H := by
    simp only [parameterHeightWeight, Nat.ne_of_gt hk, if_false]
  have hpower : (R ^ (1 / (((s + shift * k : ℕ) : ℝ) + 1))) ^ (β + shift * k) =
      R ^ (((β + shift * k : ℕ) : ℝ) / (((s + shift * k : ℕ) : ℝ) + 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hR)]
    congr 1
    ring
  calc
    _ = (C ^ n * (A * E ^ A)) * H *
        R ^ (((β + shift * k : ℕ) : ℝ) / (((s + shift * k : ℕ) : ℝ) + 1)) := by
      rw [hweight, hpower]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpack hH)
      (Real.rpow_nonneg (zero_le_one.trans hR) _)

theorem n04PositiveGeometry_coordinate_coefficient_bound
    (angle : Bool) {c C E : ℝ} (hC : 1 ≤ C) (hE : 1 ≤ E)
    (hc : |c| ≤ C * E ^ C) :
    |(if angle then (1 : ℝ) else c)| ≤ C * E ^ C := by
  cases angle with
  | false => exact hc
  | true =>
      exact (abs_one : |(1 : ℝ)| = 1).trans_le
        (one_le_mul_of_one_le_of_one_le hC (Real.one_le_rpow hE (zero_le_one.trans hC)))

/-- A fixed reciprocal width has one material cost. Removing the fixed
origin in a positive parameter jet leaves only this scalar product. -/
theorem n04PositiveGeometry_coordinate_inverse_sample_pack
    {C A E H R exponent c x y : ℝ} {k : ℕ}
    (hC : 1 ≤ C) (hE : 1 ≤ E) (hH : 0 ≤ H) (hR : 0 ≤ R) (hk : 0 < k)
    (he : x = c * y) (hc : |c| ≤ C * E ^ C)
    (hraw : |y| ≤ A * E ^ A * parameterHeightWeight H k * R ^ exponent) :
    |x| ≤ max 1 (max (C * A) (C + A)) * E ^ max 1 (max (C * A) (C + A)) * H *
      R ^ exponent := by
  let B := max 1 (max (C * A) (C + A))
  have hB : 1 ≤ B := le_max_left _ _
  have hpack : (C * E ^ C) * (A * E ^ A) ≤ B * E ^ B := by
    calc
      _ = (C * A) * E ^ (C + A) := by
        rw [Real.rpow_add (zero_lt_one.trans_le hE)]
        ring
      _ ≤ _ := mul_le_mul ((le_max_left _ _).trans (le_max_right _ _))
        (Real.rpow_le_rpow_of_exponent_le hE ((le_max_right _ _).trans (le_max_right _ _)))
        (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
  have hweight : parameterHeightWeight H k = H := by
    simp only [parameterHeightWeight, Nat.ne_of_gt hk, if_false]
  calc
    |x| = |c| * |y| := (congrArg abs he).trans (abs_mul _ _)
    _ ≤ (C * E ^ C) * (A * E ^ A * parameterHeightWeight H k * R ^ exponent) :=
      mul_le_mul hc hraw (abs_nonneg _)
        (mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg (zero_le_one.trans hE) _))
    _ = ((C * E ^ C) * (A * E ^ A)) * parameterHeightWeight H k * R ^ exponent := by ring
    _ ≤ B * E ^ B * parameterHeightWeight H k * R ^ exponent :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpack (parameterHeightWeight_nonneg hH _))
        (Real.rpow_nonneg hR _)
    _ = _ := by rw [hweight]

end ContinuousFlexibility.Analysis
