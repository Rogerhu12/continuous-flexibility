import ContinuousFlexibility.Radial.ReferenceCellL2
import ContinuousFlexibility.Radial.ScaleSlowVariation

/-!
# Endpoint geometry for the actual zero-mode kernel

The distance estimates in `AccumulatingProfileBounds` compare the actual
levels of two cells: a point farther from the endpoints can have only a
fixed larger level. Consequently the inverse profile between a point and
a deeper source costs a fixed coefficient power at the source level.
No monotonicity of the profile or of the cell enumeration is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements

/-- Moving towards an endpoint cannot decrease the actual cell level by
more than one fixed amount. This uses the frozen distance bounds. -/
theorem zeroMode_cellIndex_le_add_of_endpointDistance_le
    {D : ReferenceData} {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C) :
    ∃ K : ℕ, ∀ k m : ℕ, ∀ r t : ℝ,
      r ∈ D.cells k → t ∈ D.cells m →
      min (t - D.a) (D.b - t) ≤ min (r - D.a) (D.b - r) →
      D.cellIndex k ≤ D.cellIndex m + K := by
  rcases hD with ⟨_, _, hC, _, _, _, hdist, _, _, _, _, _, _⟩
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * C 0 + 1)
  refine ⟨K, ?_⟩
  intro k m r t hr ht htr
  have hC0 := hC 0
  have hh := (hdist m t ht).1.trans (htr.trans (hdist k r hr).2)
  have he :
      exp (-((D.cellIndex m : ℝ) + 1) ^ 2) ≤
        (C 0) ^ 2 * exp (-(D.cellIndex k : ℝ) ^ 2) := by
    calc
      exp (-((D.cellIndex m : ℝ) + 1) ^ 2) =
          C 0 * ((C 0)⁻¹ * exp (-((D.cellIndex m : ℝ) + 1) ^ 2)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hC0.ne', one_mul]
      _ ≤ C 0 * (C 0 * exp (-(D.cellIndex k : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hh hC0.le
      _ = (C 0) ^ 2 * exp (-(D.cellIndex k : ℝ) ^ 2) := by ring
  have hCe : C 0 ≤ exp (C 0) := by
    linarith only [add_one_le_exp (C 0)]
  have hCe2 : (C 0) ^ 2 ≤ exp (2 * C 0) := by
    calc
      (C 0) ^ 2 ≤ exp (C 0) * exp (C 0) := by
        nlinarith only [mul_le_mul hCe hCe hC0.le (exp_pos (C 0)).le]
      _ = exp (2 * C 0) := by rw [← exp_add]; congr 1; ring
  have hexp :
      exp (-((D.cellIndex m : ℝ) + 1) ^ 2) ≤
        exp (2 * C 0 - (D.cellIndex k : ℝ) ^ 2) := by
    calc
      _ ≤ (C 0) ^ 2 * exp (-(D.cellIndex k : ℝ) ^ 2) := he
      _ ≤ exp (2 * C 0) * exp (-(D.cellIndex k : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hCe2 (exp_pos _).le
      _ = _ := by rw [← exp_add]; congr 1; ring
  have hsq := exp_le_exp.mp hexp
  by_contra hle
  have hk : D.cellIndex m + K + 1 ≤ D.cellIndex k := by omega
  have hkR : (D.cellIndex m : ℝ) + (K : ℝ) + 1 ≤ (D.cellIndex k : ℝ) := by
    exact_mod_cast hk
  have hm0 : (0 : ℝ) ≤ D.cellIndex m := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ D.cellIndex k := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hsquare : ((D.cellIndex m : ℝ) + (K : ℝ) + 1) ^ 2 ≤
      (D.cellIndex k : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) hk0).2 hkR
  nlinarith only [hsq, hsquare, hK, hC0, sq_nonneg (K : ℝ), mul_nonneg hm0 hK0]

/-- A fixed level shift in the cubic exponent costs only a fixed power of
the actual coefficient weight. -/
theorem zeroMode_radialS_shift_sub_le (K : ℕ) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ m : ℕ, radialS (m + K) - radialS m ≤ A * radialQ m + B := by
  let A : ℝ := 2 * (K : ℝ) + 2 * (K : ℝ) ^ 2
  let B : ℝ := 2 * (K : ℝ) ^ 2 + (2 / 3 : ℝ) * (K : ℝ) ^ 3
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨A, B, hA, hB, ?_⟩
  intro m
  have hm : (m : ℝ) ≤ (m : ℝ) ^ 2 + 1 := by
    nlinarith only [sq_nonneg ((m : ℝ) - 1 / 2)]
  have hml := mul_le_mul_of_nonneg_left hm
    (by positivity : 0 ≤ 2 * (K : ℝ) ^ 2)
  have hmq := mul_le_mul_of_nonneg_left (radial_nat_sq_le_Q m) hA
  calc
    radialS (m + K) - radialS m =
        2 * (K : ℝ) * (m : ℝ) ^ 2 +
          2 * (K : ℝ) ^ 2 * (m : ℝ) + (2 / 3 : ℝ) * (K : ℝ) ^ 3 := by
      simp only [radialS, Nat.cast_add]
      ring
    _ ≤ A * (m : ℝ) ^ 2 + B := by
      dsimp [A, B]
      nlinarith only [hml]
    _ ≤ A * radialQ m + B := add_le_add hmq le_rfl

/-- The inverse profile at any shallower point has a fixed coefficient
power bound at the source cell. The source point need not be a node. -/
theorem zeroMode_inverseProfile_bound_of_deeper
    {D : ReferenceData} {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ m : ℕ, ∀ t s : ℝ, t ∈ D.cells m → s ∈ radialCore D →
      min (t - D.a) (D.b - t) ≤ min (s - D.a) (D.b - s) →
      (D.w s)⁻¹ ≤ A * exp (B * radialQ (D.cellIndex m)) := by
  obtain ⟨K, hK⟩ := zeroMode_cellIndex_le_add_of_endpointDistance_le hD
  obtain ⟨c, d, hshift⟩ := radialQ_shift_le K
  rcases hD with ⟨_, hpart, hC, _, _, _, _, _, _, hinv, _, _, _⟩
  let c' : ℝ := |c| + 1
  let d' : ℝ := |d| + 1
  have hc' : 0 < c' := by dsimp [c']; positivity
  have hd' : 0 < d' := by dsimp [d']; positivity
  have hC0 := hC 0
  refine ⟨C 0 * exp (C 0 * d'), C 0 * c', by positivity, by positivity, ?_⟩
  intro m t s ht hs hts
  obtain ⟨k, hk⟩ := hpart.exists_localizer_ne_zero hs
  have hks : s ∈ D.cells k := hpart.2.2.1 k hk
  have hlevel := hK k m s t hks ht hts
  have hq0 := radialQ_nonneg (D.cellIndex m)
  have hq :
      radialQ (D.cellIndex k) ≤ c' * radialQ (D.cellIndex m) + d' := by
    calc
      radialQ (D.cellIndex k) ≤ radialQ (D.cellIndex m + K) :=
        radialQ_monotone hlevel
      _ ≤ c * radialQ (D.cellIndex m) + d := hshift _
      _ ≤ c' * radialQ (D.cellIndex m) + d' := by
        have hc : c ≤ c' := (le_abs_self c).trans (by dsimp [c']; linarith)
        have hd : d ≤ d' := (le_abs_self d).trans (by dsimp [d']; linarith)
        exact add_le_add (mul_le_mul_of_nonneg_right hc hq0) hd
  have hinv' :
      |(D.w s)⁻¹| ≤ C 0 * exp (radialQ (D.cellIndex k) * C 0) := by
    simpa only [radialJet, radialE, ← exp_mul] using hinv k s hks 0
  calc
    (D.w s)⁻¹ ≤ |(D.w s)⁻¹| := le_abs_self _
    _ ≤ C 0 * exp (radialQ (D.cellIndex k) * C 0) := hinv'
    _ ≤ C 0 * exp ((c' * radialQ (D.cellIndex m) + d') * C 0) :=
      mul_le_mul_of_nonneg_left
        (exp_le_exp.mpr (mul_le_mul_of_nonneg_right hq hC0.le)) hC0.le
    _ = (C 0 * exp (C 0 * d')) * exp ((C 0 * c') * radialQ (D.cellIndex m)) := by
      rw [show (c' * radialQ (D.cellIndex m) + d') * C 0 =
        C 0 * d' + (C 0 * c') * radialQ (D.cellIndex m) by ring, exp_add]
      ring

end ContinuousFlexibility.Radial
