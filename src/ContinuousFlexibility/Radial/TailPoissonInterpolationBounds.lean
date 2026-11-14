module

public import ContinuousFlexibility.Radial.TailActualNodeCoefficients

/-!
# Weighted bounds for actual Poisson interpolation

Each physical interpolant uses the same canonical Poisson pair as the
tridiagonal coefficients. Exact resistance-coordinate transport turns the
local bounds into estimates for the original density and physical interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open ContinuousFlexibility.Statements

/-- The physical interpolation with prescribed values at the two nodes. -/
def tailActualEdgeInterpolation (T : DeepTailData) (hT : DeepTailHypotheses T)
    (n : ℕ) (a b : ℝ) : ℝ → ℝ :=
  fun x => a * tailActualEdgePoissonPhysical T hT n false x +
    b * tailActualEdgePoissonPhysical T hT n true x

theorem tailActualEdgeInterpolation_differentiable {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) (a b : ℝ) :
    Differentiable ℝ (tailActualEdgeInterpolation T hT n a b) :=
  ((tailActualEdgePoissonPhysical_differentiable hT n false).const_mul a).add
    ((tailActualEdgePoissonPhysical_differentiable hT n true).const_mul b)

theorem tailActualEdgeInterpolation_weighted_integrable {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) (a b : ℝ) {F : ℝ → ℝ} (hF : Continuous F) :
    IntervalIntegrable (fun x => T.p x * F (tailActualEdgeInterpolation T hT n a b x))
      volume (T.node n) (T.node (n + 1)) :=
  ((tailActualEdge_continuousOn hT n).mul
    (hF.comp (tailActualEdgeInterpolation_differentiable hT n a b).continuous).continuousOn).intervalIntegrable_of_Icc
      (μ := volume) (tailActualEdge_order hT n).le

/-- Exact transport for any continuous function of the physical interpolant. -/
theorem tailActualEdgeInterpolation_integral {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) (a b : ℝ) {F : ℝ → ℝ} (hF : Continuous F) :
    (∫ x in T.node n..T.node (n + 1), T.p x * F (tailActualEdgeInterpolation T hT n a b x)) =
      ∫ s in 0..tailActualEdgeLength T n, tailActualEdgeWeight T hT n s *
        F (a * tailActualEdgePoisson T hT n false s + b * tailActualEdgePoisson T hT n true s) := by
  let V : ℝ → ℝ := fun s => a * tailActualEdgePoisson T hT n false s +
    b * tailActualEdgePoisson T hT n true s
  have hV : Continuous V :=
    (continuous_const.mul ((tailActualEdgePoisson_spec hT n).differentiable false).continuous).add
      (continuous_const.mul ((tailActualEdgePoisson_spec hT n).differentiable true).continuous)
  have h := tailActualEdge_mass_change hT n (hF.comp hV)
    ⟨le_rfl, (tailActualEdge_order hT n).le⟩ ⟨(tailActualEdge_order hT n).le, le_rfl⟩
  simpa only [tailActualEdgeChart_left, tailActualEdgeChart_right, Function.comp_apply, V,
    tailActualEdgeInterpolation, tailActualEdgePoissonPhysical_apply] using h.symm

theorem tailActualEdgePoisson_nonneg {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) (right : Bool) {s : ℝ}
    (hs : s ∈ Icc 0 (tailActualEdgeLength T n)) : 0 ≤ tailActualEdgePoisson T hT n right s :=
  (tailActualEdgeAffineHeight_bounds hT n right hs).1.trans
    ((tailActualEdgePoisson_spec hT n).bounds right s hs).1

theorem tailActualEdgePoisson_le_two_height {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (n : ℕ) (right : Bool) {s : ℝ}
    (hs : s ∈ Icc 0 (tailActualEdgeLength T n)) :
    tailActualEdgePoisson T hT n right s ≤ 2 * tailActualEdgeAffineHeight T n right s := by
  have hi : 1 / (1 - T.η) ≤ 2 :=
    (div_le_iff₀ (sub_pos.mpr hT.2.2.2.2.2.1)).mpr (by linarith only [hη])
  calc
    tailActualEdgePoisson T hT n right s ≤ tailActualEdgeAffineHeight T n right s / (1 - T.η) :=
      (tailActualEdgePoisson_bounds_eta hT n right hs).2
    _ = (1 / (1 - T.η)) * tailActualEdgeAffineHeight T n right s := by ring
    _ ≤ 2 * tailActualEdgeAffineHeight T n right s :=
      mul_le_mul_of_nonneg_right hi (tailActualEdgeAffineHeight_bounds hT n right hs).1

theorem tailActualEdgePoisson_sq_le_pairing {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (n : ℕ) (right : Bool) {s : ℝ}
    (hs : s ∈ Icc 0 (tailActualEdgeLength T n)) :
    tailActualEdgePoisson T hT n right s ^ 2 ≤
      2 * tailActualEdgeAffineHeight T n right s * tailActualEdgePoisson T hT n right s := by
  simpa only [pow_two] using mul_le_mul_of_nonneg_right
    (tailActualEdgePoisson_le_two_height hT hη n right hs) (tailActualEdgePoisson_nonneg hT n right hs)

theorem tailActualEdgePairing_le_two_mass {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K) (n : ℕ) (right : Bool) :
    tailActualEdgePairing T hT n right 0 (tailActualEdgeLength T n) ≤
      2 * (if right then tailMass T (n + 1) else tailMass T n) := by
  have hf := tail_poisson_factors_small hT.2.2.2.2.1.le hη hK
  cases right
  · exact (tailActualEdgePairing_left_bounds hT n).2.trans
      (mul_le_mul_of_nonneg_right (hf.2.1.trans (by norm_num)) (tailMass_pos hT n).le)
  · exact (tailActualEdgePairing_right_bounds hT n).2.trans
      (mul_le_mul_of_nonneg_right (hf.2.2.1.trans (by norm_num)) (tailMass_pos hT (n + 1)).le)

/-- Both Poisson squares are controlled by the mass at their respective endpoint. -/
theorem tailActualEdgePoisson_sq_integral_le {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K) (n : ℕ) (right : Bool) :
    (∫ s in 0..tailActualEdgeLength T n,
      tailActualEdgeWeight T hT n s * tailActualEdgePoisson T hT n right s ^ 2) ≤
      4 * (if right then tailMass T (n + 1) else tailMass T n) := by
  have hV := ((tailActualEdgePoisson_spec hT n).differentiable right).continuous
  have hw := tailActualEdgeWeight_continuousOn hT n
  have hP := (hw.mul (tailActualEdgeAffineHeight_continuous T n right).continuousOn).mul hV.continuousOn
  have hi := intervalIntegral.integral_mono_on (tailActualEdgeLength_pos hT n).le
    ((hw.mul (hV.pow 2).continuousOn).intervalIntegrable_of_Icc (μ := volume)
      (tailActualEdgeLength_pos hT n).le)
    ((hP.intervalIntegrable_of_Icc (μ := volume) (tailActualEdgeLength_pos hT n).le).const_mul (2 : ℝ))
    (fun s hs => calc
      tailActualEdgeWeight T hT n s * tailActualEdgePoisson T hT n right s ^ 2 ≤
          tailActualEdgeWeight T hT n s *
            (2 * tailActualEdgeAffineHeight T n right s * tailActualEdgePoisson T hT n right s) :=
        mul_le_mul_of_nonneg_left (tailActualEdgePoisson_sq_le_pairing hT hη n right hs)
          (tailActualEdgeWeight_pos hT n s).le
      _ = 2 * (tailActualEdgeWeight T hT n s * tailActualEdgeAffineHeight T n right s *
          tailActualEdgePoisson T hT n right s) := by ring)
  rw [intervalIntegral.integral_const_mul] at hi
  calc
    (∫ s in 0..tailActualEdgeLength T n,
        tailActualEdgeWeight T hT n s * tailActualEdgePoisson T hT n right s ^ 2) ≤
        2 * tailActualEdgePairing T hT n right 0 (tailActualEdgeLength T n) := hi
    _ ≤ 2 * (2 * (if right then tailMass T (n + 1) else tailMass T n)) :=
      mul_le_mul_of_nonneg_left (tailActualEdgePairing_le_two_mass hT hη hK n right) (by norm_num)
    _ = 4 * (if right then tailMass T (n + 1) else tailMass T n) := by ring

/-- The weighted square integral of the actual physical interpolant. -/
theorem tailActualEdgeInterpolation_sq_integral_le {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K) (n : ℕ) (a b : ℝ) :
    (∫ x in T.node n..T.node (n + 1), T.p x * tailActualEdgeInterpolation T hT n a b x ^ 2) ≤
      8 * (tailMass T n * a ^ 2 + tailMass T (n + 1) * b ^ 2) := by
  have h₀ := ((tailActualEdgePoisson_spec hT n).differentiable false).continuous
  have h₁ := ((tailActualEdgePoisson_spec hT n).differentiable true).continuous
  have hw := tailActualEdgeWeight_continuousOn hT n
  have hi₀ := (hw.mul (h₀.pow 2).continuousOn).intervalIntegrable_of_Icc (μ := volume)
    (tailActualEdgeLength_pos hT n).le
  have hi₁ := (hw.mul (h₁.pow 2).continuousOn).intervalIntegrable_of_Icc (μ := volume)
    (tailActualEdgeLength_pos hT n).le
  have hcomb : Continuous (fun s => a * tailActualEdgePoisson T hT n false s +
      b * tailActualEdgePoisson T hT n true s) :=
    (continuous_const.mul h₀).add (continuous_const.mul h₁)
  have hi := intervalIntegral.integral_mono_on (tailActualEdgeLength_pos hT n).le
    ((hw.mul (hcomb.pow 2).continuousOn).intervalIntegrable_of_Icc (μ := volume)
      (tailActualEdgeLength_pos hT n).le)
    ((hi₀.const_mul (2 * a ^ 2)).add (hi₁.const_mul (2 * b ^ 2)))
    (fun s hs => calc
      tailActualEdgeWeight T hT n s *
          (a * tailActualEdgePoisson T hT n false s + b * tailActualEdgePoisson T hT n true s) ^ 2 ≤
          tailActualEdgeWeight T hT n s * (2 *
            ((a * tailActualEdgePoisson T hT n false s) ^ 2 +
              (b * tailActualEdgePoisson T hT n true s) ^ 2)) :=
        mul_le_mul_of_nonneg_left add_sq_le (tailActualEdgeWeight_pos hT n s).le
      _ = (2 * a ^ 2) * (tailActualEdgeWeight T hT n s * tailActualEdgePoisson T hT n false s ^ 2) +
          (2 * b ^ 2) * (tailActualEdgeWeight T hT n s * tailActualEdgePoisson T hT n true s ^ 2) := by ring)
  rw [intervalIntegral.integral_add (hi₀.const_mul (2 * a ^ 2)) (hi₁.const_mul (2 * b ^ 2))] at hi
  simp only [intervalIntegral.integral_const_mul] at hi
  calc
    (∫ x in T.node n..T.node (n + 1), T.p x * tailActualEdgeInterpolation T hT n a b x ^ 2) =
        ∫ s in 0..tailActualEdgeLength T n, tailActualEdgeWeight T hT n s *
          (a * tailActualEdgePoisson T hT n false s + b * tailActualEdgePoisson T hT n true s) ^ 2 :=
      tailActualEdgeInterpolation_integral hT n a b (continuous_id.pow 2)
    _ ≤ (2 * a ^ 2) * (∫ s in 0..tailActualEdgeLength T n,
          tailActualEdgeWeight T hT n s * tailActualEdgePoisson T hT n false s ^ 2) +
        (2 * b ^ 2) * (∫ s in 0..tailActualEdgeLength T n,
          tailActualEdgeWeight T hT n s * tailActualEdgePoisson T hT n true s ^ 2) := hi
    _ ≤ (2 * a ^ 2) * (4 * tailMass T n) + (2 * b ^ 2) * (4 * tailMass T (n + 1)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (tailActualEdgePoisson_sq_integral_le hT hη hK n false)
          (mul_nonneg (by norm_num) (sq_nonneg a)))
        (mul_le_mul_of_nonneg_left (tailActualEdgePoisson_sq_integral_le hT hη hK n true)
          (mul_nonneg (by norm_num) (sq_nonneg b)))
    _ = 8 * (tailMass T n * a ^ 2 + tailMass T (n + 1) * b ^ 2) := by ring

/-- A first-power Poisson bound on any resistance subinterval. -/
theorem tailActualEdgePoisson_integral_le_on {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (n : ℕ) (right : Bool) {l r high : ℝ}
    (hlr : l ≤ r) (hsub : Icc l r ⊆ Icc 0 (tailActualEdgeLength T n))
    (hh : ∀ s ∈ Icc l r, tailActualEdgeAffineHeight T n right s ≤ high) :
    (∫ s in l..r, tailActualEdgeWeight T hT n s * tailActualEdgePoisson T hT n right s) ≤
      (2 * high) * ∫ s in l..r, tailActualEdgeWeight T hT n s := by
  have hw := (tailActualEdgeWeight_continuousOn hT n).mono hsub
  have hV := ((tailActualEdgePoisson_spec hT n).differentiable right).continuous
  have hi := intervalIntegral.integral_mono_on hlr
    ((hw.mul hV.continuousOn).intervalIntegrable_of_Icc (μ := volume) hlr)
    ((hw.intervalIntegrable_of_Icc (μ := volume) hlr).const_mul (2 * high))
    (fun s hs => calc
      tailActualEdgeWeight T hT n s * tailActualEdgePoisson T hT n right s ≤
          tailActualEdgeWeight T hT n s * (2 * tailActualEdgeAffineHeight T n right s) :=
        mul_le_mul_of_nonneg_left (tailActualEdgePoisson_le_two_height hT hη n right (hsub hs))
          (tailActualEdgeWeight_pos hT n s).le
      _ ≤ tailActualEdgeWeight T hT n s * (2 * high) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hh s hs) (by norm_num))
          (tailActualEdgeWeight_pos hT n s).le
      _ = (2 * high) * tailActualEdgeWeight T hT n s := mul_comm _ _)
  rwa [intervalIntegral.integral_const_mul] at hi

theorem tailActualEdge_weighted_inner_ratio_le {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) :
    tailMass T n * (tailInnerResistance T n / tailActualEdgeLength T n) ≤
      (T.η / T.K) * tailMass T (n + 1) := by
  calc
    tailMass T n * (tailInnerResistance T n / tailActualEdgeLength T n) ≤
        tailMass T n * (tailInnerResistance T n / tailResistance T n) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (tailInnerResistance_pos hT n).le (tailResistance_pos hT n)
          (le_add_of_nonneg_left (tailInnerResistance_pos hT n).le)) (tailMass_pos hT n).le
    _ ≤ T.η * tailMass T (n + 1) / T.K := deepTail_weighted_inner_resistance_ratio_le hT n
    _ = (T.η / T.K) * tailMass T (n + 1) := by ring

/-- Both Poisson first moments are controlled by their own endpoint mass. -/
theorem tailActualEdgePoisson_integral_le {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (n : ℕ) (right : Bool) :
    (∫ s in 0..tailActualEdgeLength T n,
      tailActualEdgeWeight T hT n s * tailActualEdgePoisson T hT n right s) ≤
      4 * (if right then tailMass T (n + 1) else tailMass T n) := by
  have hm := tailActualEdgePoisson_integral_le_on hT hη n right
    (high := if right then tailInnerResistance T n / tailActualEdgeLength T n else 1)
    (tailInnerResistance_pos hT n).le (tailActualEdge_mass_subset hT n)
    (fun s hs => (tailActualEdgeAffineHeight_mass_bounds hT n right hs).2)
  rw [tailActualEdgeWeight_mass] at hm
  have hg := tailActualEdgePoisson_integral_le_on hT hη n right
    (l := tailInnerResistance T n) (r := tailActualEdgeLength T n) (high := 1)
    (le_add_of_nonneg_right (tailResistance_pos hT n).le) (tailActualEdge_gap_subset hT n)
    (fun s hs => (tailActualEdgeAffineHeight_bounds hT n right (tailActualEdge_gap_subset hT n hs)).2)
  rw [tailActualEdgeWeight_gapMass, mul_one] at hg
  have hc := (tailActualEdgeWeight_continuousOn hT n).mul
    ((tailActualEdgePoisson_spec hT n).differentiable right).continuous.continuousOn
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (a := 0) (b := tailInnerResistance T n) (c := tailActualEdgeLength T n)
    ((hc.mono (tailActualEdge_mass_subset hT n)).intervalIntegrable_of_Icc (μ := volume)
      (tailInnerResistance_pos hT n).le)
    ((hc.mono (tailActualEdge_gap_subset hT n)).intervalIntegrable_of_Icc (μ := volume)
      (le_add_of_nonneg_right (tailResistance_pos hT n).le))
  simp only [Pi.mul_apply] at hsplit
  rw [← hsplit]
  cases right
  · simp only [Bool.false_eq_true, ite_false, mul_one] at hm ⊢
    have hν : tailGapMass T n ≤ tailMass T n :=
      (deepTail_gap_mass_le_left hT n).trans
        ((mul_le_mul_of_nonneg_right hT.2.2.2.2.2.1.le (tailMass_pos hT n).le).trans_eq (one_mul _))
    exact (add_le_add hm hg).trans (by nlinarith only [hν])
  · simp only [ite_true] at hm ⊢
    have hν : tailGapMass T n ≤ tailMass T (n + 1) :=
      (deepTail_gap_mass_le_right hT n).trans
        ((mul_le_mul_of_nonneg_right hT.2.2.2.2.2.1.le (tailMass_pos hT (n + 1)).le).trans_eq
          (one_mul _))
    have hratio : T.η / T.K ≤ 1 := (sub_pos.mp (tailActualEdge_one_sub_ratio_pos hT)).le
    have hshift : tailMass T n * (tailInnerResistance T n / tailActualEdgeLength T n) ≤
        tailMass T (n + 1) :=
      (tailActualEdge_weighted_inner_ratio_le hT n).trans
        ((mul_le_mul_of_nonneg_right hratio (tailMass_pos hT (n + 1)).le).trans_eq (one_mul _))
    exact (add_le_add hm hg).trans (by nlinarith only [hν, hshift])

/-- The weighted absolute integral of the actual physical interpolant. -/
theorem tailActualEdgeInterpolation_abs_integral_le {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (n : ℕ) (a b : ℝ) :
    (∫ x in T.node n..T.node (n + 1), T.p x * |tailActualEdgeInterpolation T hT n a b x|) ≤
      4 * (tailMass T n * |a| + tailMass T (n + 1) * |b|) := by
  have h₀ := ((tailActualEdgePoisson_spec hT n).differentiable false).continuous
  have h₁ := ((tailActualEdgePoisson_spec hT n).differentiable true).continuous
  have hw := tailActualEdgeWeight_continuousOn hT n
  have hi₀ := (hw.mul h₀.continuousOn).intervalIntegrable_of_Icc (μ := volume)
    (tailActualEdgeLength_pos hT n).le
  have hi₁ := (hw.mul h₁.continuousOn).intervalIntegrable_of_Icc (μ := volume)
    (tailActualEdgeLength_pos hT n).le
  have hcomb : Continuous (fun s => a * tailActualEdgePoisson T hT n false s +
      b * tailActualEdgePoisson T hT n true s) :=
    (continuous_const.mul h₀).add (continuous_const.mul h₁)
  have hi := intervalIntegral.integral_mono_on (tailActualEdgeLength_pos hT n).le
    ((hw.mul hcomb.abs.continuousOn).intervalIntegrable_of_Icc (μ := volume)
      (tailActualEdgeLength_pos hT n).le)
    ((hi₀.const_mul |a|).add (hi₁.const_mul |b|)) (fun s hs => by
      have habs : |a * tailActualEdgePoisson T hT n false s + b * tailActualEdgePoisson T hT n true s| ≤
          |a| * tailActualEdgePoisson T hT n false s + |b| * tailActualEdgePoisson T hT n true s := by
        calc
          _ ≤ |a * tailActualEdgePoisson T hT n false s| + |b * tailActualEdgePoisson T hT n true s| :=
            abs_add_le _ _
          _ = _ := by
            rw [abs_mul, abs_mul, abs_of_nonneg (tailActualEdgePoisson_nonneg hT n false hs),
              abs_of_nonneg (tailActualEdgePoisson_nonneg hT n true hs)]
      calc
        tailActualEdgeWeight T hT n s *
            |a * tailActualEdgePoisson T hT n false s + b * tailActualEdgePoisson T hT n true s| ≤
            tailActualEdgeWeight T hT n s *
              (|a| * tailActualEdgePoisson T hT n false s + |b| * tailActualEdgePoisson T hT n true s) :=
          mul_le_mul_of_nonneg_left habs (tailActualEdgeWeight_pos hT n s).le
        _ = |a| * (tailActualEdgeWeight T hT n s * tailActualEdgePoisson T hT n false s) +
            |b| * (tailActualEdgeWeight T hT n s * tailActualEdgePoisson T hT n true s) := by ring)
  rw [intervalIntegral.integral_add (hi₀.const_mul |a|) (hi₁.const_mul |b|)] at hi
  simp only [intervalIntegral.integral_const_mul] at hi
  calc
    (∫ x in T.node n..T.node (n + 1), T.p x * |tailActualEdgeInterpolation T hT n a b x|) =
        ∫ s in 0..tailActualEdgeLength T n, tailActualEdgeWeight T hT n s *
          |a * tailActualEdgePoisson T hT n false s + b * tailActualEdgePoisson T hT n true s| :=
      tailActualEdgeInterpolation_integral hT n a b continuous_abs
    _ ≤ |a| * (∫ s in 0..tailActualEdgeLength T n,
          tailActualEdgeWeight T hT n s * tailActualEdgePoisson T hT n false s) +
        |b| * (∫ s in 0..tailActualEdgeLength T n,
          tailActualEdgeWeight T hT n s * tailActualEdgePoisson T hT n true s) := hi
    _ ≤ |a| * (4 * tailMass T n) + |b| * (4 * tailMass T (n + 1)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (tailActualEdgePoisson_integral_le hT hη n false) (abs_nonneg a))
        (mul_le_mul_of_nonneg_left (tailActualEdgePoisson_integral_le hT hη n true) (abs_nonneg b))
    _ = 4 * (tailMass T n * |a| + tailMass T (n + 1) * |b|) := by ring

end ContinuousFlexibility.Radial
