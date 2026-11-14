module

public import ContinuousFlexibility.Scalar.WeightedReferenceCoefficients
public import ContinuousFlexibility.Radial.ScaleSlowVariation

/-!
# Comparing the actual material coordinate with the reference cell index

Both endpoints use the prescribed material coordinate. Its difference from
the reference index is uniformly bounded on every cell near an endpoint.
The estimate keeps all three actual weight formulas, including the material
weight used in the fixed-loss Schur argument.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

/-- One endpoint-distance argument treats both collars and retains the
bounded additive coordinate error, not just a coarse proportional bound. -/
theorem n05_materialCell_endpoint_coordinates {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) :
    ∃ δ A : ℝ, 0 < δ ∧ 0 < A ∧ ∀ m r,
      r ∈ Ioo D.a D.b → r ∈ D.cells m → endpointDistance D r < δ →
      ∃ x : ℝ, 0 ≤ x ∧ |x - (D.cellIndex m : ℝ)| ≤ A ∧
        T.H r = materialH x ∧ T.E0 r = materialE0 x ∧ T.M r = materialM x := by
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hend, _, _, _, _, _, _, hcomp⟩ := hdata
  obtain ⟨d0, δ0, hd0, hδ0, hδbound, hleft, hright⟩ := hend
  obtain ⟨cellError, _, hcellError, _, hcmp⟩ := hcomp
  refine ⟨min δ0 1, cellError + Real.sqrt |Real.log d0| + 1,
    lt_min hδ0 zero_lt_one, by positivity, ?_⟩
  intro m r hr hrm hnear
  let d : ℝ := endpointDistance D r
  let x : ℝ := endpointX d0 d
  let x1 : ℝ := endpointX 1 d
  have hd : 0 < d := lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)
  have hdδ0 : d < δ0 := hnear.trans_le (min_le_left _ _)
  have hd1 : d < 1 := hnear.trans_le (min_le_right _ _)
  have hdd0 : d < d0 := hdδ0.trans (hδbound.trans_le (min_le_left _ _))
  have hscale : |x - x1| ≤ Real.sqrt |Real.log d0| :=
    abs_endpointX_scale_sub_le hd0 hd hdd0 hd1
  have hcell : |x1 - (D.cellIndex m : ℝ)| ≤ cellError := by
    simpa only [x1, d] using (hcmp m r hrm).1
  have hclose : |x - (D.cellIndex m : ℝ)| ≤
      cellError + Real.sqrt |Real.log d0| + 1 := by
    calc
      _ ≤ |x - x1| + |x1 - (D.cellIndex m : ℝ)| := abs_sub_le _ _ _
      _ ≤ Real.sqrt |Real.log d0| + cellError := add_le_add hscale hcell
      _ ≤ _ := by linarith
  refine ⟨x, Real.sqrt_nonneg _, hclose, ?_⟩
  dsimp only [x, d, endpointDistance]
  by_cases hside : r - D.a ≤ D.b - r
  · rw [min_eq_left hside]
    have hn : r - D.a < δ0 := by
      simpa only [d, endpointDistance, min_eq_left hside] using hdδ0
    have h := hleft r ⟨hr.1, by linarith only [hn]⟩
    exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
  · have hside' : D.b - r ≤ r - D.a := le_of_not_ge hside
    rw [min_eq_right hside']
    have hn : D.b - r < δ0 := by
      simpa only [d, endpointDistance, min_eq_right hside'] using hdδ0
    have h := hright r ⟨by linarith only [hn], hr.2⟩
    exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

/-- A bounded shift changes the cubic endpoint exponent by at most a
quadratic coefficient factor. -/
theorem n05_cube_shift_bound {x n A : ℝ} (hx : 0 ≤ x) (hn : 0 ≤ n)
    (hA : 0 ≤ A) (hshift : |x - n| ≤ A) :
    |x ^ 3 - n ^ 3| ≤ 6 * A * (A ^ 2 + 1) * (n ^ 2 + 1) := by
  have hxA : x ≤ n + A := by linarith only [(abs_le.mp hshift).2]
  have hnA : n ≤ n + A := le_add_of_nonneg_right hA
  have hsum : x ^ 2 + x * n + n ^ 2 ≤ 3 * (n + A) ^ 2 := by
    have hxx : x ^ 2 ≤ (n + A) ^ 2 := (sq_le_sq₀ hx (by positivity)).mpr hxA
    have hnn : n ^ 2 ≤ (n + A) ^ 2 := (sq_le_sq₀ hn (by positivity)).mpr hnA
    have hxn : x * n ≤ (n + A) * (n + A) := mul_le_mul hxA hnA hn (by positivity)
    nlinarith only [hxx, hnn, hxn]
  have hquad : 0 ≤ x ^ 2 + x * n + n ^ 2 :=
    add_nonneg (add_nonneg (sq_nonneg x) (mul_nonneg hx hn)) (sq_nonneg n)
  calc
    |x ^ 3 - n ^ 3| = |x - n| * (x ^ 2 + x * n + n ^ 2) := by
      rw [show x ^ 3 - n ^ 3 = (x - n) * (x ^ 2 + x * n + n ^ 2) by ring,
        abs_mul, abs_of_nonneg hquad]
    _ ≤ A * (3 * (n + A) ^ 2) := mul_le_mul hshift hsum hquad hA
    _ ≤ 6 * A * (n ^ 2 + A ^ 2) := by
      have hsq : (n + A) ^ 2 ≤ 2 * (n ^ 2 + A ^ 2) := by nlinarith [sq_nonneg (n - A)]
      nlinarith only [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 3 * A)]
    _ ≤ _ := by
      have hterm : n ^ 2 + A ^ 2 ≤ (A ^ 2 + 1) * (n ^ 2 + 1) := by
        nlinarith only [mul_nonneg (sq_nonneg A) (sq_nonneg n)]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hterm (by positivity : 0 ≤ 6 * A)

end ContinuousFlexibility.Statements
