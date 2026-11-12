import ContinuousFlexibility.Radial.ZeroModeWeightGeometry
import ContinuousFlexibility.Radial.ReferenceWeightedProduct

/-!
# The endpoint singularity is controlled by the actual output weight

For every positive lower bound on the attenuation exponent, the frozen
output weights dominate the inverse square of the distance to the two
endpoints. This is a consequence of the stated coefficient absorption
and distance bounds, without using trace scaffolds or spectral data.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory
open ContinuousFlexibility.Statements

theorem zeroMode_endpoint_inv_sq_le_outputWeight
    {D : ReferenceData} {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C)
    {γlo : ℝ} (hγlo : 0 < γlo) (M : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ γ : ℝ, γlo ≤ γ →
      ∀ m : ℕ, ∀ r ∈ D.cells m,
      (min (r - D.a) (D.b - r))⁻¹ ^ 2 ≤
        K * exp (2 * (-M) * radialQ (D.cellIndex m) +
          2 * γ * radialS (D.cellIndex m)) := by
  rcases hD with ⟨_, _, hC, _, _, _, hdist, _, _, _, _, habsorb, _⟩
  let α : ℝ := 2 * |M| + 1
  have hα : 0 < α := by dsimp [α]; positivity
  obtain ⟨L, hL, hscale⟩ := habsorb α 4 (2 * γlo) hα (by norm_num) (by linarith)
  have hC0 := hC 0
  refine ⟨(C 0) ^ 2 * (exp 4 * L), by positivity, ?_⟩
  intro γ hγ m r hr
  let n : ℕ := D.cellIndex m
  let δ : ℝ := min (r - D.a) (D.b - r)
  let z : ℝ := ((n : ℝ) + 1) ^ 2
  have hd : (C 0)⁻¹ * exp (-z) ≤ δ := (hdist m r hr).1
  have hdpos : 0 < δ :=
    (mul_pos (inv_pos.mpr hC0) (exp_pos (-z))).trans_le hd
  have hi : δ⁻¹ ≤ C 0 * exp z := by
    have h := one_div_le_one_div_of_le
      (mul_pos (inv_pos.mpr hC0) (exp_pos (-z))) hd
    simpa only [one_div, mul_inv_rev, inv_inv, ← exp_neg, neg_neg, mul_comm] using h
  have hsq : δ⁻¹ ^ 2 ≤ (C 0) ^ 2 * exp (2 * z) := by
    calc
      δ⁻¹ ^ 2 ≤ (C 0 * exp z) ^ 2 :=
        (sq_le_sq₀ (inv_nonneg.mpr hdpos.le) (by positivity)).2 hi
      _ = (C 0) ^ 2 * (exp z * exp z) := by ring
      _ = (C 0) ^ 2 * exp (2 * z) := by rw [← exp_add]; congr 2 <;> ring
  have hq := radialQ_nonneg n
  have hS : 0 ≤ radialS n := by unfold radialS; positivity
  have hcoef : 2 * M ≤ α := by
    dsimp [α]
    linarith only [le_abs_self M]
  have hcq := mul_le_mul_of_nonneg_right hcoef hq
  have hz : 2 * z ≤ 4 * (n : ℝ) ^ 2 + 4 := by
    dsimp [z]
    nlinarith only [sq_nonneg ((n : ℝ) - 1)]
  have hpoly :
      2 * z ≤ (4 - 2 * M * radialQ n) +
        (radialQ n * α + 4 * (n : ℝ) ^ 2) := by
    nlinarith only [hz, hcq]
  have hscale' := hscale n
  rw [radialE, ← exp_mul, ← exp_add] at hscale'
  have he :
      exp (2 * z) ≤ (exp 4 * L) *
        exp (2 * (-M) * radialQ n + 2 * γ * radialS n) := by
    calc
      exp (2 * z) ≤
          exp ((4 - 2 * M * radialQ n) + (radialQ n * α + 4 * (n : ℝ) ^ 2)) :=
        exp_le_exp.mpr hpoly
      _ = exp (4 - 2 * M * radialQ n) *
          exp (radialQ n * α + 4 * (n : ℝ) ^ 2) := exp_add _ _
      _ ≤ exp (4 - 2 * M * radialQ n) * (L * exp (2 * γlo * radialS n)) :=
        mul_le_mul_of_nonneg_left hscale' (exp_pos _).le
      _ = (exp 4 * L) * exp (2 * (-M) * radialQ n + 2 * γlo * radialS n) := by
        rw [show 4 - 2 * M * radialQ n = 4 + 2 * (-M) * radialQ n by ring]
        simp only [exp_add]
        ring
      _ ≤ (exp 4 * L) * exp (2 * (-M) * radialQ n + 2 * γ * radialS n) := by
        apply mul_le_mul_of_nonneg_left _ (mul_pos (exp_pos 4) hL).le
        apply exp_le_exp.mpr
        nlinarith only [mul_nonneg (sub_nonneg.mpr hγ) hS]
  change δ⁻¹ ^ 2 ≤ ((C 0) ^ 2 * (exp 4 * L)) *
    exp (2 * (-M) * radialQ n + 2 * γ * radialS n)
  calc
    δ⁻¹ ^ 2 ≤ (C 0) ^ 2 * exp (2 * z) := hsq
    _ ≤ (C 0) ^ 2 * ((exp 4 * L) *
        exp (2 * (-M) * radialQ n + 2 * γ * radialS n)) :=
      mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ = _ := by ring

end ContinuousFlexibility.Radial
