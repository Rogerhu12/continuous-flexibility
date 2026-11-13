import ContinuousFlexibility.Analysis.PositiveReferenceFiniteRadialJets
import ContinuousFlexibility.Analysis.EndpointFiberPolynomialMargins

/-!
# A displayed width for the actual reference Taylor data

The coordinate and height use the same finite radial Taylor slices as
the qualitative reference construction. A single displayed width makes
both slices positive near their endpoints and bounds the endpoint mass.
Every reciprocal cost is stated in the actual finite data; no estimate
for a qualitatively selected continuity radius is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

def positiveReferenceTaylorWidth (n : ℕ) (l r κ M : ℝ) : ℝ :=
  prescribedEndpointWidth (n + 1) (r - l) 1 κ M
    (M + ((n + 1 : ℕ) : ℝ) * M) 1

theorem positiveReferenceTaylorWidth_margins (n : ℕ) {l r κ M : ℝ}
    (hlr : l < r) (hκ : 0 < κ) (hM : 0 ≤ M) :
    let δ := positiveReferenceTaylorWidth n l r κ M
    0 < δ ∧ δ ≤ 1 ∧ 4 * δ ≤ r - l ∧ 2 * δ < r - l ∧
      ((n + 2 : ℕ) : ℝ) * M * δ ≤ κ / 2 ∧
      2 * (M + ((n + 1 : ℕ) : ℝ) * M) * δ ≤ 1 / 2 ∧
      δ⁻¹ ≤ 4 + 4 / (r - l) +
        (4 * ((n + 2 : ℕ) : ℝ) * (M + 1)) / κ +
          8 * (M + ((n + 1 : ℕ) : ℝ) * M + 1) := by
  have hS : 0 ≤ M + ((n + 1 : ℕ) : ℝ) * M := by positivity
  obtain ⟨hδ, _, hδone, hgap, hsmall, hmass⟩ :=
    prescribedEndpointWidth_margins (n + 1) (sub_pos.mpr hlr)
      zero_lt_one hκ hM hS zero_lt_one
  have hfour : 4 * positiveReferenceTaylorWidth n l r κ M ≤ r - l := by
    have hwidth : positiveReferenceTaylorWidth n l r κ M ≤ (r - l) / 4 := by
      exact (min_le_right _ _).trans (min_le_left _ _)
    linarith only [hwidth]
  have hinv := prescribedEndpointWidth_inv_le (n + 1) (sub_pos.mpr hlr)
    zero_lt_one hκ hM hS zero_lt_one
  refine ⟨hδ, hδone, hfour, hgap, hsmall, hmass, ?_⟩
  change (prescribedEndpointWidth (n + 1) (r - l) 1 κ M
    (M + ((n + 1 : ℕ) : ℝ) * M) 1)⁻¹ ≤ _
  calc
    _ ≤ 2 + 4 / (r - l) + 2 / 1 +
        (4 * ((n + 2 : ℕ) : ℝ) * (M + 1)) / κ +
          8 * (M + ((n + 1 : ℕ) : ℝ) * M + 1) / 1 := hinv
    _ = _ := by ring

/-- The same scalar proof handles either endpoint and both actual
Taylor slices. Only their displayed finite root coefficients enter. -/
theorem radialEndpointTaylorSlice_collar_bounds
    (n : ℕ) {f g : PolarPoint → ℝ} {c x δ κ M : ℝ}
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hM : 0 ≤ M) (hx : |x - c| ≤ δ)
    (hflow : κ ≤ radialBoundaryJet f c 1 0)
    (hheight : κ ≤ radialBoundaryJet g c 0 0)
    (hf : ∀ j, 1 ≤ j → j ≤ n + 1 → |radialBoundaryJet f c j 0| ≤ M)
    (hg : ∀ j, j ≤ n + 1 → |radialBoundaryJet g c j 0| ≤ M)
    (hsmall : ((n + 2 : ℕ) : ℝ) * M * δ ≤ κ / 2) :
    κ / 2 ≤ deriv (radialEndpointTaylorSlice (n + 1) c f) x ∧
      |deriv (radialEndpointTaylorSlice (n + 1) c f) x| ≤
        M + ((n + 1 : ℕ) : ℝ) * M ∧
      κ / 2 ≤ radialEndpointTaylorSlice (n + 1) c g x ∧
      |radialEndpointTaylorSlice (n + 1) c g x| ≤ 2 * M := by
  have hstep : ((n + 1 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show n + 1 ≤ n + 2 by omega)
  have hs : ((n + 1 : ℕ) : ℝ) * M * δ ≤ κ / 2 :=
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hstep hM) hδ).trans hsmall
  have hslope := boundaryTaylorPolynomial_radial_slope_bounds
    (n := n) (A := radialBoundaryJet f c) (θ := 0)
    hδ hδone hM hx hflow hf hs
  have hdiff := (abs_boundaryTaylorPolynomial_sub_zero_le
    (n := n + 1) (A := radialBoundaryJet g c) (θ := 0)
    hδ hδone hM hx (fun j _ hj => hg j hj)).trans hsmall
  have hκM : κ ≤ M := hheight.trans ((le_abs_self _).trans (hg 0 (by omega)))
  have htriangle := abs_add_le
    (boundaryTaylorPolynomial (n + 1) c (radialBoundaryJet g c) (x, 0) -
      radialBoundaryJet g c 0 0) (radialBoundaryJet g c 0 0)
  rw [sub_add_cancel] at htriangle
  change κ / 2 ≤ deriv
      (fun t => boundaryTaylorPolynomial (n + 1) c (radialBoundaryJet f c) (t, 0)) x ∧
    |deriv (fun t => boundaryTaylorPolynomial (n + 1) c
      (radialBoundaryJet f c) (t, 0)) x| ≤ _ ∧
    κ / 2 ≤ boundaryTaylorPolynomial (n + 1) c (radialBoundaryJet g c) (x, 0) ∧
    |boundaryTaylorPolynomial (n + 1) c (radialBoundaryJet g c) (x, 0)| ≤ 2 * M
  refine ⟨hslope.1, hslope.2, ?_, ?_⟩
  · have hlo := (abs_le.mp hdiff).1
    linarith only [hlo, hheight]
  · have hzero := hg 0 (by omega)
    linarith only [htriangle, hdiff, hzero, hκM, hM]

/-- The displayed width has a quadratic reciprocal cost once the
finite jets, reciprocal endpoint lower bound and reciprocal gap have
one common numerical envelope. The envelope is not a material claim. -/
theorem positiveReferenceTaylorWidth_polynomial_inv_le (n : ℕ)
    {l r κ M U : ℝ} (hlr : l < r) (hκ : 0 < κ) (hM : 0 ≤ M)
    (hU : 1 ≤ U) (hMU : M ≤ U) (hκU : κ⁻¹ ≤ U) (hgapU : (r - l)⁻¹ ≤ U) :
    (positiveReferenceTaylorWidth n l r κ M)⁻¹ ≤
      (24 + 16 * ((n + 2 : ℕ) : ℝ)) * U ^ 2 := by
  let N : ℝ := ((n + 2 : ℕ) : ℝ)
  have hN : 1 ≤ N := by
    change (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ)
    exact_mod_cast (show 1 ≤ n + 2 by omega)
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hU2 : U ≤ U ^ 2 := by nlinarith only [hU, sq_nonneg (U - 1)]
  have hM1 : M + 1 ≤ 2 * U := by linarith only [hMU, hU]
  have hS : M + ((n + 1 : ℕ) : ℝ) * M = N * M := by
    dsimp only [N]
    push_cast
    ring
  have hS1 : M + ((n + 1 : ℕ) : ℝ) * M + 1 ≤ (N + 1) * U := by
    rw [hS]
    have h := mul_le_mul_of_nonneg_left hMU hN0
    nlinarith only [h, hU]
  have hjet : (4 * N * (M + 1)) / κ ≤ 8 * N * U ^ 2 := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ (4 * N * (2 * U)) * U :=
        mul_le_mul (mul_le_mul_of_nonneg_left hM1 (by positivity)) hκU
          (inv_nonneg.mpr hκ.le) (by positivity)
      _ = _ := by ring
  have hmass : 8 * (M + ((n + 1 : ℕ) : ℝ) * M + 1) ≤
      8 * (N + 1) * U ^ 2 := by
    calc
      _ ≤ 8 * ((N + 1) * U) := mul_le_mul_of_nonneg_left hS1 (by norm_num)
      _ ≤ 8 * ((N + 1) * U ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hU2 (by positivity)) (by norm_num)
      _ = _ := by ring
  have hgap : 4 / (r - l) ≤ 4 * U ^ 2 := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (hgapU.trans hU2) (by norm_num)
  have hconst : (4 : ℝ) ≤ 4 * U ^ 2 := by nlinarith only [hU.trans hU2]
  have hraw := (positiveReferenceTaylorWidth_margins n hlr hκ hM).2.2.2.2.2.2
  change (positiveReferenceTaylorWidth n l r κ M)⁻¹ ≤ (24 + 16 * N) * U ^ 2
  change (positiveReferenceTaylorWidth n l r κ M)⁻¹ ≤
    4 + 4 / (r - l) + (4 * N * (M + 1)) / κ +
      8 * (M + ((n + 1 : ℕ) : ℝ) * M + 1) at hraw
  nlinarith only [hraw, hjet, hmass, hgap, hconst, sq_nonneg U]

end ContinuousFlexibility.Analysis
