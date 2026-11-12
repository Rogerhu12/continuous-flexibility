import ContinuousFlexibility.Analysis.PositiveReferenceLinearJetEnvelope
import ContinuousFlexibility.Analysis.EndpointTaylorLinearJetEnvelope
import ContinuousFlexibility.Analysis.PositiveReferenceCollarFactory
import ContinuousFlexibility.Analysis.CylinderMixedJetNorms

/-!
# Linear high jets of the actual unit-reference radial collar

The radial derivative of the prescribed root Taylor polynomial removes
its zeroth coefficient. Subtracting the unit reference leaves exactly
one endpoint Taylor correction. Its high data remain linear through
the existing fixed mass normalization and the actual radial primitive.
The polynomial degree and the selected collar width never change with
the requested output order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

def positiveReferenceCollarSlopeData (root : Bool) (A : ℕ → ℝ → ℝ)
    (side : Bool) (j : ℕ) (θ : ℝ) : ℝ :=
  if side = root then A (j + 1) θ - (if j = 0 then 1 else 0) else 0

private theorem boundaryTaylorPolynomial_sub_unit
    (n : ℕ) (c : ℝ) (A : ℕ → ℝ → ℝ) :
    boundaryTaylorPolynomial n c
        (fun j θ => A j θ - (if j = 0 then 1 else 0)) =
      fun p => boundaryTaylorPolynomial n c A p - 1 := by
  have hunit : boundaryTaylorPolynomial n c
      (fun j _ => if j = 0 then (1 : ℝ) else 0) = (fun _ => (1 : ℝ)) := by
    funext p
    unfold boundaryTaylorPolynomial
    rw [Finset.sum_eq_single 0]
    · simp only [↓reduceIte, Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, mul_one]
    · intro j _ hj
      simp only [if_neg hj, zero_div, zero_mul]
    · intro hz
      exact (hz (Finset.mem_range.mpr (Nat.succ_pos n))).elim
  funext p
  calc
    _ = boundaryTaylorPolynomial n c A p -
        boundaryTaylorPolynomial n c (fun j _ => if j = 0 then (1 : ℝ) else 0) p := by
      simp only [boundaryTaylorPolynomial, sub_div, sub_mul, Finset.sum_sub_distrib]
    _ = _ := by rw [hunit]

private theorem radialPartial_boundaryTaylorPolynomial
    {n : ℕ} {A : ℕ → ℝ → ℝ}
    (hA : ∀ j, j ≤ n + 1 → ContDiff ℝ ∞ (A j)) (c : ℝ) :
    radialPartial (boundaryTaylorPolynomial (n + 1) c A) =
      boundaryTaylorPolynomial n c (fun j => A (j + 1)) := by
  funext p
  rcases p with ⟨x, θ⟩
  rw [← deriv_cylinder_radial_slice
    ((contDiff_boundaryTaylorPolynomial hA c).differentiable (by simp)) x θ,
    (hasDerivAt_boundaryTaylorPolynomial_radial n c x θ A).deriv]

theorem positiveReferenceCollarSlopeDeviation_eq_correction
    {n : ℕ} {A : ℕ → ℝ → ℝ}
    (hA : ∀ j, j ≤ n + 1 → ContDiff ℝ ∞ (A j))
    (l r δ : ℝ) (root : Bool) :
    positiveReferenceSlopeDeviation l r δ
        (fun side => radialPartial
          (positiveReferenceCollarField n l r root A (Prod.fst : PolarPoint → ℝ) side)) =
      endpointTaylorCorrection n l r δ (positiveReferenceCollarSlopeData root A) := by
  have hslope (side : Bool) :
      (fun p => radialPartial
          (positiveReferenceCollarField n l r root A (Prod.fst : PolarPoint → ℝ) side) p - 1) =
        boundaryTaylorPolynomial n (if side then r else l)
          (positiveReferenceCollarSlopeData root A side) := by
    by_cases hs : side = root
    · subst side
      have hfield : positiveReferenceCollarField n l r root A
          (Prod.fst : PolarPoint → ℝ) root =
            boundaryTaylorPolynomial (n + 1) (if root then r else l) A := by
        simp only [positiveReferenceCollarField, if_pos rfl, ite_true]
      have hdata : positiveReferenceCollarSlopeData root A root =
          fun j θ => A (j + 1) θ - (if j = 0 then 1 else 0) := by
        funext j θ
        simp only [positiveReferenceCollarSlopeData, if_pos rfl, ite_true]
      rw [hfield, hdata, radialPartial_boundaryTaylorPolynomial hA]
      exact (boundaryTaylorPolynomial_sub_unit n (if root then r else l)
        (fun j => A (j + 1))).symm
    · have hfield : positiveReferenceCollarField n l r root A
          (Prod.fst : PolarPoint → ℝ) side = (Prod.fst : PolarPoint → ℝ) := by
        simp only [positiveReferenceCollarField, if_neg hs]
      have hdata : positiveReferenceCollarSlopeData root A side =
          fun _ _ => (0 : ℝ) := by
        funext j θ
        simp only [positiveReferenceCollarSlopeData, if_neg hs]
      rw [hfield, hdata]
      funext p
      simp only [radialPartial_fst, sub_self, boundaryTaylorPolynomial,
        zero_div, zero_mul, Finset.sum_const_zero]
  funext p
  dsimp only [positiveReferenceSlopeDeviation, endpointTaylorCorrection]
  rw [← congrFun (hslope false) p, ← congrFun (hslope true) p]

/-- The root data of positive radial order enter linearly. The bound
uses the same displayed collar, unit reference, physical mass and width. -/
theorem exists_positiveReferenceCollarCoordinate_linear_jet_envelope (n N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {U B l r δ : ℝ},
      1 ≤ U → 1 ≤ B → 0 < δ → δ ≤ 1 → 4 * δ ≤ r - l → δ⁻¹ ≤ U →
      ∀ (root : Bool) (A : ℕ → ℝ → ℝ),
      (∀ j, j ≤ n + 1 → ContDiff ℝ ∞ (A j)) →
      (∀ j, 1 ≤ j → j ≤ n + 1 → ∀ b, b ≤ N → ∀ θ,
        |iteratedDeriv b (A j) θ| ≤ B) →
      ∀ k, k ≤ N → ∀ p : PolarPoint, p.1 ∈ Icc l r →
        ‖iteratedFDeriv ℝ k
          (fun q => positiveReferenceCollarCoordinate n l r δ l (r - l) root A
            (Prod.fst : PolarPoint → ℝ) q - q.1) p‖ ≤
          C * (1 + (r - l)) * U ^ (2 * N + 1) * B := by
  obtain ⟨CT, hCT, hTaylor⟩ := exists_endpointTaylorCorrection_linear_jet_envelope n N
  obtain ⟨CR, hCR, hRadial⟩ :=
    exists_parameterizedPositiveReferenceCoordinate_linear_jet_envelope N
  have hprod : 1 ≤ CR * CT := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ CR * CT := mul_le_mul hCR hCT zero_le_one (zero_le_one.trans hCR)
  refine ⟨2 * CR * CT, by nlinarith only [hprod], ?_⟩
  intro U B l r δ hU hB hδ hδone hgap hδinv root A hA hjets k hk p hp
  let D := positiveReferenceCollarSlopeData root A
  let V : Bool → PolarPoint → ℝ := fun side => radialPartial
    (positiveReferenceCollarField n l r root A (Prod.fst : PolarPoint → ℝ) side)
  have hV (side : Bool) : ContDiff ℝ ∞ (V side) := by
    apply contDiff_cylinder_radialPartial
    by_cases hs : side = root
    · simpa only [positiveReferenceCollarField, if_pos hs] using
        contDiff_boundaryTaylorPolynomial hA (if side then r else l)
    · simpa only [positiveReferenceCollarField, if_neg hs] using
        (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : PolarPoint → ℝ))
  have hD (side : Bool) (j : ℕ) (hj : j ≤ n) : ContDiff ℝ ∞ (D side j) := by
    change ContDiff ℝ ∞ (fun θ =>
      if side = root then A (j + 1) θ - (if j = 0 then 1 else 0) else 0)
    by_cases hs : side = root
    · simp only [if_pos hs]
      exact (hA (j + 1) (by omega)).sub contDiff_const
    · simp only [if_neg hs]
      exact contDiff_const
  have hDjets (side : Bool) (j : ℕ) (hj : j ≤ n)
      (b : ℕ) (hb : b ≤ N) (θ : ℝ) : |iteratedDeriv b (D side j) θ| ≤ 2 * B := by
    by_cases hs : side = root
    · have he : D side j = fun η => A (j + 1) η - (if j = 0 then 1 else 0) := by
        funext η
        simp only [D, positiveReferenceCollarSlopeData, if_pos hs]
      rw [he, iteratedDeriv_fun_sub
        ((hA (j + 1) (by omega)).contDiffAt.of_le (by simp)) contDiffAt_const]
      have hc : |iteratedDeriv b (fun _ : ℝ => if j = 0 then (1 : ℝ) else 0) θ| ≤ 1 := by
        by_cases hb0 : b = 0
        · simp only [iteratedDeriv_const, if_pos hb0]
          split <;> norm_num
        · simp only [iteratedDeriv_const, if_neg hb0, abs_zero, zero_le_one]
      calc
        _ ≤ |iteratedDeriv b (A (j + 1)) θ| +
            |iteratedDeriv b (fun _ : ℝ => if j = 0 then (1 : ℝ) else 0) θ| := abs_sub _ _
        _ ≤ B + 1 := add_le_add (hjets (j + 1) (by omega) (by omega) b hb θ) hc
        _ ≤ 2 * B := by linarith only [hB]
    · have he : D side j = fun _ => (0 : ℝ) := by
        funext η
        simp only [D, positiveReferenceCollarSlopeData, if_neg hs]
      rw [he, iteratedDeriv_fun_const_zero, abs_zero]
      positivity
  have hBp : 0 ≤ CT * U ^ (N + 1) * (2 * B) :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hCT)
      (pow_nonneg (zero_le_one.trans hU) _)) (by positivity)
  have he : positiveReferenceSlopeDeviation l r δ V = endpointTaylorCorrection n l r δ D :=
    positiveReferenceCollarSlopeDeviation_eq_correction hA l r δ root
  have hE : ContDiff ℝ ∞ (endpointTaylorCorrection n l r δ D) :=
    contDiff_endpointTaylorCorrection hD l r δ
  have hmix (a b : ℕ) (hab : a + b ≤ N) (x : ℝ) (_hx : x ∈ Icc l r) (θ : ℝ) :
      |mixedDerivative a b (positiveReferenceSlopeDeviation l r δ V) (x, θ)| ≤
        CT * U ^ (N + 1) * (2 * B) := by
    rw [he]
    exact (abs_mixedDerivative_le_norm_iteratedFDeriv isOpen_univ hE.contDiffOn
      a b (mem_univ (x, θ))).trans
        (hTaylor hU (by positivity) hδ hδone hδinv l r D hD hDjets (a + b) hab (x, θ))
  have hpow : U ^ N * U ^ (N + 1) = U ^ (2 * N + 1) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ ≤ CR * (1 + (r - l)) * U ^ N * (CT * U ^ (N + 1) * (2 * B)) :=
      hRadial hU hδ hgap hδinv hBp V hV hmix k hk p hp
    _ = (2 * CR * CT) * (1 + (r - l)) * (U ^ N * U ^ (N + 1)) * B := by ring
    _ = _ := by rw [hpow]

end ContinuousFlexibility.Analysis
