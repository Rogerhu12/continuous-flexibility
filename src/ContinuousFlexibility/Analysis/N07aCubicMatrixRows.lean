import ContinuousFlexibility.Analysis.N07aCubicDifferenceJets
import ContinuousFlexibility.Analysis.N07aCircleBlockCoefficients

/-!
# Circle matrix entries retain the cubic endpoint factors

The cosine and sine entries satisfy the same linear identities. The
first radial derivative costs one endpoint power; an angular derivative
retains all three powers.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements ContinuousFlexibility.Radial CanonicalGeometry
open scoped ContDiff

def n07aTrigMatrixEntry (sine : Bool) (f : ℝ → ℝ) (l j : ℕ) : ℝ :=
  if sine then n07aSineMatrixEntry f l j else n07aCosineMatrixEntry f l j

theorem n07aTrigMatrixEntry_const_mul (sine : Bool) (c : ℝ) (f : ℝ → ℝ) (l j : ℕ) :
    n07aTrigMatrixEntry sine (fun θ => c * f θ) l j = c * n07aTrigMatrixEntry sine f l j := by
  cases sine <;> simp only [n07aTrigMatrixEntry, Bool.false_eq_true, ite_false, ite_true,
    n07aSineMatrixEntry, n07aCosineMatrixEntry, mul_assoc, integral_const_mul] <;> ring

theorem n07aTrigMatrixEntry_add (sine : Bool) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (l j : ℕ) :
    n07aTrigMatrixEntry sine (fun θ => f θ + g θ) l j =
      n07aTrigMatrixEntry sine f l j + n07aTrigMatrixEntry sine g l j := by
  have hs : Continuous (n07aSineBasis j) := by
    unfold n07aSineBasis
    fun_prop
  have hi (v : ℝ → ℝ) (hv : Continuous v) (b : ℝ → ℝ) (hb : Continuous b) :
      Integrable (fun θ => v θ * b θ * referenceAngularBasis l θ) angleMeasure :=
    ((hv.mul hb).mul (contDiff_referenceAngularBasis l).continuous).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  cases sine
  · simp only [n07aTrigMatrixEntry, Bool.false_eq_true, ite_false, n07aCosineMatrixEntry, add_mul]
    rw [integral_add (hi f hf _ (contDiff_referenceAngularBasis j).continuous)
      (hi g hg _ (contDiff_referenceAngularBasis j).continuous), mul_add]
  · simp only [n07aTrigMatrixEntry, ite_true, n07aSineMatrixEntry, add_mul]
    rw [integral_add (hi f hf _ hs) (hi g hg _ hs), mul_add]

theorem n07a_unitCubic_matrix (sine : Bool) (g : PolarPoint → ℝ)
    (c x : ℝ) (l j : ℕ) :
    n07aTrigMatrixEntry sine (fun θ => c * cylinderWeight x ^ 3 * g (x, θ)) l j =
      c * cylinderWeight x ^ 3 * n07aTrigMatrixEntry sine (fun θ => g (x, θ)) l j :=
  n07aTrigMatrixEntry_const_mul sine _ _ l j

theorem n07a_unitCubic_firstNormal_matrix (sine : Bool) {g : PolarPoint → ℝ}
    (hg : ContDiffOn ℝ ∞ g unitStrip) (c : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (l j : ℕ) :
    n07aTrigMatrixEntry sine
      (fun θ => mixedDerivative 1 0 (fun q => c * cylinderWeight q.1 ^ 3 * g q) (x, θ)) l j =
      c * (3 * cylinderWeight x ^ 2 * (1 - 2 * x) *
        n07aTrigMatrixEntry sine (fun θ => g (x, θ)) l j +
        cylinderWeight x ^ 3 * n07aTrigMatrixEntry sine (n07aUnitJetRow g 1 0 x) l j) := by
  have he : (fun θ => mixedDerivative 1 0 (fun q => c * cylinderWeight q.1 ^ 3 * g q) (x, θ)) =
      fun θ => c * (3 * cylinderWeight x ^ 2 * (1 - 2 * x) * g (x, θ) +
        cylinderWeight x ^ 3 * n07aUnitJetRow g 1 0 x θ) := by
    funext θ
    exact n07a_unitCubic_firstNormal hg c ⟨hx, mem_univ _⟩
  have hg0 : Continuous (fun θ => g (x, θ)) := by
    exact hg.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun θ => ⟨hx, mem_univ θ⟩)
  have hf : Continuous (fun θ => 3 * cylinderWeight x ^ 2 * (1 - 2 * x) * g (x, θ)) :=
    continuous_const.mul hg0
  have hgr : Continuous (fun θ => cylinderWeight x ^ 3 * n07aUnitJetRow g 1 0 x θ) :=
    continuous_const.mul ((n07aUnitJetRow_contDiff hg 1 0 hx).continuous)
  rw [he, n07aTrigMatrixEntry_const_mul,
    n07aTrigMatrixEntry_add sine hf hgr,
    n07aTrigMatrixEntry_const_mul, n07aTrigMatrixEntry_const_mul]

theorem n07a_unitCubic_firstAngular_matrix (sine : Bool) (g : PolarPoint → ℝ)
    (c x : ℝ) (l j : ℕ) :
    n07aTrigMatrixEntry sine
      (fun θ => mixedDerivative 0 1 (fun q => c * cylinderWeight q.1 ^ 3 * g q) (x, θ)) l j =
      c * cylinderWeight x ^ 3 * n07aTrigMatrixEntry sine (n07aUnitJetRow g 0 1 x) l j := by
  have he : (fun θ => mixedDerivative 0 1 (fun q => c * cylinderWeight q.1 ^ 3 * g q) (x, θ)) =
      fun θ => c * cylinderWeight x ^ 3 * n07aUnitJetRow g 0 1 x θ := by
    funext θ
    exact n07a_unitCubic_firstAngular c (x, θ)
  rw [he, n07aTrigMatrixEntry_const_mul]

theorem n07a_unitCubic_firstNormal_matrix_bound (sine : Bool) {g : PolarPoint → ℝ}
    (hg : ContDiffOn ℝ ∞ g unitStrip) {c M κ x : ℝ} (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hx : x ∈ Ioo (0 : ℝ) 1) (l j : ℕ)
    (h₀ : |κ * n07aTrigMatrixEntry sine (fun θ => g (x, θ)) l j| ≤ M)
    (h₁ : |κ * n07aTrigMatrixEntry sine (n07aUnitJetRow g 1 0 x) l j| ≤ M) :
    |κ * n07aTrigMatrixEntry sine
      (fun θ => mixedDerivative 1 0 (fun q => c * cylinderWeight q.1 ^ 3 * g q) (x, θ)) l j| ≤
      4 * c * cylinderWeight x ^ 2 * M := by
  rw [n07a_unitCubic_firstNormal_matrix sine hg c hx]
  have hw : 0 ≤ cylinderWeight x := cylinderWeight_nonneg (Ioo_subset_Icc_self hx)
  have hw1 : cylinderWeight x ≤ 1 := cylinderWeight_le_one (Ioo_subset_Icc_self hx)
  have hd : |1 - 2 * x| ≤ 1 := (abs_le).mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
  calc
    _ = |(3 * c * cylinderWeight x ^ 2 * (1 - 2 * x)) *
        (κ * n07aTrigMatrixEntry sine (fun θ => g (x, θ)) l j) +
        (c * cylinderWeight x ^ 3) *
        (κ * n07aTrigMatrixEntry sine (n07aUnitJetRow g 1 0 x) l j)| := by congr 1; ring
    _ ≤ |3 * c * cylinderWeight x ^ 2 * (1 - 2 * x)| * M +
        |c * cylinderWeight x ^ 3| * M :=
      (abs_add_le _ _).trans (add_le_add
        (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h₀ (abs_nonneg _))
        (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h₁ (abs_nonneg _)))
    _ = (c * cylinderWeight x ^ 2 * M) * (3 * |1 - 2 * x| + cylinderWeight x) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 3 * c * cylinderWeight x ^ 2),
        abs_of_nonneg (mul_nonneg hc (pow_nonneg hw 3))]
      ring
    _ ≤ (c * cylinderWeight x ^ 2 * M) * 4 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

end ContinuousFlexibility.Analysis
