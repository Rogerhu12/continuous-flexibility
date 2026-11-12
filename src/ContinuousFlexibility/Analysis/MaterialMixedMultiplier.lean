import ContinuousFlexibility.Analysis.MaterialCylinderPointwise
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Polynomially weighted mixed multipliers on the material cylinder

The two-variable Leibniz formula retains both derivative indices. A
coefficient whose mixed jets grow by one fixed power of the material
weight multiplies the complete weighted L² class into itself. The power
loss is fixed before the derivative orders are chosen.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff BigOperators ENNReal

private theorem contDiff_radial_angular_jet {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (b : ℕ) (θ : ℝ) :
    ContDiff ℝ ∞ (fun r => iteratedDeriv b (fun t => f (r, t)) θ) := by
  have h := (contDiff_mixedDerivative hf 0 b).comp
    (contDiff_id.prodMk (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => θ)))
  simpa only [Function.comp_def, mixedDerivative, iteratedDeriv_zero, id_eq] using h

theorem mixedDerivative_mul {f g : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => f q * g q) p =
      ∑ j ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
        (b.choose j : ℝ) * (a.choose i : ℝ) *
          mixedDerivative i j f p * mixedDerivative (a - i) (b - j) g p := by
  have hangle (r : ℝ) :
      iteratedDeriv b (fun θ => f (r, θ) * g (r, θ)) p.2 =
        ∑ j ∈ Finset.range (b + 1), (b.choose j : ℝ) *
          iteratedDeriv j (fun θ => f (r, θ)) p.2 *
            iteratedDeriv (b - j) (fun θ => g (r, θ)) p.2 :=
    iteratedDeriv_fun_mul
      ((hf.comp (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by simp))
      ((hg.comp (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by simp))
  have hterm (j : ℕ) : ContDiff ℝ ∞ (fun r =>
      (b.choose j : ℝ) * iteratedDeriv j (fun θ => f (r, θ)) p.2 *
        iteratedDeriv (b - j) (fun θ => g (r, θ)) p.2) :=
    (contDiff_const.mul (contDiff_radial_angular_jet hf j p.2)).mul
      (contDiff_radial_angular_jet hg (b - j) p.2)
  unfold mixedDerivative
  simp only [hangle]
  rw [iteratedDeriv_fun_sum (fun j hj => (hterm j).contDiffAt.of_le (by simp))]
  apply Finset.sum_congr rfl
  intro j hj
  have hfun : (fun r => (b.choose j : ℝ) *
      iteratedDeriv j (fun θ => f (r, θ)) p.2 *
        iteratedDeriv (b - j) (fun θ => g (r, θ)) p.2) =
      (fun r => (b.choose j : ℝ) *
        (iteratedDeriv j (fun θ => f (r, θ)) p.2 *
          iteratedDeriv (b - j) (fun θ => g (r, θ)) p.2)) := by
    funext r
    exact mul_assoc _ _ _
  rw [hfun, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_mul
      ((contDiff_radial_angular_jet hf j p.2).contDiffAt.of_le (by simp))
      ((contDiff_radial_angular_jet hg (b - j) p.2).contDiffAt.of_le (by simp)),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem weighted_mixedDerivative_mul {f g : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (W : PolarPoint → ℝ) (a b c : ℕ) (p : PolarPoint) :
    W p ^ c * mixedDerivative a b (fun q => f q * g q) p =
      ∑ j ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
        ((b.choose j : ℝ) * (a.choose i : ℝ)) *
          (W p ^ c * mixedDerivative i j f p * mixedDerivative (a - i) (b - j) g p) := by
  rw [mixedDerivative_mul hf hg]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem weighted_product_abs_bound
    (w f g K : ℝ) (c d : ℕ) (hw : 0 ≤ w) (hK : 0 ≤ K)
    (hf : |f| ≤ K * w ^ d) :
    |w ^ c * f * g| ≤ |K * (w ^ (c + d) * g)| := by
  simp only [abs_mul, abs_of_nonneg hK,
    pow_add, abs_of_nonneg (pow_nonneg hw c), abs_of_nonneg (pow_nonneg hw d)]
  calc
    w ^ c * |f| * |g| ≤ w ^ c * (K * w ^ d) * |g| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf (pow_nonneg hw c))
        (abs_nonneg g)
    _ = K * (w ^ c * w ^ d * |g|) := by ring

theorem memLp_weighted_product_of_power_bound
    {W f g : PolarPoint → ℝ} (hW : Continuous W) (hWpos : ∀ p, 0 ≤ W p)
    (hf : Continuous f) (hg : Continuous g) (c d : ℕ)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ p, |f p| ≤ K * W p ^ d)
    (hLp : MemLp (fun p => W p ^ (c + d) * g p) 2 materialCylinderMeasure) :
    MemLp (fun p => W p ^ c * f p * g p) 2 materialCylinderMeasure := by
  apply (hLp.const_mul K).of_le (((hW.pow c).mul hf).mul hg).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    simpa only [Real.norm_eq_abs, Pi.mul_apply, Pi.pow_apply] using
      weighted_product_abs_bound (W p) (f p) (g p) K c d (hWpos p) hK (hbound p)

/-- Every term uses only the original derivative budget a + b and the
same additional weight power d. -/
theorem memLp_weighted_mixed_product
    {W f g : PolarPoint → ℝ} (hW : Continuous W) (hWpos : ∀ p, 0 ≤ W p)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (d : ℕ)
    (hbound : ∀ a b, ∃ K : ℝ, 0 ≤ K ∧
      ∀ p, |mixedDerivative a b f p| ≤ K * W p ^ d)
    (hLp : ∀ a b c,
      MemLp (fun p => W p ^ c * mixedDerivative a b g p) 2 materialCylinderMeasure)
    (a b c : ℕ) :
    MemLp (fun p => W p ^ c * mixedDerivative a b (fun q => f q * g q) p)
      2 materialCylinderMeasure := by
  have hterm (i j : ℕ) :
      MemLp (fun p => ((b.choose j : ℝ) * (a.choose i : ℝ)) *
        (W p ^ c * mixedDerivative i j f p * mixedDerivative (a - i) (b - j) g p))
        2 materialCylinderMeasure := by
    obtain ⟨K, hK, hb⟩ := hbound i j
    exact (memLp_weighted_product_of_power_bound hW hWpos
      (contDiff_mixedDerivative hf i j).continuous
      (contDiff_mixedDerivative hg (a - i) (b - j)).continuous c d hK hb
      (hLp (a - i) (b - j) (c + d))).const_mul _
  have hsum := memLp_finsetSum (Finset.range (b + 1)) (fun j hj =>
    memLp_finsetSum (Finset.range (a + 1)) (fun i hi => hterm i j))
  apply hsum.ae_eq
  exact Eventually.of_forall fun p => (weighted_mixedDerivative_mul hf hg W a b c p).symm

end ContinuousFlexibility.Statements
