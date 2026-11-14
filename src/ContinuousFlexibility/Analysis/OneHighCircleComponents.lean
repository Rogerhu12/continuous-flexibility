module

public import ContinuousFlexibility.Analysis.OneHighCircleRealSobolev
public import ContinuousFlexibility.Analysis.OneHighL2Domination
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Actual component derivatives for multivariable composition

The joint input uses the usual finite-product norm. Its component functions
use exactly the existing physical Fourier norms. The finite sums below make
the dependence on the number of input functions explicit.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal BigOperators

variable {P : ℝ} [Fact (0 < P)] {m : ℕ}

def circleComponent (f : C(AddCircle P, Fin m → ℝ)) (i : Fin m) :
    C(AddCircle P, ℝ) :=
  ⟨fun θ => f θ i, (continuous_apply i).comp f.continuous⟩

@[simp] theorem circleComponent_apply (f : C(AddCircle P, Fin m → ℝ))
    (i : Fin m) (θ : AddCircle P) : circleComponent f i θ = f θ i := rfl

theorem circleComponent_hasDerivAt
    (f : ℕ → C(AddCircle P, Fin m → ℝ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x)
    (i : Fin m) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => circleComponent (f k) i (y : AddCircle P))
      (circleComponent (f (k + 1)) i (x : AddCircle P)) x := by
  simpa only [circleComponent_apply, ContinuousLinearMap.proj_apply, Function.comp_def] using
    (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt x
      (hderiv k x)

theorem norm_pi_le_sum_norm (z : Fin m → ℝ) : ‖z‖ ≤ ∑ i, ‖z i‖ := by
  classical
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg (z i))).mpr
  intro i
  exact Finset.single_le_sum (fun j _ => norm_nonneg (z j)) (Finset.mem_univ i)

theorem circle_l2_pi_le_sum (f : C(AddCircle P, Fin m → ℝ)) :
    (eLpNorm f 2 AddCircle.haarAddCircle).toReal ≤
      ∑ i, (eLpNorm (circleComponent f i) 2 AddCircle.haarAddCircle).toReal := by
  classical
  have hp (θ : AddCircle P) :
      ‖f θ‖ ≤ ∑ i : Fin m, 1 * ‖circleComponent f i θ‖ := by
    simpa only [one_mul, circleComponent_apply] using norm_pi_le_sum_norm (f θ)
  have h := oneHigh_l2_finite_domination
    (μ := AddCircle.haarAddCircle) (g := (f : AddCircle P → Fin m → ℝ))
    f.continuous.aestronglyMeasurable
    (fun i : Fin m => (circleComponent f i : AddCircle P → ℝ))
    (fun i => ContinuousMap.memLp (p := 2) (μ := AddCircle.haarAddCircle) ℝ
      (circleComponent f i))
    (fun _ => (1 : ℝ)) (fun _ => zero_le_one) (Eventually.of_forall hp)
  simpa only [one_mul] using h.2

/-- An arbitrary selection of input components in the derivative product.
The high norm is the sum of the actual component Sobolev norms. -/
theorem circle_real_selected_derivative_product_le
    (f : Fin m → ℕ → C(AddCircle P, ℝ))
    (hderiv : ∀ i, ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f i k (y : AddCircle P))
        (f i (k + 1) (x : AddCircle P)) x)
    {k s : ℕ} (hk : 0 < k) (sel : Fin k → Fin m)
    (a : Fin k → ℕ) (ha : ∑ i, a i ≤ s) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ i, circleRealFourierL1Norm (f i 0) ≤ R) :
    (eLpNorm (∏ j, f (sel j) (a j)) 2 AddCircle.haarAddCircle).toReal ≤
      (k : ℝ) * R ^ (k - 1) * ∑ i, circleRealSobolevNorm (s : ℝ) (f i 0) := by
  classical
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  let H := ∑ i, circleRealSobolevNorm (s : ℝ) (f i 0)
  have h := circle_real_derivative_product_oneHigh l s
    (fun j => f (sel j)) (fun j => hderiv (sel j)) a ha
  have hprod (j : Fin (l + 1)) :
      (∏ i ∈ Finset.univ.erase j, circleRealFourierL1Norm (f (sel i) 0)) ≤ R ^ l := by
    calc
      _ ≤ ∏ _i ∈ Finset.univ.erase j, R :=
        Finset.prod_le_prod₀ (fun _ _ => ENNReal.toReal_nonneg) (fun i _ => hR (sel i))
      _ = _ := by simp
  have hhigh (j : Fin (l + 1)) : circleRealSobolevNorm (s : ℝ) (f (sel j) 0) ≤ H :=
    Finset.single_le_sum (f := fun i => circleRealSobolevNorm (s : ℝ) (f i 0))
      (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ (sel j))
  calc
    _ ≤ ∑ j : Fin (l + 1), circleRealSobolevNorm (s : ℝ) (f (sel j) 0) *
        ∏ i ∈ Finset.univ.erase j, circleRealFourierL1Norm (f (sel i) 0) := h
    _ ≤ ∑ _j : Fin (l + 1), H * R ^ l := by
      apply Finset.sum_le_sum
      intro j _
      exact (mul_le_mul_of_nonneg_left (hprod j) ENNReal.toReal_nonneg).trans
        (mul_le_mul_of_nonneg_right (hhigh j) (pow_nonneg hR0 l))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.succ_eq_add_one, Nat.add_sub_cancel]
      ring

end ContinuousFlexibility.Analysis
