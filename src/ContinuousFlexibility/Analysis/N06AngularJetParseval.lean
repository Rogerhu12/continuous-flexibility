module

public import ContinuousFlexibility.Analysis.N06EvenCylinder
public import ContinuousFlexibility.Analysis.SpacesCircleFourierJets

/-!
# Actual angular jets and their finite Parseval weights

The diagonal weight of the k-th actual angular derivative is ν^(2k).
This includes the zero frequency and gives the finite-jet source norm
used by the canonical Banach spaces, without replacing it by a formal norm.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped BigOperators ContDiff
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

private theorem n06_angularPairing_const_mul (a b : ℝ) (f g : ℝ → ℝ) :
    angularPairing (fun θ => a * f θ) (fun θ => b * g θ) =
      a * b * angularPairing f g := by
  unfold angularPairing angularAverage
  have heq : (fun θ => (a * f θ) * (b * g θ)) =
      fun θ => (a * b) * (f θ * g θ) := by funext θ; ring
  rw [heq, intervalIntegral.integral_const_mul]
  ring

private theorem n06_angularAverage_finsetSum {ι : Type*}
    (s : Finset ι) (f : ι → ℝ → ℝ) (hf : ∀ i ∈ s, Continuous (f i)) :
    angularAverage (fun θ => ∑ i ∈ s, f i θ) =
      ∑ i ∈ s, angularAverage (f i) := by
  unfold angularAverage
  rw [intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).intervalIntegrable _ _),
    Finset.mul_sum]

/-- Finite Parseval also applies when the orthogonal basis vectors have
different square norms, including zero. -/
theorem n06_angularAverage_sq_finite_orthogonal {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (e : ι → ℝ → ℝ) (w c : ι → ℝ)
    (he : ∀ i ∈ s, Continuous (e i))
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then w i else 0) :
    angularAverage (fun θ => (∑ i ∈ s, c i * e i θ) ^ 2) =
      ∑ i ∈ s, w i * c i ^ 2 := by
  have hpoint (θ : ℝ) :
      (∑ i ∈ s, c i * e i θ) ^ 2 =
        ∑ i ∈ s, ∑ j ∈ s, (c i * e i θ) * (c j * e j θ) := by
    rw [pow_two, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => Finset.mul_sum _ _ _)
  have heq := funext hpoint
  have hterm (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      Continuous (fun θ => (c i * e i θ) * (c j * e j θ)) :=
    (continuous_const.mul (he i hi)).mul (continuous_const.mul (he j hj))
  have hsum (i : ι) (hi : i ∈ s) :
      Continuous (fun θ => ∑ j ∈ s, (c i * e i θ) * (c j * e j θ)) :=
    continuous_finsetSum s (fun j hj => hterm i hi j hj)
  rw [heq, n06_angularAverage_finsetSum s
    (fun i θ => ∑ j ∈ s, (c i * e i θ) * (c j * e j θ)) hsum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [n06_angularAverage_finsetSum s (fun j θ => (c i * e i θ) * (c j * e j θ))
    (hterm i hi)]
  change (∑ j ∈ s, angularPairing (fun θ => c i * e i θ)
      (fun θ => c j * e j θ)) = w i * c i ^ 2
  rw [Finset.sum_eq_single i]
  · rw [n06_angularPairing_const_mul, horth i hi i hi, if_pos rfl]
    ring
  · intro j hj hji
    rw [n06_angularPairing_const_mul, horth i hi j hj, if_neg (Ne.symm hji), mul_zero]
  · intro hnot
    exact False.elim (hnot hi)

/-- Both derivative-partner families have the expected diagonal Gram
matrix after any number of actual angular derivatives. -/
theorem n06_iteratedDeriv_partner_pairings {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (e o : ι → ℝ → ℝ) (ν : ι → ℝ)
    (heorth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0)
    (hoorth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (o i) (o j) = if i = j then 1 else 0)
    (hde : ∀ i ∈ s, ∀ θ, HasDerivAt (e i) (ν i * o i θ) θ)
    (hdo : ∀ i ∈ s, ∀ θ, HasDerivAt (o i) (-ν i * e i θ) θ)
    (k : ℕ) :
    (∀ i ∈ s, ∀ j ∈ s,
      angularPairing (iteratedDeriv k (e i)) (iteratedDeriv k (e j)) =
        if i = j then ν i ^ (2 * k) else 0) ∧
    (∀ i ∈ s, ∀ j ∈ s,
      angularPairing (iteratedDeriv k (o i)) (iteratedDeriv k (o j)) =
        if i = j then ν i ^ (2 * k) else 0) := by
  have hdE (i : ι) (hi : i ∈ s) :
      deriv (e i) = fun θ => ν i * o i θ := funext fun θ => (hde i hi θ).deriv
  have hdO (i : ι) (hi : i ∈ s) :
      deriv (o i) = fun θ => -ν i * e i θ := funext fun θ => (hdo i hi θ).deriv
  induction k with
  | zero => simpa only [iteratedDeriv_zero, Nat.mul_zero, pow_zero] using And.intro heorth hoorth
  | succ k ih =>
    have he (i : ι) (hi : i ∈ s) : iteratedDeriv (k + 1) (e i) =
        fun θ => ν i * iteratedDeriv k (o i) θ := by
      funext θ
      rw [iteratedDeriv_succ', hdE i hi, iteratedDeriv_const_mul_field]
    have ho (i : ι) (hi : i ∈ s) : iteratedDeriv (k + 1) (o i) =
        fun θ => -ν i * iteratedDeriv k (e i) θ := by
      funext θ
      rw [iteratedDeriv_succ', hdO i hi, iteratedDeriv_const_mul_field]
    have hpow (x : ℝ) : x * x * x ^ (2 * k) = x ^ (2 * (k + 1)) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
      ring
    constructor
    · intro i hi j hj
      rw [he i hi, he j hj, n06_angularPairing_const_mul, ih.2 i hi j hj]
      by_cases hij : i = j
      · subst j
        simp only [if_pos rfl]
        exact hpow (ν i)
      · simp only [if_neg hij, mul_zero]
    · intro i hi j hj
      rw [ho i hi, ho j hj, n06_angularPairing_const_mul, ih.1 i hi j hj]
      by_cases hij : i = j
      · subst j
        simp only [if_pos rfl, neg_mul_neg]
        exact hpow (ν i)
      · simp only [if_neg hij, mul_zero]

/-- An actual pure angular jet of a finite field differentiates only its
angular basis functions. -/
theorem n06_mixedAngularDerivative_finiteSynthesis {ι : Type*}
    (s : Finset ι) (u e : ι → ℝ → ℝ)
    (he : ∀ i ∈ s, ContDiff ℝ ∞ (e i)) (k : ℕ) :
    mixedDerivative 0 k (r11bFiniteSynthesis s u e) =
      r11bFiniteSynthesis s u (fun i => iteratedDeriv k (e i)) := by
  funext p
  simp only [mixedDerivative, iteratedDeriv_zero, r11bFiniteSynthesis]
  rw [iteratedDeriv_fun_sum (fun i hi =>
    (contDiff_const.mul (he i hi)).contDiffAt.of_le (by simp))]
  exact Finset.sum_congr rfl (fun i _ => iteratedDeriv_const_mul_field _ _)

/-- The k-th actual angular derivative has the exact frequency-square
weight ν^(2k), with any radial endpoint weight. -/
theorem n06CylinderSquare_angularJet_finite {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u e o : ι → ℝ → ℝ) (ν : ι → ℝ)
    (hu : ∀ i ∈ s, Continuous (u i))
    (he : ∀ i ∈ s, ContDiff ℝ ∞ (e i))
    (heorth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0)
    (hoorth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (o i) (o j) = if i = j then 1 else 0)
    (hde : ∀ i ∈ s, ∀ θ, HasDerivAt (e i) (ν i * o i θ) θ)
    (hdo : ∀ i ∈ s, ∀ θ, HasDerivAt (o i) (-ν i * e i θ) θ)
    (a k : ℕ) :
    n06CylinderSquare a (mixedDerivative 0 k (r11bFiniteSynthesis s u e)) =
      ∑ i ∈ s, ν i ^ (2 * k) *
        (∫ y in (0 : ℝ)..1, cylinderWeight y ^ a * u i y ^ 2) := by
  rw [n06_mixedAngularDerivative_finiteSynthesis s u e he k]
  have hgram := (n06_iteratedDeriv_partner_pairings s e o ν heorth hoorth hde hdo k).1
  have hj (i : ι) (hi : i ∈ s) : Continuous (iteratedDeriv k (e i)) :=
    (circleFourier_contDiff_iteratedDeriv (he i hi) k).continuous
  unfold n06CylinderSquare
  have hpoint (y : ℝ) :
      cylinderWeight y ^ a *
        angularAverage (fun θ =>
          r11bFiniteSynthesis s u (fun i => iteratedDeriv k (e i)) (y, θ) ^ 2) =
      ∑ i ∈ s, ν i ^ (2 * k) * (cylinderWeight y ^ a * u i y ^ 2) := by
    unfold r11bFiniteSynthesis
    rw [n06_angularAverage_sq_finite_orthogonal s _ _ (fun i => u i y) hj hgram,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [hpoint]
  have hterm (i : ι) (hi : i ∈ s) :
      Continuous (fun y => ν i ^ (2 * k) * (cylinderWeight y ^ a * u i y ^ 2)) :=
    continuous_const.mul ((cylinderWeight_continuous.pow a).mul ((hu i hi).pow 2))
  have hint (i : ι) (hi : i ∈ s) :
      IntervalIntegrable (fun y => ν i ^ (2 * k) * (cylinderWeight y ^ a * u i y ^ 2))
        volume 0 1 := (hterm i hi).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum hint]
  exact Finset.sum_congr rfl (fun i _ => intervalIntegral.integral_const_mul _ _)

/-- The genuine finite angular-jet square norm. -/
def n06CylinderJetSquare (b : ℕ) (U : PolarPoint → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (b + 1), n06CylinderSquare 0 (mixedDerivative 0 k U)

/-- The canonical finite-jet weight is the sum of the derivative-square
weights. This identity includes the mean and every finite Sobolev order. -/
theorem n06CylinderJetSquare_finite {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u e o : ι → ℝ → ℝ) (ν : ι → ℝ)
    (hu : ∀ i ∈ s, Continuous (u i))
    (he : ∀ i ∈ s, ContDiff ℝ ∞ (e i))
    (heorth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0)
    (hoorth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (o i) (o j) = if i = j then 1 else 0)
    (hde : ∀ i ∈ s, ∀ θ, HasDerivAt (e i) (ν i * o i θ) θ)
    (hdo : ∀ i ∈ s, ∀ θ, HasDerivAt (o i) (-ν i * e i θ) θ)
    (b : ℕ) :
    n06CylinderJetSquare b (r11bFiniteSynthesis s u e) =
      ∑ i ∈ s, (∑ k ∈ Finset.range (b + 1), ν i ^ (2 * k)) *
        (∫ y in (0 : ℝ)..1, u i y ^ 2) := by
  unfold n06CylinderJetSquare
  simp_rw [n06CylinderSquare_angularJet_finite s u e o ν hu he
    heorth hoorth hde hdo 0, pow_zero, one_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => (Finset.sum_mul _ _ _).symm)

end ContinuousFlexibility.Analysis
