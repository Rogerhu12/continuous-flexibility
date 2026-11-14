module

public import ContinuousFlexibility.Scalar.S05CalculusProof
public import ContinuousFlexibility.Analysis.SmoothScaledIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Fixed-loss bounds for the existing smooth simple-zero division

The smooth factor is the one already constructed by S05. Its factorization
identifies it uniquely with a fixed interval integral, giving actual
all-order derivatives and a loss of one independent of the interval width.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Topology Interval

/-- Any smooth factor of a true zero equals the first Taylor integral. -/
theorem smoothDivisionFactor_eq_integral {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfactor : ∀ x : ℝ, f x = x * g x) (x : ℝ) :
    g x = ∫ t in (0 : ℝ)..1, deriv f (t * x) := by
  have hf0 : f 0 = 0 := by simpa only [zero_mul] using hfactor 0
  have he : f = fun y => y * g y := funext hfactor
  have hdf0 : deriv f 0 = g 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).fun_mul
      (hg.differentiable (by simp) 0).hasDerivAt).deriv
    rw [he]
    simpa only [id_eq, zero_mul, one_mul, add_zero] using h
  by_cases hx : x = 0
  · subst x
    simp only [mul_zero, intervalIntegral.integral_const, sub_zero, one_smul, hdf0]
  have hd : ContDiff ℝ ∞ (deriv f) := ContDiff.iterate_deriv 1 hf
  have hchange :
      x * (∫ t in (0 : ℝ)..1, deriv f (t * x)) = ∫ y in (0 : ℝ)..x, deriv f y := by
    simpa only [mul_zero, zero_add, mul_one, add_zero, smul_eq_mul, mul_comm] using
      intervalIntegral.smul_integral_comp_mul_add (deriv f)
        (a := (0 : ℝ)) (b := 1) x 0
  have hFTC := intervalIntegral.integral_deriv_eq_sub
    (a := (0 : ℝ)) (b := x)
    (fun y _ => hf.differentiable (by simp) y)
    (hd.continuous.intervalIntegrable 0 x)
  rw [hf0, sub_zero, hfactor x] at hFTC
  exact (mul_left_cancel₀ hx (hchange.trans hFTC)).symm

theorem iteratedDeriv_smoothDivisionFactor {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfactor : ∀ x : ℝ, f x = x * g x) (n : ℕ) :
    iteratedDeriv n g =
      fun x => ∫ t in (0 : ℝ)..1, t ^ n * iteratedDeriv (n + 1) f (t * x) := by
  have hd : ContDiff ℝ ∞ (deriv f) := ContDiff.iterate_deriv 1 hf
  have he : g = fun x => ∫ t in (0 : ℝ)..1, (1 : ℝ) * deriv f (t * x) := by
    funext x
    simpa only [one_mul] using smoothDivisionFactor_eq_integral hf hg hfactor x
  rw [he, iteratedDeriv_scaled_intervalIntegral continuous_const hd n]
  simp only [one_mul, ← iteratedDeriv_succ']

/-- The derivative bound is uniform as the actual interval shrinks. -/
theorem norm_iteratedDeriv_smoothDivisionFactor_le {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfactor : ∀ x : ℝ, f x = x * g x) (n : ℕ) {ρ M x : ℝ}
    (hM : 0 ≤ M) (hx : x ∈ Icc (0 : ℝ) ρ)
    (hbound : ∀ y ∈ Icc (0 : ℝ) ρ, |iteratedDeriv (n + 1) f y| ≤ M) :
    |iteratedDeriv n g x| ≤ M := by
  rw [iteratedDeriv_smoothDivisionFactor hf hg hfactor n]
  have hpoint (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      ‖t ^ n * iteratedDeriv (n + 1) f (t * x)‖ ≤ M := by
    have htx0 : 0 ≤ t * x := mul_nonneg ht.1.le hx.1
    have htx : t * x ≤ ρ := by
      have h := mul_le_mul_of_nonneg_right ht.2 hx.1
      exact (show t * x ≤ x by simpa only [one_mul] using h).trans hx.2
    have hp0 : 0 ≤ t ^ n := pow_nonneg ht.1.le n
    have hp1 : t ^ n ≤ 1 := pow_le_one₀ ht.1.le ht.2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp0]
    calc
      t ^ n * |iteratedDeriv (n + 1) f (t * x)| ≤ t ^ n * M :=
        mul_le_mul_of_nonneg_left (hbound _ ⟨htx0, htx⟩) hp0
      _ ≤ 1 * M := mul_le_mul_of_nonneg_right hp1 hM
      _ = M := one_mul M
  have hweight : IntervalIntegrable (fun _ : ℝ => M) volume 0 1 :=
    intervalIntegrable_const
  have h := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Eventually.of_forall hpoint) hweight
  simpa only [Real.norm_eq_abs, intervalIntegral.integral_const, sub_zero, one_smul] using h

/-- S05's actual construction carries the additional all-order bounds;
no new choice of quotient or extension is required. -/
theorem exists_smooth_division_with_jet_bounds {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfzero : f 0 = 0) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ g 0 = deriv f 0 ∧
      (∀ x : ℝ, f x = x * g x) ∧
      ∀ (n : ℕ) (ρ M : ℝ), 0 ≤ M →
        (∀ y ∈ Icc (0 : ℝ) ρ, |iteratedDeriv (n + 1) f y| ≤ M) →
        ∀ x ∈ Icc (0 : ℝ) ρ, |iteratedDeriv n g x| ≤ M := by
  obtain ⟨g, hg, hg0, hfactor⟩ := exists_smooth_division_at_zero hf hfzero
  exact ⟨g, hg, hg0, hfactor, fun n _ _ hM hb x hx =>
    norm_iteratedDeriv_smoothDivisionFactor_le hf hg hfactor n hM hx hb⟩

end ContinuousFlexibility.Analysis
