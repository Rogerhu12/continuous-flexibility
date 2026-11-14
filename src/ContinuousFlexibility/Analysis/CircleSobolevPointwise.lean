module

public import ContinuousFlexibility.Analysis.StateKappaBounds
public import ContinuousFlexibility.Analysis.CylinderSobolev
public import ContinuousFlexibility.Analysis.CircleModelRealization
public import ContinuousFlexibility.Analysis.CircleJetClosedGraph
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Algebra.Order.ToIntervalMod

/-!
# Pointwise angular jets in the actual weighted circle model

The one-dimensional fundamental theorem of calculus and Hölder inequality
give a uniform Sobolev evaluation bound on one period.  Extracting an
actual angular jet from the complete circle energy then bounds every
decoded derivative by the existing grading and its sample weight.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

def circleSobolevConstant : ℝ :=
  Real.pi⁻¹ * Real.sqrt Real.pi + Real.sqrt Real.pi

theorem circleSobolevConstant_nonneg : 0 ≤ circleSobolevConstant := by
  unfold circleSobolevConstant
  positivity

theorem circleSobolevConstant_pos : 0 < circleSobolevConstant := by
  have hπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (inv_nonneg.mpr Real.pi_pos.le) hπ.le) hπ

/-- Every actual angular derivative of a periodic function is periodic. -/
theorem circlePeriodic_iteratedDeriv_real {f : ℝ → ℝ}
    (hp : Function.Periodic f Real.pi) (b : ℕ) :
    Function.Periodic (iteratedDeriv b f) Real.pi := by
  have heq : (fun x : ℝ => f (x + Real.pi)) = f := funext hp
  intro x
  have h := congrArg (fun g : ℝ → ℝ => iteratedDeriv b g x) heq
  simpa only [iteratedDeriv_comp_add_const] using h

/-- Evaluation on the whole real line is bounded by the two adjacent
actual L² norms on the fixed angular interval. -/
theorem abs_periodic_le_angleL2_add_deriv {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi) (θ : ℝ) :
    |f θ| ≤ circleSobolevConstant *
      ((eLpNorm f 2 angleMeasure).toReal + (eLpNorm (deriv f) 2 angleMeasure).toReal) := by
  let y := toIocMod Real.pi_pos 0 θ
  let n := toIocDiv Real.pi_pos 0 θ
  have hy : y ∈ Icc (0 : ℝ) Real.pi := by
    have h : y ∈ Ioc (0 : ℝ) Real.pi := by
      simpa only [y, zero_add] using toIocMod_mem_Ioc Real.pi_pos 0 θ
    exact ⟨h.1.le, h.2⟩
  have hθ : y + n • Real.pi = θ := toIocMod_add_toIocDiv_zsmul Real.pi_pos 0 θ
  have heval : f θ = f y := (congrArg f hθ.symm).trans (hp.zsmul n y)
  have hpoint := Analysis.abs_le_interval_average_add_deriv hf Real.pi_pos hy
  rw [sub_zero, ← heval] at hpoint
  have hlf := integral_abs_le_angleL2 (memLp_angleMeasure_of_continuous hf.continuous)
  have hld := integral_abs_le_angleL2
    (memLp_angleMeasure_of_continuous (hf.continuous_deriv (by simp)))
  have hπ0 : 0 ≤ Real.pi⁻¹ := inv_nonneg.mpr Real.pi_pos.le
  calc
    |f θ| ≤ Real.pi⁻¹ * (∫ y, |f y| ∂angleMeasure) +
        ∫ y, |deriv f y| ∂angleMeasure := hpoint
    _ ≤ (Real.pi⁻¹ * Real.sqrt Real.pi) * (eLpNorm f 2 angleMeasure).toReal +
        Real.sqrt Real.pi * (eLpNorm (deriv f) 2 angleMeasure).toReal := by
      simpa only [mul_assoc] using
        add_le_add (mul_le_mul_of_nonneg_left hlf hπ0) hld
    _ ≤ circleSobolevConstant * (eLpNorm f 2 angleMeasure).toReal +
        circleSobolevConstant * (eLpNorm (deriv f) 2 angleMeasure).toReal := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (Real.sqrt_nonneg _)) ENNReal.toReal_nonneg
      · exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left (mul_nonneg hπ0 (Real.sqrt_nonneg _)))
          ENNReal.toReal_nonneg
    _ = _ := (mul_add _ _ _).symm

theorem abs_periodic_iteratedDeriv_le_angleL2 {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi) (b : ℕ) (θ : ℝ) :
    |iteratedDeriv b f θ| ≤ circleSobolevConstant *
      ((eLpNorm (iteratedDeriv b f) 2 angleMeasure).toReal +
        (eLpNorm (iteratedDeriv (b + 1) f) 2 angleMeasure).toReal) := by
  have hfb : ContDiff ℝ ∞ (iteratedDeriv b f) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv b hf
  have h := abs_periodic_le_angleL2_add_deriv hfb
    (circlePeriodic_iteratedDeriv_real hp b) θ
  simpa only [iteratedDeriv_succ] using h

/-- Extract a single actual angular derivative from the complete norm sum
at that same order. -/
theorem circleMember_deriv_angleL2_le_weight
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (hH : ∀ m, 0 < T.H (T.sample m)) (m b : ℕ) :
    (eLpNorm (iteratedDeriv b (u m)) 2 angleMeasure).toReal ≤
      circleNorm T γ b u * T.H (T.sample m) ^ γ := by
  let j : CircleJetIndex b :=
    ⟨fun i => if i = 0 then ⟨b, Nat.lt_succ_self b⟩ else 0, by simp⟩
  let term (i : ℕ) (k : CircleJetIndex b) : ℝ≥0∞ :=
    ENNReal.ofReal ((T.M (T.sample i) ^ (k.val 1).val * T.H (T.sample i) ^ (-γ)) ^ 2) *
      eLpNorm (iteratedDeriv (k.val 0).val (u i)) 2 angleMeasure ^ 2
  let total : ℝ≥0∞ := ∑' i : ℕ, ∑ k : CircleJetIndex b, term i k
  have hfinite : total < ⊤ := hu.2.2 b
  have hsingle : term m j ≤ ∑ k : CircleJetIndex b, term m k :=
    Finset.single_le_sum (f := term m) (fun _ _ => zero_le) (Finset.mem_univ _)
  have hsum : (∑ k : CircleJetIndex b, term m k) ≤ total :=
    ENNReal.le_tsum (f := fun i => ∑ k : CircleJetIndex b, term i k) m
  have hterm : ENNReal.ofReal ((T.H (T.sample m) ^ (-γ)) ^ 2) *
      eLpNorm (iteratedDeriv b (u m)) 2 angleMeasure ^ 2 ≤ total := by
    simpa [term, j] using hsingle.trans hsum
  have hreal := ENNReal.toReal_mono hfinite.ne hterm
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_pow] at hreal
  have hsq : (T.H (T.sample m) ^ (-γ) *
      (eLpNorm (iteratedDeriv b (u m)) 2 angleMeasure).toReal) ^ 2 ≤ total.toReal := by
    rw [mul_pow]
    exact hreal
  have hnonneg : 0 ≤ T.H (T.sample m) ^ (-γ) *
      (eLpNorm (iteratedDeriv b (u m)) 2 angleMeasure).toReal :=
    mul_nonneg (Real.rpow_nonneg (hH m).le _) ENNReal.toReal_nonneg
  have hweighted := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq hnonneg] at hweighted
  change T.H (T.sample m) ^ (-γ) *
    (eLpNorm (iteratedDeriv b (u m)) 2 angleMeasure).toReal ≤ circleNorm T γ b u at hweighted
  rw [Real.rpow_neg (hH m).le, ← div_eq_inv_mul] at hweighted
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (hH m) γ)).mp hweighted

theorem circleMember_iteratedDeriv_abs_le
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (hH : ∀ m, 0 < T.H (T.sample m)) (m b : ℕ) (θ : ℝ) :
    |iteratedDeriv b (u m) θ| ≤
      circleSobolevConstant * (circleNorm T γ b u + circleNorm T γ (b + 1) u) *
        T.H (T.sample m) ^ γ := by
  calc
    _ ≤ circleSobolevConstant *
        ((eLpNorm (iteratedDeriv b (u m)) 2 angleMeasure).toReal +
          (eLpNorm (iteratedDeriv (b + 1) (u m)) 2 angleMeasure).toReal) :=
      abs_periodic_iteratedDeriv_le_angleL2 (hu.1 m).1 (hu.1 m).2 b θ
    _ ≤ circleSobolevConstant *
        (circleNorm T γ b u * T.H (T.sample m) ^ γ +
          circleNorm T γ (b + 1) u * T.H (T.sample m) ^ γ) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (circleMember_deriv_angleL2_le_weight hu hH m b)
          (circleMember_deriv_angleL2_le_weight hu hH m (b + 1))) circleSobolevConstant_nonneg
    _ = _ := by ring

/-- The bound uses the supplied circle model's own grading. -/
theorem circleModel_iteratedDeriv_abs_le
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (hH : ∀ m, 0 < T.H (T.sample m))
    (u : S.Space) (m b : ℕ) (θ : ℝ) :
    |iteratedDeriv b (S.decode u m) θ| ≤
      (2 * circleSobolevConstant * S.grading (b + 1) u) * T.H (T.sample m) ^ γ := by
  have hu : CircleMember T γ (S.decode u) := hS.2.2.2.1 u
  have hgrades := (circleGrading_le_iff_circleNorm hS (b + 1) u (apply_nonneg _ _)).mp
    (le_refl (S.grading (b + 1) u))
  have hb := hgrades b (Nat.le_succ b)
  have hb1 := hgrades (b + 1) le_rfl
  have hsum : circleNorm T γ b (S.decode u) + circleNorm T γ (b + 1) (S.decode u) ≤
      2 * S.grading (b + 1) u := by linarith
  calc
    _ ≤ circleSobolevConstant *
        (circleNorm T γ b (S.decode u) + circleNorm T γ (b + 1) (S.decode u)) *
          T.H (T.sample m) ^ γ := circleMember_iteratedDeriv_abs_le hu hH m b θ
    _ ≤ circleSobolevConstant * (2 * S.grading (b + 1) u) * T.H (T.sample m) ^ γ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum circleSobolevConstant_nonneg)
        (Real.rpow_nonneg (hH m).le _)
    _ = _ := by ring

end ContinuousFlexibility.Statements
