import ContinuousFlexibility.Analysis.OneHighCircleFlowIntegral
import ContinuousFlexibility.Analysis.OneHighCircleFlowMinkowski
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Actual angular jets and Sobolev bounds of a compact parameter integral

Only angular smoothness and joint continuity of the actual angular jets
are needed. No time differentiability is required, so the result applies
to a flow kernel after clamping time to its original closed interval.
The derivative identities are derived by differentiation under the
compact integral, then the verified circle Minkowski bound is applied.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff

/-- Compact integration preserves smoothness in the angular variable and
commutes with every actual angular derivative. -/
theorem scalarIntervalIntegral_contDiff_and_iteratedDeriv
    (f : ℝ → ℝ → ℝ)
    (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hj : ∀ n : ℕ, Continuous (fun z : ℝ × ℝ => iteratedDeriv n (f z.1) z.2))
    (a b : ℝ) :
    ContDiff ℝ ∞ (fun θ => ∫ t in a..b, f t θ) ∧
      ∀ n : ℕ, ∀ θ : ℝ,
        iteratedDeriv n (fun η => ∫ t in a..b, f t η) θ =
          ∫ t in a..b, iteratedDeriv n (f t) θ := by
  let J (n : ℕ) (θ : ℝ) := ∫ t in a..b, iteratedDeriv n (f t) θ
  have hJ (n : ℕ) : Continuous (J n) := by
    have hc : Continuous (fun z : ℝ × ℝ => iteratedDeriv n (f z.2) z.1) :=
      (hj n).comp (continuous_snd.prodMk continuous_fst)
    exact continuous_parametric_intervalIntegral hc a b
  have hd (n : ℕ) (θ : ℝ) : HasDerivAt (J n) (J (n + 1) θ) θ := by
    let L := ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ
    have hc : Continuous (fun z : ℝ × ℝ => iteratedDeriv n (f z.2) z.1) :=
      (hj n).comp (continuous_snd.prodMk continuous_fst)
    have hc' : Continuous (fun z : ℝ × ℝ => L (iteratedDeriv (n + 1) (f z.2) z.1)) :=
      L.continuous.comp ((hj (n + 1)).comp (continuous_snd.prodMk continuous_fst))
    have hdiff (x t : ℝ) :
        HasFDerivAt (fun y => iteratedDeriv n (f t) y)
          (L (iteratedDeriv (n + 1) (f t) x)) x := by
      have hn : (n : ℕ∞ω) < ∞ :=
        WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)
      have h := ((hf t).differentiable_iteratedDeriv n hn x).hasDerivAt.hasFDerivAt
      simpa only [L, ContinuousLinearMap.toSpanSingletonLIE_apply, iteratedDeriv_succ] using h
    have hh := (hasFDerivAt_parametric_intervalIntegral hc hc' hdiff a b θ).hasDerivAt
    have hI : (∫ t in a..b, L (iteratedDeriv (n + 1) (f t) θ)) =
        L (∫ t in a..b, iteratedDeriv (n + 1) (f t) θ) := by
      simpa only [LinearIsometryEquiv.coe_toLinearIsometry] using
        L.toLinearIsometry.intervalIntegral_comp_comm (a := a) (b := b) (μ := volume)
          (fun t => iteratedDeriv (n + 1) (f t) θ)
    rw [hI] at hh
    simpa only [L, ContinuousLinearMap.toSpanSingletonLIE_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] using hh
  have hsmooth : ∀ n : ℕ, ∀ k : ℕ, ContDiff ℝ (n : ℕ∞ω) (J k) := by
    intro n
    induction n with
    | zero => intro k; exact contDiff_zero.mpr (hJ k)
    | succ n ih =>
        intro k
        rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 from rfl,
          contDiff_succ_iff_deriv]
        refine ⟨fun θ => (hd k θ).differentiableAt, by simp, ?_⟩
        have he : deriv (J k) = J (k + 1) := funext (fun θ => (hd k θ).deriv)
        rw [he]
        exact ih (k + 1)
  have hjet : ∀ n : ℕ, ∀ θ : ℝ, iteratedDeriv n (J 0) θ = J n θ := by
    intro n
    induction n with
    | zero => intro θ; rfl
    | succ n ih =>
        have he : iteratedDeriv n (J 0) = J n := funext ih
        intro θ
        rw [iteratedDeriv_succ, he]
        exact (hd n θ).deriv
  change ContDiff ℝ ∞ (J 0) ∧ ∀ n θ, iteratedDeriv n (J 0) θ = J n θ
  exact ⟨contDiff_infty.mpr (fun n => hsmooth n 0), hjet⟩

variable {P : ℝ} [Fact (0 < P)]

theorem periodicCircleIntervalIntegral_periodic
    (f : ℝ → ℝ → ℝ) (hp : ∀ t, Function.Periodic (f t) P) (a b : ℝ) :
    Function.Periodic (fun θ => ∫ t in a..b, f t θ) P := by
  intro θ
  exact intervalIntegral.integral_congr (fun t _ => hp t θ)

def periodicCircleIntegralJet (f : ℝ → ℝ → ℝ)
    (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hj : ∀ n : ℕ, Continuous (fun z : ℝ × ℝ => iteratedDeriv n (f z.1) z.2))
    (hp : ∀ t, Function.Periodic (f t) P) (a b : ℝ) (n : ℕ) : C(AddCircle P, ℝ) :=
  periodicCircleJet (fun θ => ∫ t in a..b, f t θ)
    (periodicCircleIntervalIntegral_periodic f hp a b)
    (scalarIntervalIntegral_contDiff_and_iteratedDeriv f hf hj a b).1 n

/-- The estimate concerns the actual derivative tower of the actual
integral; the required jet identities have already been proved. -/
theorem periodicCircle_intervalIntegral_sobolev_le
    (f : ℝ → ℝ → ℝ)
    (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hj : ∀ n : ℕ, Continuous (fun z : ℝ × ℝ => iteratedDeriv n (f z.1) z.2))
    (hp : ∀ t, Function.Periodic (f t) P)
    {a b : ℝ} (hab : a ≤ b) (s : ℕ) :
    circleRealSobolevNorm (s : ℝ) (periodicCircleIntegralJet f hf hj hp a b 0) ≤
      (2 : ℝ) ^ (s + 1) * ∫ t in a..b,
        circleRealSobolevNorm (s : ℝ) (periodicCircleJet (f t) (hp t) (hf t) 0) := by
  have hI := scalarIntervalIntegral_contDiff_and_iteratedDeriv f hf hj a b
  refine circle_real_sobolevNorm_intervalIntegral_le
    (periodicCircleIntegralJet f hf hj hp a b)
    (fun t n => periodicCircleJet (f t) (hp t) (hf t) n) hab
    (periodicCircleJet_hasDerivAt _ _ hI.1)
    (fun t _ => periodicCircleJet_hasDerivAt (f t) (hp t) (hf t))
    (fun n => (continuous_periodicCircleJet_family f hp hf n (hj n)).continuousOn)
    ?_ s
  intro n x
  induction x using QuotientAddGroup.induction_on
  rename_i θ
  simp only [periodicCircleIntegralJet, periodicCircleJet_coe_apply]
  exact hI.2 n θ

end ContinuousFlexibility.Analysis
