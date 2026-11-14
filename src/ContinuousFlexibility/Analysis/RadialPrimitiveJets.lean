module

public import ContinuousFlexibility.Analysis.MaterialRadiusJets
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Bounded jets of the actual reference primitive

The reference profile is globally smooth and vanishes outside the closed
annulus. Its integral from the right endpoint is a global primitive with
bounded jets of every order, including order zero. These are the fixed
unweighted input bounds for compact radial height tests.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

set_option backward.isDefEq.respectTransparency false

theorem iteratedDeriv_hasCompactSupport {f : ℝ → ℝ}
    (hf : HasCompactSupport f) (n : ℕ) : HasCompactSupport (iteratedDeriv n f) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv

theorem iteratedDeriv_bounded_of_contDiff_compactSupport {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hsupp : HasCompactSupport f) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, |iteratedDeriv n f x| ≤ K := by
  obtain ⟨K, hK⟩ := (iteratedDeriv_hasCompactSupport hsupp n).exists_bound_of_continuous
    (hf.continuous_iteratedDeriv n (by simp))
  refine ⟨max K 0, le_max_right _ _, fun x => ?_⟩
  have hb : |iteratedDeriv n f x| ≤ K := by simpa only [Real.norm_eq_abs] using hK x
  exact hb.trans (le_max_left _ _)

theorem referenceProfile_hasCompactSupport {D : ReferenceData}
    (hD : RadialProfileGeometry D) : HasCompactSupport D.w := by
  apply HasCompactSupport.intro (K := Icc D.a D.b) isCompact_Icc
  intro r hr
  simp only [mem_Icc, not_and_or, not_le] at hr
  rcases hr with hr | hr
  · exact hD.2.2.1.2 r (Or.inl hr.le)
  · exact hD.2.2.1.2 r (Or.inr hr.le)

def referenceRadialPrimitive (D : ReferenceData) (r : ℝ) : ℝ :=
  ∫ t in D.b..r, D.w t

theorem referenceRadialPrimitive_hasDerivAt {D : ReferenceData}
    (hD : RadialProfileGeometry D) (r : ℝ) :
    HasDerivAt (referenceRadialPrimitive D) (D.w r) r :=
  intervalIntegral.integral_hasDerivAt_right
    (hD.2.2.1.1.continuous.intervalIntegrable D.b r)
    hD.2.2.1.1.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    hD.2.2.1.1.continuous.continuousAt

theorem referenceRadialPrimitive_contDiff {D : ReferenceData}
    (hD : RadialProfileGeometry D) : ContDiff ℝ ∞ (referenceRadialPrimitive D) := by
  have hd : deriv (referenceRadialPrimitive D) = D.w :=
    funext (fun r => (referenceRadialPrimitive_hasDerivAt hD r).deriv)
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun r => (referenceRadialPrimitive_hasDerivAt hD r).differentiableAt, ?_⟩
  rw [hd]
  exact hD.2.2.1.1

/-- The zero-th primitive bound uses the full integral of the compactly
supported profile; positive orders use the actual profile derivatives. -/
theorem referenceRadialPrimitive_iteratedDeriv_bounded {D : ReferenceData}
    (hD : RadialProfileGeometry D) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ,
      |iteratedDeriv n (referenceRadialPrimitive D) x| ≤ K := by
  cases n with
  | zero =>
    have hwi : Integrable D.w := hD.2.2.1.1.continuous.integrable_of_hasCompactSupport
      (referenceProfile_hasCompactSupport hD)
    refine ⟨∫ t : ℝ, ‖D.w t‖, integral_nonneg (fun t => norm_nonneg _), fun x => ?_⟩
    have hb : ‖∫ t in D.b..x, D.w t‖ ≤ ∫ t : ℝ, ‖D.w t‖ :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
        (setIntegral_le_integral hwi.norm (Eventually.of_forall (fun t => norm_nonneg _)))
    simpa only [iteratedDeriv_zero, referenceRadialPrimitive, Real.norm_eq_abs] using hb
  | succ n =>
    obtain ⟨K, hK, hb⟩ := iteratedDeriv_bounded_of_contDiff_compactSupport
      hD.2.2.1.1 (referenceProfile_hasCompactSupport hD) n
    refine ⟨K, hK, fun x => ?_⟩
    have hd : deriv (referenceRadialPrimitive D) = D.w :=
      funext (fun r => (referenceRadialPrimitive_hasDerivAt hD r).deriv)
    rw [iteratedDeriv_succ', hd]
    exact hb x

end ContinuousFlexibility.Statements
