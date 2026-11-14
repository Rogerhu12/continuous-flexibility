module

public import ContinuousFlexibility.Analysis.CircleFlowVariationKernel
public import ContinuousFlexibility.Analysis.OneHighCircleFlowLowGeometryBasic
public import ContinuousFlexibility.Analysis.OneHighCircleFlowJets

/-!
# Actual angular regularity of the scalar flow variation kernel

The supplied classical trajectories determine all angular derivatives.
A compact smooth time change proves smoothness of the true reciprocal
Jacobian kernel, and the compact quotient argument descends continuity
of its angular jets to the original closed time interval. Clamping time
then provides total continuous families for compact integration.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

def circleFlowVariationKernel (A Θ : PolarPoint → ℝ) (t θ : ℝ) : ℝ :=
  circleLiftVariationKernel (fun η => A (t, η)) (fun η => Θ (t, η)) θ

theorem circleFlowVariationKernel_eq_div (A Θ : PolarPoint → ℝ) (t θ : ℝ) :
    circleFlowVariationKernel A Θ t θ =
      A (t, Θ (t, θ)) / deriv (fun η => Θ (t, η)) θ :=
  circleLiftVariationKernel_apply _ _ _

def circleFlowClampedVariationKernel (A Θ : PolarPoint → ℝ)
    (a b t θ : ℝ) : ℝ :=
  circleFlowVariationKernel A Θ (max a (min t b)) θ

theorem circleFlowClampedVariationKernel_eq {A Θ : PolarPoint → ℝ} {a b t : ℝ}
    (ht : t ∈ Icc a b) :
    circleFlowClampedVariationKernel A Θ a b t = circleFlowVariationKernel A Θ t := by
  funext θ
  change circleFlowVariationKernel A Θ (max a (min t b)) θ =
    circleFlowVariationKernel A Θ t θ
  rw [min_eq_left ht.2, max_eq_right ht.1]

variable {P : ℝ} [hP : Fact (0 < P)] {G Θ A : PolarPoint → ℝ} {a b : ℝ}
  (hG : ContDiff ℝ ∞ G)
  (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
  (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
  (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
  (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
    HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)

include hG hperiod hΘ hinit hflow

theorem circleFlowVariationKernel_periodic
    (hAperiod : ∀ t : ℝ, Function.Periodic (fun θ => A (t, θ)) P)
    {t : ℝ} (ht : t ∈ Icc a b) :
    Function.Periodic (circleFlowVariationKernel A Θ t) P :=
  periodic_circleLiftVariationKernel (hAperiod t)
    (circleFlow_lift_add hG hperiod hΘ hinit hflow ht)

theorem circleFlowVariationKernel_contDiff
    (hA : ContDiff ℝ ∞ A) {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiff ℝ ∞ (circleFlowVariationKernel A Θ t) :=
  contDiff_circleLiftVariationKernel
    (hA.comp (contDiff_const.prodMk contDiff_id))
    (circleFlow_contDiff_angle hG hP.out hperiod hΘ hinit hflow ht)
    (Real.exp_pos _)
    (fun θ => (circleFlow_deriv_bounds_lowSobolev hG hperiod hΘ hinit hflow ht θ).1)

/-- Endpoint continuity of every actual angular derivative of the
reciprocal-Jacobian forcing kernel follows from the true flow equation. -/
theorem circleFlowVariationKernel_continuousOn_angularJet
    (hA : ContDiff ℝ ∞ A) (n : ℕ) :
    ContinuousOn (fun p : PolarPoint =>
      iteratedDeriv n (circleFlowVariationKernel A Θ p.1) p.2)
      (Icc a b ×ˢ (univ : Set ℝ)) := by
  by_cases hab : a ≤ b
  · have hΨ := contDiff_circleFlow_timeChange hG hP.out hperiod hΘ hinit hflow
      (contDiff_circleFlowCompactTime a b) (circleFlowCompactTime_zero a b)
      (circleFlowCompactTime_mem hab)
    have hJ : ContDiff ℝ ∞ (fun p : PolarPoint =>
        deriv (fun η => Θ (circleFlowCompactTime a b p.1, η)) p.2) := by
      have he : Statements.mixedDerivative 0 1
          (fun p : PolarPoint => Θ (circleFlowCompactTime a b p.1, p.2)) =
          (fun p : PolarPoint =>
            deriv (fun η => Θ (circleFlowCompactTime a b p.1, η)) p.2) := by
        funext p
        simp only [Statements.mixedDerivative, iteratedDeriv_zero, iteratedDeriv_one]
      have hc := contDiffOn_univ.mp
        (Statements.contDiffOn_mixedDerivative isOpen_univ hΨ.contDiffOn 0 1)
      rw [he] at hc
      exact hc
    have hJn (p : PolarPoint) :
        deriv (fun η => Θ (circleFlowCompactTime a b p.1, η)) p.2 ≠ 0 :=
      ne_of_gt ((Real.exp_pos _).trans_le
        (circleFlow_deriv_bounds_lowSobolev hG hperiod hΘ hinit hflow
          (circleFlowCompactTime_mem hab p.1) p.2).1)
    have hN : ContDiff ℝ ∞ (fun p : PolarPoint =>
        A (circleFlowCompactTime a b p.1, Θ (circleFlowCompactTime a b p.1, p.2))) :=
      hA.comp (((contDiff_circleFlowCompactTime a b).comp contDiff_fst).prodMk hΨ)
    have hK : ContDiff ℝ ∞ (fun p : PolarPoint =>
        circleFlowVariationKernel A Θ (circleFlowCompactTime a b p.1) p.2) := by
      have he : (fun p : PolarPoint =>
          circleFlowVariationKernel A Θ (circleFlowCompactTime a b p.1) p.2) =
          (fun p : PolarPoint =>
            A (circleFlowCompactTime a b p.1, Θ (circleFlowCompactTime a b p.1, p.2)) /
              deriv (fun η => Θ (circleFlowCompactTime a b p.1, η)) p.2) :=
        funext (fun p => circleFlowVariationKernel_eq_div A Θ _ _)
      rw [he]
      exact hN.fun_div hJ hJn
    have hjet : Continuous (fun p : PolarPoint =>
        iteratedDeriv n
          (circleFlowVariationKernel A Θ (circleFlowCompactTime a b p.1)) p.2) := by
      have hc := (contDiffOn_univ.mp
        (Statements.contDiffOn_mixedDerivative isOpen_univ hK.contDiffOn 0 n)).continuous
      exact hc.congr (fun p => by
        simp only [Statements.mixedDerivative, iteratedDeriv_zero])
    exact continuousOn_of_compact_time_reparam
      (contDiff_circleFlowCompactTime a b).continuous
      (fun s _ => circleFlowCompactTime_mem hab s)
      (circleFlowCompactTime_surjOn a b) hjet
  · rw [Icc_eq_empty_of_lt (lt_of_not_ge hab), empty_prod]
    exact continuousOn_empty _

theorem circleFlowClampedVariationKernel_contDiff
    (hA : ContDiff ℝ ∞ A) (hab : a ≤ b) (t : ℝ) :
    ContDiff ℝ ∞ (circleFlowClampedVariationKernel A Θ a b t) :=
  circleFlowVariationKernel_contDiff hG hperiod hΘ hinit hflow hA
    ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

theorem circleFlowClampedVariationKernel_periodic
    (hAperiod : ∀ t : ℝ, Function.Periodic (fun θ => A (t, θ)) P)
    (hab : a ≤ b) (t : ℝ) :
    Function.Periodic (circleFlowClampedVariationKernel A Θ a b t) P :=
  circleFlowVariationKernel_periodic hG hperiod hΘ hinit hflow hAperiod
    ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

theorem circleFlowClampedVariationKernel_continuous_angularJet
    (hA : ContDiff ℝ ∞ A) (hab : a ≤ b) (n : ℕ) :
    Continuous (fun p : PolarPoint =>
      iteratedDeriv n (circleFlowClampedVariationKernel A Θ a b p.1) p.2) := by
  have hc : Continuous (fun t : ℝ => max a (min t b)) :=
    continuous_const.max (continuous_id.min continuous_const)
  exact (circleFlowVariationKernel_continuousOn_angularJet hG hperiod hΘ hinit hflow hA n).comp_continuous
    ((hc.comp continuous_fst).prodMk continuous_snd)
      (fun p => ⟨⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩, mem_univ p.2⟩)

end ContinuousFlexibility.Analysis
