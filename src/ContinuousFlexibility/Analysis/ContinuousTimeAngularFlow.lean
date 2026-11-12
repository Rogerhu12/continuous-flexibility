import ContinuousFlexibility.Analysis.ScalarFlowAngularSmooth
import ContinuousFlexibility.Analysis.NeighborhoodCircleFlowRegularity

/-!
# Closed-time angular smoothness of an actual periodic scalar flow

The continuous-time circle-flow API supplies joint continuity and the
actual first variational derivative. The finite spatial bootstrap then
gives all higher angular derivatives, including at both time endpoints.
No time derivative of the vector field or angular derivative of the flow
is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Spatial coordinates come first. The periodic speed and its actual
spatial derivative tower determine genuine closed-time angular regularity. -/
theorem continuousTimeCircleFlow_angularSmooth
    {F Θ : PolarPoint → ℝ} {a b P : ℝ} (hab : a ≤ b) (hP : 0 < P)
    (hF : ∀ n : ℕ, ScalarSpatialRegularity n F)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun x => F (x, t)) P)
    (htime : ∀ x : ℝ, ContinuousOn (fun t => Θ (x, t)) (Icc a b))
    (hinit : ∀ x : ℝ, Θ (x, a) = x)
    (hflow : ∀ x t : ℝ, t ∈ Ioo a b →
      HasDerivAt (fun r => Θ (x, r)) (F (Θ (x, t), t)) t) :
    (∀ t ∈ Icc a b, ContDiff ℝ ∞ (fun x => Θ (x, t))) ∧
      ∀ n : ℕ, ContinuousOn
        (fun p : PolarPoint => iteratedDeriv n (fun x => Θ (x, p.2)) p.1)
        ((univ : Set ℝ) ×ˢ Icc a b) := by
  let G : PolarPoint → ℝ := fun p => F (p.2, p.1)
  let D : PolarPoint → ℝ := fun p => scalarSpatialDerivative F (p.2, p.1)
  let T : PolarPoint → ℝ := fun p => Θ (p.2, p.1)
  have hD : Continuous D :=
    ((hF 1).2.2.continuous).comp (continuous_snd.prodMk continuous_fst)
  have hangle (t x : ℝ) : HasDerivAt (fun y => G (t, y)) (D (t, x)) x :=
    ((hF 1).2.1 x t).hasDerivAt
  have hT : ContinuousOn T (Icc a b ×ˢ (univ : Set ℝ)) :=
    continuousAngleFlow_continuousOn hD hangle hP hperiod htime hinit
      (fun t ht x => hflow x t ht)
  have hΘ : ContinuousOn Θ ((univ : Set ℝ) ×ˢ Icc a b) :=
    hT.comp (continuousOn_snd.prodMk continuousOn_fst)
      (fun p hp => ⟨hp.2, mem_univ p.1⟩)
  apply scalarFlow_angularSmooth_of_variationalFormula hab hF hΘ
  intro x t ht
  exact continuousAngleFlow_hasDerivAt_angle_of_continuous hD hangle hT hinit
    (fun r hr y => hflow y r hr) ht x

/-- A continuous radial factor is allowed to vanish or to arise as a
totalized square root. Only its continuity is used. -/
theorem continuousTimeCircleFlow_angularSmooth_separated
    {d c Θ : PolarPoint → ℝ} {ρ : ℝ → ℝ} {a b P : ℝ}
    (hab : a ≤ b) (hP : 0 < P)
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c) (hρ : Continuous ρ)
    (hperiod : ∀ t : ℝ,
      Function.Periodic (fun x => d (x, t) - ρ t * c (x, t)) P)
    (htime : ∀ x : ℝ, ContinuousOn (fun t => Θ (x, t)) (Icc a b))
    (hinit : ∀ x : ℝ, Θ (x, a) = x)
    (hflow : ∀ x t : ℝ, t ∈ Ioo a b →
      HasDerivAt (fun r => Θ (x, r))
        (d (Θ (x, t), t) - ρ t * c (Θ (x, t), t)) t) :
    (∀ t ∈ Icc a b, ContDiff ℝ ∞ (fun x => Θ (x, t))) ∧
      ∀ n : ℕ, ContinuousOn
        (fun p : PolarPoint => iteratedDeriv n (fun x => Θ (x, p.2)) p.1)
        ((univ : Set ℝ) ×ˢ Icc a b) := by
  apply continuousTimeCircleFlow_angularSmooth
    (F := fun p : PolarPoint => d p - ρ p.2 * c p)
    hab hP _ hperiod htime hinit hflow
  intro n
  simpa only [sub_eq_add_neg] using
    (scalarSpatialRegularity_of_contDiff hd n).add
      (((ScalarSpatialRegularity.timeOnly hρ n).mul
        (scalarSpatialRegularity_of_contDiff hc n)).neg)

end ContinuousFlexibility.Analysis
