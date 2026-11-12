import ContinuousFlexibility.Analysis.OneSidedBoundaryJets
import ContinuousFlexibility.Analysis.PositiveFiberInterpolationSymmetry
import ContinuousFlexibility.Analysis.AngularTaylorPolynomial

/-!
# Global Taylor representatives of genuine one-sided boundary fields

The angular coefficients are the actual radial derivatives at the root
circle.  The source needs only pointwise smoothness on that circle.
Equations on one open side determine the same boundary coefficients.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def oneSidedBoundaryTaylorRepresentative (n : ℕ) (c : ℝ)
    (F : PolarPoint → ℝ) : PolarPoint → ℝ :=
  boundaryTaylorPolynomial n c (radialBoundaryJet F c)

theorem contDiff_oneSidedBoundaryTaylorRepresentative
    {F : PolarPoint → ℝ} (c : ℝ)
    (hF : ∀ θ, ContDiffAt ℝ ∞ F (c, θ)) (n : ℕ) :
    ContDiff ℝ ∞ (oneSidedBoundaryTaylorRepresentative n c F) :=
  contDiff_boundaryTaylorPolynomial
    (fun j _ => contDiff_radialBoundaryJet_of_contDiffAt c hF j) c

theorem radialBoundaryJet_oneSidedBoundaryTaylorRepresentative
    (F : PolarPoint → ℝ) (n : ℕ) (c : ℝ) {k : ℕ}
    (hk : k ≤ n) (θ : ℝ) :
    radialBoundaryJet (oneSidedBoundaryTaylorRepresentative n c F) c k θ =
      radialBoundaryJet F c k θ :=
  iteratedDeriv_boundaryTaylorPolynomial n c (radialBoundaryJet F c) hk θ

theorem iteratedFDeriv_oneSidedBoundaryTaylorRepresentative
    {F : PolarPoint → ℝ} {a b c : ℝ} (hab : a < b)
    (hF : ContDiffOn ℝ ∞ F (Ioo a b ×ˢ (univ : Set ℝ)))
    (hc : c ∈ Icc a b) (hFc : ∀ θ, ContDiffAt ℝ ∞ F (c, θ))
    (n : ℕ) {k : ℕ} (hk : k ≤ n) (θ : ℝ) :
    iteratedFDeriv ℝ k (oneSidedBoundaryTaylorRepresentative n c F) (c, θ) =
      iteratedFDeriv ℝ k F (c, θ) := by
  have hR := contDiff_oneSidedBoundaryTaylorRepresentative c hFc n
  exact iteratedFDeriv_eq_of_radialBoundaryJets_eq_on_closedStrip hab
    hR.contDiffOn hF hc (fun _ => hR.contDiffAt) hFc
    (fun j hj η => radialBoundaryJet_oneSidedBoundaryTaylorRepresentative F n c hj η) hk θ

theorem radialBoundaryJet_angleAffine_on_closedStrip
    {F : PolarPoint → ℝ} {a b c α β : ℝ} {τ : ℝ → ℝ}
    (hab : a < b) (hc : c ∈ Icc a b)
    (hFc : ∀ θ, ContDiffAt ℝ ∞ F (c, θ)) (hτ : ContDiff ℝ ∞ τ)
    (he : ∀ x ∈ Ioo a b, ∀ θ, F (x, τ θ) = β + α * F (x, θ))
    (j : ℕ) (θ : ℝ) :
    radialBoundaryJet F c j (τ θ) =
      (if j = 0 then β else 0) + α * radialBoundaryJet F c j θ := by
  have hmap : ContDiffAt ℝ ∞
      (fun p : PolarPoint => (p.1, τ p.2)) (c, θ) :=
    (contDiff_fst.prodMk (hτ.comp contDiff_snd)).contDiffAt
  have hleft : ContDiffAt ℝ ∞ (fun p : PolarPoint => F (p.1, τ p.2)) (c, θ) :=
    ContDiffAt.fun_comp (f := fun p : PolarPoint => (p.1, τ p.2)) (g := F)
      (c, θ) (hFc (τ θ)) hmap
  have hright : ContDiffAt ℝ ∞ (fun p : PolarPoint => β + α * F p) (c, θ) :=
    contDiffAt_const.add (contDiffAt_const.mul (hFc θ))
  have hjet := mixedDerivative_eq_on_closedStrip_of_contDiffAt
    hleft hright hab (fun p hp => he p.1 hp.1 p.2) hc j 0
  have hslice :
      iteratedDeriv j (fun x => F (x, τ θ)) c =
        iteratedDeriv j (fun x => β + α * F (x, θ)) c := by
    simpa only [mixedDerivative, iteratedDeriv_zero] using hjet
  by_cases hj : j = 0
  · subst j
    simpa only [radialBoundaryJet, iteratedDeriv_zero, if_pos rfl, ↓reduceIte] using hslice
  · rw [iteratedDeriv_const_add (Nat.pos_of_ne_zero hj) β,
      iteratedDeriv_const_mul_field] at hslice
    simpa only [radialBoundaryJet, if_neg hj, zero_add] using hslice

theorem oneSidedBoundaryTaylorRepresentative_angleInvariant
    {F : PolarPoint → ℝ} {a b c : ℝ} {τ : ℝ → ℝ}
    (hab : a < b) (hc : c ∈ Icc a b)
    (hFc : ∀ θ, ContDiffAt ℝ ∞ F (c, θ)) (hτ : ContDiff ℝ ∞ τ)
    (he : ∀ x ∈ Ioo a b, ∀ θ, F (x, τ θ) = F (x, θ))
    (n : ℕ) (x θ : ℝ) :
    oneSidedBoundaryTaylorRepresentative n c F (x, τ θ) =
      oneSidedBoundaryTaylorRepresentative n c F (x, θ) := by
  apply boundaryTaylorPolynomial_angleInvariant τ
  intro j _ η
  simpa only [ite_self, zero_add, one_mul] using
    radialBoundaryJet_angleAffine_on_closedStrip (α := 1) (β := 0)
      hab hc hFc hτ (fun r hr t => by simpa only [zero_add, one_mul] using he r hr t) j η

theorem oneSidedBoundaryTaylorRepresentative_lift
    {F : PolarPoint → ℝ} {a b c : ℝ}
    (hab : a < b) (hc : c ∈ Icc a b)
    (hFc : ∀ θ, ContDiffAt ℝ ∞ F (c, θ))
    (he : ∀ x ∈ Ioo a b, ∀ θ, F (x, θ + Real.pi) = F (x, θ) + Real.pi)
    (n : ℕ) (x θ : ℝ) :
    oneSidedBoundaryTaylorRepresentative n c F (x, θ + Real.pi) =
      oneSidedBoundaryTaylorRepresentative n c F (x, θ) + Real.pi := by
  have hdata (j : ℕ) (η : ℝ) :=
    radialBoundaryJet_angleAffine_on_closedStrip (α := 1) (β := Real.pi)
      (τ := fun t : ℝ => t + Real.pi)
      hab hc hFc (contDiff_id.add contDiff_const)
      (fun r hr t => by simpa only [one_mul, add_comm] using he r hr t) j η
  apply boundaryTaylorPolynomial_period_add
  · intro η
    simpa only [if_pos rfl, ↓reduceIte, one_mul, add_comm] using hdata 0 η
  · intro j hj _ η
    simpa only [if_neg (Nat.ne_of_gt hj), one_mul, zero_add] using hdata j η

theorem oneSidedBoundaryTaylorRepresentative_odd
    {F : PolarPoint → ℝ} {a b c : ℝ}
    (hab : a < b) (hc : c ∈ Icc a b)
    (hFc : ∀ θ, ContDiffAt ℝ ∞ F (c, θ))
    (he : ∀ x ∈ Ioo a b, ∀ θ, F (x, -θ) = -F (x, θ))
    (n : ℕ) (x θ : ℝ) :
    oneSidedBoundaryTaylorRepresentative n c F (x, -θ) =
      -oneSidedBoundaryTaylorRepresentative n c F (x, θ) := by
  apply boundaryTaylorPolynomial_reflect
  intro j _ η
  simpa only [ite_self, zero_add, neg_one_mul] using
    radialBoundaryJet_angleAffine_on_closedStrip (α := -1) (β := 0)
      hab hc hFc contDiff_neg
      (fun r hr t => by simpa only [zero_add, neg_one_mul] using he r hr t) j η

end ContinuousFlexibility.Analysis
