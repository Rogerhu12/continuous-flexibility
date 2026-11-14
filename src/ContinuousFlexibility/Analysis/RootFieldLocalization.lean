import ContinuousFlexibility.Analysis.OneHighCircleFlowLocalization
import ContinuousFlexibility.Analysis.OneSidedOrdinaryJets
import ContinuousFlexibility.Analysis.CylinderMixedJetNorms

/-!
# One fixed smooth localization of a root coefficient field

The clamp maps the entire radial line into the original root strip and
equals the identity on its middle half. All ordinary jets therefore
agree on the middle quarter, including its endpoints. The quantitative
flow input only uses that quarter, so no derivatives of the clamp enter
the actual field bounds there.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def rootFieldLocalization (F : PolarPoint → ℝ) {R : ℝ} (hR : 0 < R) : PolarPoint → ℝ :=
  circleFlowLocalizedSpeed F (neg_le_self (half_pos hR).le) (half_pos hR)

theorem contDiff_rootFieldLocalization {F : PolarPoint → ℝ} {R : ℝ} (hR : 0 < R)
    (hF : ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ (univ : Set ℝ))) :
    ContDiff ℝ ∞ (rootFieldLocalization F hR) := by
  apply contDiff_circleFlowLocalizedSpeed
  apply hF.mono
  intro p hp
  refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith [hp.1.1, hp.1.2]

theorem rootFieldLocalization_periodic {F : PolarPoint → ℝ} {R T : ℝ} (hR : 0 < R)
    (hperiod : Function.Periodic F (0, T)) :
    ∀ r : ℝ, Function.Periodic (fun θ => rootFieldLocalization F hR (r, θ)) T := by
  apply circleFlowLocalizedSpeed_periodic
  intro r _ θ
  change F (r, θ + T) = F (r, θ)
  simpa only [Prod.mk_add_mk, add_zero] using hperiod (r, θ)

theorem rootFieldLocalization_eqOn {F : PolarPoint → ℝ} {R : ℝ} (hR : 0 < R) :
    EqOn (rootFieldLocalization F hR) F
      (Ioo (-(R / 2)) (R / 2) ×ˢ (univ : Set ℝ)) := by
  intro p hp
  exact circleFlowLocalizedSpeed_eq (neg_le_self (half_pos hR).le) (half_pos hR)
    ⟨hp.1.1.le, hp.1.2.le⟩ p.2

theorem iteratedFDeriv_rootFieldLocalization_eq
    {F : PolarPoint → ℝ} {R : ℝ} (hR : 0 < R)
    (n : ℕ) {q : PolarPoint} (hq : |q.1| ≤ R / 4) :
    iteratedFDeriv ℝ n (rootFieldLocalization F hR) q = iteratedFDeriv ℝ n F q := by
  have hq' : q ∈ Ioo (-(R / 2)) (R / 2) ×ˢ (univ : Set ℝ) := by
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith [(abs_le.mp hq).1, (abs_le.mp hq).2]
  exact iteratedFDeriv_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ)
    (rootFieldLocalization_eqOn hR) n hq'

theorem abs_deriv_angular_le_first_frechet {F : PolarPoint → ℝ}
    (hF : ContDiff ℝ ∞ F) (r θ : ℝ) :
    |deriv (fun η => F (r, η)) θ| ≤ ‖iteratedFDeriv ℝ 1 F (r, θ)‖ := by
  have hh := abs_mixedDerivative_le_norm_iteratedFDeriv
    isOpen_univ hF.contDiffOn 0 1 (mem_univ (r, θ))
  simpa only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_one, Nat.zero_add] using hh

end ContinuousFlexibility.Analysis
