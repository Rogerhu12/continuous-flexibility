module

public import ContinuousFlexibility.Analysis.IntervalWeakPrimitive
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Reflection and almost-everywhere representatives of a weak flux

Reflecting a coordinate reverses the flux sign and the interval order.
The source has no sign change. These identities apply to the actual weak
derivative and use all compactly contained tests in its definition.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem intervalWeak_pairing_congr {a b : ℝ} {p q φ : ℝ → ℝ}
    (hpq : p =ᵐ[volume.restrict (Ioo a b)] q)
    (hφ : Function.support φ ⊆ Ioo a b) :
    (∫ x, p x * φ x) = ∫ x, q x * φ x := by
  apply integral_congr_ae
  filter_upwards [ae_imp_of_ae_restrict hpq] with x hx
  by_cases hxi : x ∈ Ioo a b
  · rw [hx hxi]
  · have hz : φ x = 0 := Function.notMem_support.mp (fun h => hxi (hφ h))
    rw [hz, mul_zero, mul_zero]

theorem HasIntervalWeakDerivative.congr_restrict {a b : ℝ} {p q f g : ℝ → ℝ}
    (h : HasIntervalWeakDerivative a b p f)
    (hpq : p =ᵐ[volume.restrict (Ioo a b)] q)
    (hfg : f =ᵐ[volume.restrict (Ioo a b)] g) :
    HasIntervalWeakDerivative a b q g := by
  intro ψ hψ hcψ hsψ
  rw [← intervalWeak_pairing_congr hpq (support_deriv_subset.trans hsψ),
    h ψ hψ hcψ hsψ,
    intervalWeak_pairing_congr hfg ((subset_tsupport ψ).trans hsψ)]

theorem HasIntervalWeakDerivative.reflect {a b : ℝ} {p g : ℝ → ℝ}
    (h : HasIntervalWeakDerivative a b p g) :
    HasIntervalWeakDerivative (-b) (-a) (fun x => -p (-x)) (fun x => g (-x)) := by
  intro ψ hψ hcψ hsψ
  let φ : ℝ → ℝ := fun x => ψ (-x)
  have hφ : ContDiff ℝ ∞ φ := hψ.comp (contDiff_id.neg)
  have hcφ : HasCompactSupport φ := hcψ.comp_homeomorph (Homeomorph.neg ℝ)
  have hsφ : tsupport φ ⊆ Ioo a b := by
    intro x hx
    have hxψ := hsψ (tsupport_comp_subset_preimage ψ continuous_neg hx)
    change -b < -x ∧ -x < -a at hxψ
    constructor <;> linarith only [hxψ.1, hxψ.2]
  have hdφ (x : ℝ) : deriv φ x = -(deriv ψ (-x)) := by
    exact deriv_comp_neg ψ x
  have hleft : (∫ x, p x * deriv φ x) = ∫ x, -p (-x) * deriv ψ x := by
    calc
      _ = ∫ x, -p x * deriv ψ (-x) := by
        apply integral_congr_ae
        exact ae_of_all _ (fun x => by dsimp only; rw [hdφ]; ring)
      _ = _ := by
        simpa only [neg_neg] using
          (integral_neg_eq_self (fun x : ℝ => -p (-x) * deriv ψ x) volume)
  have hright : (∫ x, g x * φ x) = ∫ x, g (-x) * ψ x := by
    simpa only [φ, neg_neg] using
      (integral_neg_eq_self (fun x : ℝ => g (-x) * ψ x) volume)
  have he := h φ hφ hcφ hsφ
  rw [hleft, hright] at he
  exact he

end ContinuousFlexibility.Analysis
