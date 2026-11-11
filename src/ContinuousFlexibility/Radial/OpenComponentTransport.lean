import ContinuousFlexibility.Radial.ReferenceDilation
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Transport of a negative component from an open tail identity

Only equality on the open negative component is needed.  Smoothness
extends both the profile identity and its first derivative to the closed
component, so a component endpoint may coincide with the tail entry.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Filter Real Set
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

/-- Exact open-component transport, including endpoint criticality and
the ordinary radial characteristic integral. -/
theorem negativeRadialComponent_travel_of_open_identity
    {D E : ReferenceData} {R H l h : ℝ}
    (hR : 0 < R) (hH : 0 < H) (hneg : NegativeRadialComponent D l h)
    (ha : E.a < R * l) (hb : R * h < E.b)
    (hD : ContDiff ℝ ∞ D.w) (hE : ContDiff ℝ ∞ E.w)
    (heq : ∀ r ∈ Ioo l h, E.w (R * r) = H * R * D.w r) :
    NegativeRadialComponent E (R * l) (R * h) ∧
      radialTravel E (R * l) (R * h) = radialTravel D l h := by
  have hValues : EqOn (fun r => E.w (R * r)) (fun r => H * R * D.w r) (Ioo l h) :=
    heq
  have hValuesClosed : EqOn (fun r => E.w (R * r))
      (fun r => H * R * D.w r) (Icc l h) := by
    have h := hValues.closure
      (hE.continuous.comp (continuous_const.mul continuous_id))
      (continuous_const.mul hD.continuous)
    rw [closure_Ioo hneg.2.1.ne] at h
    exact h
  have hDeriv : EqOn (fun r => deriv E.w (R * r))
      (fun r => H * deriv D.w r) (Ioo l h) := by
    intro r hr
    have hg : (fun t => E.w (R * t)) =ᶠ[𝓝 r] fun t => H * R * D.w t :=
      Filter.eventuallyEq_of_mem (Ioo_mem_nhds hr.1 hr.2) heq
    calc
      _ = ((H * R) / R) * deriv D.w r :=
        deriv_radius_pullback_of_germ hR.ne'
          (hD.differentiable (by simp) r) (hE.differentiable (by simp) (R * r)) hg
      _ = _ := by field_simp [hR.ne']
  have hDerivClosed : EqOn (fun r => deriv E.w (R * r))
      (fun r => H * deriv D.w r) (Icc l h) := by
    have h := hDeriv.closure
      ((hE.continuous_deriv (by simp)).comp (continuous_const.mul continuous_id))
      (continuous_const.mul (hD.continuous_deriv (by simp)))
    rw [closure_Ioo hneg.2.1.ne] at h
    exact h
  refine ⟨negativeRadialComponent_radius_height_change hR hH hneg ha hb hDerivClosed,
    radialTravel_radius_height_change hR hH.ne' ?_ ?_⟩
  · intro r hr
    apply hValuesClosed
    simpa only [uIcc_of_le hneg.2.1.le] using hr
  · intro r hr
    apply hDerivClosed
    simpa only [uIcc_of_le hneg.2.1.le] using hr

/-- Directly matches R08's open-component-subset-tail hypothesis. -/
theorem negativeRadialComponent_travel_of_open_tail
    {D E : ReferenceData} {R H l h : ℝ} {T : Set ℝ}
    (hR : 0 < R) (hH : 0 < H) (hneg : NegativeRadialComponent D l h)
    (ha : E.a < R * l) (hb : R * h < E.b)
    (hD : ContDiff ℝ ∞ D.w) (hE : ContDiff ℝ ∞ E.w)
    (hsub : Ioo l h ⊆ T)
    (heq : ∀ r ∈ T, E.w (R * r) = H * R * D.w r) :
    NegativeRadialComponent E (R * l) (R * h) ∧
      radialTravel E (R * l) (R * h) = radialTravel D l h :=
  negativeRadialComponent_travel_of_open_identity hR hH hneg ha hb hD hE
    (fun r hr => heq r (hsub hr))

end ContinuousFlexibility.Radial
