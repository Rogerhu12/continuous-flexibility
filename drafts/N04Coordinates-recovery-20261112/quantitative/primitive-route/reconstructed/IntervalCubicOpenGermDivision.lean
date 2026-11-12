import ContinuousFlexibility.Analysis.IntervalCubicGermDivision

/-!
# Cubic division from interior germs alone

The smooth representative has genuine zero jets at its boundary circles.
The actual field is only compared inside the open cylinder: its values
and regularity at ambient endpoints are not assumptions. Continuity of
the representative's mixed derivative extends the interior bound to the
closed interval before applying the existing loss-six estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem intervalRadialCubicQuotient_of_open_germs
    {F f : PolarPoint → ℝ} {l r : ℝ}
    (hF : ContDiff ℝ ∞ F) (hlr : l < r)
    (he : ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ), F =ᶠ[𝓝 p] f)
    (hleft : ∀ θ k, k ≤ 2 → radialBoundaryJet F l k θ = 0)
    (hright : ∀ θ k, k ≤ 2 → radialBoundaryJet F r k θ = 0) :
    ContDiff ℝ ∞ (intervalRadialCubicQuotient F l r) ∧
      (∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ),
        f p = ((p.1 - l) * (r - p.1)) ^ 3 * intervalRadialCubicQuotient F l r p) ∧
      ∀ a b : ℕ, ∀ M : ℝ, ∀ p ∈ Icc l r ×ˢ (univ : Set ℝ),
        (∀ x ∈ Ioo l r, |mixedDerivative (a + 6) b f (x, p.2)| ≤ M) →
        |mixedDerivative a b (intervalRadialCubicQuotient F l r) p| ≤ M / 36 := by
  obtain ⟨hQ, hfactor, hquotient⟩ :=
    intervalRadialCubicQuotient_of_closed_germs (f := F) hF hlr
      (fun _ _ => Filter.EventuallyEq.rfl) hleft hright
  refine ⟨hQ, ?_, ?_⟩
  · intro p hp
    exact (he p hp).eq_of_nhds.symm.trans
      (hfactor p ⟨⟨hp.1.1.le, hp.1.2.le⟩, mem_univ _⟩)
  · intro a b M p hp hraw
    apply hquotient a b M p hp
    have hcont : Continuous
        (fun x : ℝ => |mixedDerivative (a + 6) b F (x, p.2)|) :=
      ((contDiff_mixedDerivative hF (a + 6) b).continuous.comp
        (continuous_id.prodMk continuous_const)).abs
    intro x hx
    have hxclosure : x ∈ closure (Ioo l r) := by
      simpa only [closure_Ioo hlr.ne] using hx
    apply le_on_closure (s := Ioo l r)
      (f := fun t : ℝ => |mixedDerivative (a + 6) b F (t, p.2)|)
      (g := fun _ => M) ?_ hcont.continuousOn continuousOn_const hxclosure
    intro t ht
    rw [mixedDerivative_eq_of_germ (he (t, p.2) ⟨ht, mem_univ _⟩) (a + 6) b]
    exact hraw t ht

end ContinuousFlexibility.Analysis
