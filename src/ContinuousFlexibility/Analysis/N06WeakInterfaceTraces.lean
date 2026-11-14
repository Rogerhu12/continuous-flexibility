module

public import ContinuousFlexibility.Analysis.N06RootTraceFromInterior
public import ContinuousFlexibility.Analysis.N06WeakModeRegularity

/-!
# Actual interface traces forced by the original weak modal equation

The original L2 unknown has a single C1 representative across every
interior cut where the radial leading coefficient stays nonzero. Any
one-sided C1 representatives of that same unknown therefore have the
same value and derivative at the cut. Their arbitrary extensions outside
their own intervals play no role.

This obtains transmission from the given distributional equation; it
does not add matching traces to the domain as an assumption.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Radial
open scoped ContDiff Topology

/-- A common C1 representative identifies the true endpoint jets of two
one-sided representatives known only almost everywhere. -/
theorem n06_cauchyData_eq_of_adjacent_ae
    {l r s : ℝ} (hlr : l < r) (hrs : r < s)
    {u v vl vr : ℝ → ℝ}
    (hv : ContDiff ℝ 1 v) (hvl : ContDiff ℝ 1 vl) (hvr : ContDiff ℝ 1 vr)
    (huv : u =ᵐ[volume.restrict (Ioo l s)] v)
    (hul : u =ᵐ[volume.restrict (Ioo l r)] vl)
    (hur : u =ᵐ[volume.restrict (Ioo r s)] vr) :
    vl r = vr r ∧ deriv vl r = deriv vr r := by
  have hsubL : Ioo l r ⊆ Ioo l s := fun _ hx => ⟨hx.1, hx.2.trans hrs⟩
  have hsubR : Ioo r s ⊆ Ioo l s := fun _ hx => ⟨hlr.trans hx.1, hx.2⟩
  have hleft : vl =ᵐ[volume.restrict (Ioo l r)] v :=
    hul.symm.trans (ae_restrict_of_ae_restrict_of_subset hsubL huv)
  have hright : vr =ᵐ[volume.restrict (Ioo r s)] v :=
    hur.symm.trans (ae_restrict_of_ae_restrict_of_subset hsubR huv)
  have hleq : EqOn vl v (Ioo l r) :=
    Measure.eqOn_open_of_ae_eq hleft isOpen_Ioo
      hvl.continuous.continuousOn hv.continuous.continuousOn
  have hreq : EqOn vr v (Ioo r s) :=
    Measure.eqOn_open_of_ae_eq hright isOpen_Ioo
      hvr.continuous.continuousOn hv.continuous.continuousOn
  have hL := n06_cauchyData_eq_of_eqOn_Ioo_left hlr
    (hvl.differentiable (by norm_num) r) (hv.differentiable (by norm_num) r) hleq
  have hR := cauchyData_eq_of_eqOn_Ioo_right hrs
    (hvr.differentiable (by norm_num) r) (hv.differentiable (by norm_num) r) hreq
  exact ⟨hL.1.trans hR.1.symm, hL.2.trans hR.2.symm⟩

/-- The actual original weak equation, with merely L2 forcing, enforces
the common value and physical flux of all represented pieces. Neither
endpoint values nor an extra transmission-domain condition is assumed. -/
theorem n06_weak_modal_interface_traces
    {l r s : ℝ} (hlr : l < r) (hrs : r < s)
    {a c V u F vl vr : ℝ → ℝ} (j : ℝ)
    (ha : ContDiff ℝ ∞ a) (han : ∀ x ∈ Icc l s, a x ≠ 0)
    (hc : Continuous c) (hV : Continuous V)
    (hu : MemLp u 2 (volume.restrict (Ioo l s)))
    (hF : MemLp F 2 (volume.restrict (Ioo l s)))
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo l s →
        (∫ x in l..s, u x * (-deriv (fun y => a y * deriv φ y) x +
          (j ^ 2 * c x + V x) * φ x)) = ∫ x in l..s, F x * φ x)
    (hvl : ContDiff ℝ 1 vl) (hvr : ContDiff ℝ 1 vr)
    (hul : u =ᵐ[volume.restrict (Ioo l r)] vl)
    (hur : u =ᵐ[volume.restrict (Ioo r s)] vr) :
    vl r = vr r ∧ deriv vl r = deriv vr r ∧
      a r * deriv vl r = a r * deriv vr r := by
  obtain ⟨v, huv, hv, _⟩ :=
    n06_weak_mode_L2_regular (hlr.trans hrs) j ha han hc hV hu hF hweak
  have h := n06_cauchyData_eq_of_adjacent_ae hlr hrs hv hvl hvr huv hul hur
  exact ⟨h.1, h.2, congrArg (a r * ·) h.2⟩

end ContinuousFlexibility.Analysis
