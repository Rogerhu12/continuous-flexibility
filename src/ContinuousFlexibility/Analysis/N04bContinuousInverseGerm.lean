import ContinuousFlexibility.Analysis.N04bPlanarInverseGerm

/-!
# Genuine inverse germs for the literal forward function

An actual right inverse that is continuous at the relevant target point
must agree with the smooth inverse supplied by the inverse function
theorem. The theorem is applied to the specified forward function itself,
so the resulting partial homeomorphism has that function globally as its
forward map, even when the function was constructed by local pasting.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem n04b_boundaryInverseGerm_of_continuous_rightInverse
    {F G : PolarPoint → PolarPoint} {p : PolarPoint}
    (hF : ContDiffAt ℝ ∞ F p) (hJ : planeJacobian F p ≠ 0)
    (hG : ContinuousAt G (F p)) (hValue : G (F p) = p)
    (hRight : ∀ᶠ q in 𝓝 (F p), F (G q) = q) :
    CanonicalBoundaryInverseGerm F G p := by
  obtain ⟨e, he, hp, hsmooth⟩ :=
    exists_smooth_localInverse_of_planeJacobian_ne_zero hF hJ
  have hSource : e.source ∈ 𝓝 (G (F p)) := by
    rw [hValue]
    exact e.open_source.mem_nhds hp
  have hGSource : ∀ᶠ q in 𝓝 (F p), G q ∈ e.source :=
    hG.tendsto.eventually hSource
  refine ⟨e, he, hp, hsmooth, ?_⟩
  filter_upwards [hGSource, hRight] with q hq hright
  calc
    G q = e.symm (e (G q)) := (e.left_inv hq).symm
    _ = e.symm (F (G q)) := congrArg e.symm (congrFun he (G q))
    _ = e.symm q := congrArg e.symm hright

/-- The stored inverse itself inherits the smooth full-neighborhood germ. -/
theorem n04b_contDiffAt_inverse_of_boundaryInverseGerm
    {F G : PolarPoint → PolarPoint} {p : PolarPoint}
    (h : CanonicalBoundaryInverseGerm F G p) :
    ContDiffAt ℝ ∞ G (F p) := by
  obtain ⟨e, _, _, hsmooth, heq⟩ := h
  exact hsmooth.congr_of_eventuallyEq heq

end ContinuousFlexibility.Analysis
