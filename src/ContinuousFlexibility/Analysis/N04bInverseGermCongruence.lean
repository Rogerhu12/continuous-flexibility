import ContinuousFlexibility.Analysis.N04bContinuousInverseGerm

/-!
# Transporting inverse germs to globally specified pasted functions

Agreement of both functions in the relevant neighborhoods preserves the
actual inverse germ. A fresh inverse-function-theorem chart uses the
literal new forward function globally.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem n04b_boundaryInverseGerm_of_same_germs
    {F G F₀ G₀ : PolarPoint → PolarPoint} {p : PolarPoint}
    (hF : ContDiffAt ℝ ∞ F p) (hJ : planeJacobian F p ≠ 0)
    (hOld : CanonicalBoundaryInverseGerm F₀ G₀ p)
    (hForward : F =ᶠ[𝓝 p] F₀)
    (hInverse : G =ᶠ[𝓝 (F₀ p)] G₀) :
    CanonicalBoundaryInverseGerm F G p := by
  obtain ⟨e, he, hp, hsmooth, hG₀⟩ := hOld
  have hImage : F p = F₀ p := hForward.self_of_nhds
  have hGe : G =ᶠ[𝓝 (F₀ p)] e.symm := hInverse.trans hG₀
  have hGSmooth : ContDiffAt ℝ ∞ G (F₀ p) :=
    hsmooth.congr_of_eventuallyEq hGe
  have hValue : G (F₀ p) = p := by
    rw [hGe.self_of_nhds, ← he]
    exact e.left_inv hp
  have hTarget : F₀ p ∈ e.target := by
    rw [← he]
    exact e.map_source hp
  have hNearForward : ∀ᶠ q in 𝓝 (F₀ p), F (G q) = F₀ (G q) := by
    apply hGSmooth.continuousAt.tendsto.eventually
    rwa [hValue]
  have hRight : ∀ᶠ q in 𝓝 (F₀ p), F (G q) = q := by
    filter_upwards [hNearForward, hGe, e.open_target.mem_nhds hTarget] with q hq hGeq hqt
    rw [hq, hGeq, ← he]
    exact e.right_inv hqt
  apply n04b_boundaryInverseGerm_of_continuous_rightInverse hF hJ
  · simpa only [hImage] using hGSmooth.continuousAt
  · simpa only [hImage] using hValue
  · simpa only [hImage] using hRight

end ContinuousFlexibility.Analysis
