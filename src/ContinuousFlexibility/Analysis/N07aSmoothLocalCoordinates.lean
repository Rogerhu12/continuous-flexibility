import ContinuousFlexibility.Geometry.LocalInverse
import ContinuousFlexibility.Analysis.CanonicalSourceMeasure

/-!
# Genuine smooth local coordinates for a globally smooth map

Continuity of the derivative gives one open neighborhood on which it is
invertible. Restricting the inverse-function chart to this neighborhood
gives smoothness of its inverse at every target point. The construction
uses the original globally smooth map and retains its exact derivative
and inverse derivative at the center.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

/-- A global smooth map with an invertible derivative admits a chart that
is smooth on its entire open source and whose inverse is smooth on its
entire open target. The forward function is unchanged everywhere. -/
theorem n07a_smoothLocalCoordinates
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : E → F} (hH : ContDiff ℝ ∞ H) (a : E) (A : E ≃L[ℝ] F)
    (hder : HasFDerivAt H (A : E →L[ℝ] F) a) :
    ∃ e : OpenPartialHomeomorph E F,
      (e : E → F) = H ∧ a ∈ e.source ∧ H a ∈ e.target ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      HasFDerivAt e.symm (A.symm : F →L[ℝ] E) (H a) ∧
      fderiv ℝ e.symm (H a) = (A.symm : F →L[ℝ] E) := by
  have hn : {z : E | ∃ v : E ≃L[ℝ] F,
      (v : E →L[ℝ] F) = fderiv ℝ H z} ∈ 𝓝 a := by
    have hA := A.nhds
    rw [← hder.fderiv] at hA
    exact (hH.continuous_fderiv (by simp)).continuousAt.preimage_mem_nhds hA
  obtain ⟨U, hU, hUopen, haU⟩ := mem_nhds_iff.mp hn
  let e₀ := hH.contDiffAt.toOpenPartialHomeomorph H hder (by simp)
  let e := e₀.restr U
  have he : (e : E → F) = H := rfl
  have ha : a ∈ e.source := by
    rw [OpenPartialHomeomorph.restr_source' _ _ hUopen]
    exact ⟨hH.contDiffAt.mem_toOpenPartialHomeomorph_source hder (by simp), haU⟩
  have hHa : H a ∈ e.target := by simpa only [he] using e.map_source ha
  have hinv : e.symm (H a) = a := by simpa only [he] using e.left_inv ha
  have hinvs : ContDiffOn ℝ ∞ e.symm e.target := by
    intro y hy
    have hyU : e.symm y ∈ U := by
      have hm := e.map_target hy
      rw [OpenPartialHomeomorph.restr_source' _ _ hUopen] at hm
      exact hm.2
    obtain ⟨v, hv⟩ := hU hyU
    have hd : HasFDerivAt e (v : E →L[ℝ] F) (e.symm y) := by
      rw [he, hv]
      exact (hH.differentiable (by simp) _).hasFDerivAt
    exact (e.contDiffAt_symm hy hd (he ▸ hH.contDiffAt)).contDiffWithinAt
  have hdinv : HasFDerivAt e.symm (A.symm : F →L[ℝ] E) (H a) := by
    apply e.hasFDerivAt_symm hHa
    rw [hinv, he]
    exact hder
  exact ⟨e, he, ha, hHa, he ▸ hH.contDiffOn, hinvs, hdinv, hdinv.fderiv⟩

/-- In the physical plane, a nonzero Jacobian supplies the invertible
derivative and both inverse differential identities at the center. -/
theorem n07a_smoothLocalCoordinates_of_planeJacobian_ne_zero
    {H : PolarPoint → PolarPoint} (hH : ContDiff ℝ ∞ H)
    (a : PolarPoint) (hJ : planeJacobian H a ≠ 0) :
    ∃ e : OpenPartialHomeomorph PolarPoint PolarPoint,
      (e : PolarPoint → PolarPoint) = H ∧ a ∈ e.source ∧ H a ∈ e.target ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (fderiv ℝ e.symm (H a)).comp (fderiv ℝ H a) = ContinuousLinearMap.id ℝ PolarPoint ∧
      (fderiv ℝ H a).comp (fderiv ℝ e.symm (H a)) = ContinuousLinearMap.id ℝ PolarPoint := by
  have hd : (fderiv ℝ H a).det ≠ 0 := by
    rwa [← planeJacobian_eq_fderiv_det]
  let A := (fderiv ℝ H a).toContinuousLinearEquivOfDetNeZero hd
  have hA : (A : PolarPoint →L[ℝ] PolarPoint) = fderiv ℝ H a :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
  have hder : HasFDerivAt H (A : PolarPoint →L[ℝ] PolarPoint) a := by
    rw [hA]
    exact (hH.differentiable (by simp) a).hasFDerivAt
  obtain ⟨e, he, ha, hHa, hes, hinvs, _, hdinv⟩ := n07a_smoothLocalCoordinates hH a A hder
  refine ⟨e, he, ha, hHa, hes, hinvs, ?_, ?_⟩
  · rw [hdinv, ← hA]
    ext v
    simp
  · rw [hdinv, ← hA]
    ext v
    simp

end ContinuousFlexibility.Analysis
