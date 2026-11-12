import ContinuousFlexibility.Analysis.N07aAngularReferenceFlux
import ContinuousFlexibility.Analysis.N07aAngularMaterialWeights
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Actual endpoint flux and the reference compatibility integral

The natural reference field need only be C¹ inside the annulus. A bounded
radial first derivative and the actual flat endpoint coefficient make its
flux continuous on the closed radial interval. FTC2 then applies to its
right derivative, including all interior transmission interfaces.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped Topology ContDiff

/-- This is the envelope already present in arbitrary admissible material
data; it does not use a particular affine construction of the weights. -/
theorem n07a_material_decay_uniform_bound {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {β : ℝ} (hβ : 0 < β) (q : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ r ∈ radialCore D, T.H r ^ β * T.M r ^ q ≤ B := by
  obtain ⟨B, hB, henvelope, _, _⟩ :=
    hT.2.2.2.2.2.2.2.2.2.2.2.2.1 q β hβ
  exact ⟨B, hB, henvelope⟩

/-- A single closed-interval statement covers both flat endpoints. -/
theorem n07a_continuousOn_flat_flux {a b : ℝ} {w ur : ℝ → ℝ}
    (hw : Continuous w) (hwa : w a = 0) (hwb : w b = 0)
    (hq : ContinuousOn (fun r => w r * ur r) (Ioo a b))
    {B : ℝ} (hB : ∀ r ∈ Ioo a b, |ur r| ≤ B) :
    ContinuousOn (fun r => w r * ur r) (Icc a b) := by
  intro r hr
  by_cases hi : r ∈ Ioo a b
  · exact (hq.continuousAt (isOpen_Ioo.mem_nhds hi)).continuousWithinAt
  · have he : r = a ∨ r = b := by
      rcases not_and_or.mp hi with hleft | hright
      · exact Or.inl (le_antisymm (le_of_not_gt hleft) hr.1)
      · exact Or.inr (le_antisymm hr.2 (le_of_not_gt hright))
    have hwzero : w r = 0 := by
      rcases he with rfl | rfl
      · exact hwa
      · exact hwb
    have hbounded : IsBoundedUnder (· ≤ ·) (𝓝[Icc a b] r) (fun x => ‖ur x‖) := by
      apply isBoundedUnder_of_eventually_le (a := max B (max |ur a| |ur b|))
      filter_upwards [self_mem_nhdsWithin] with x hx
      by_cases hxi : x ∈ Ioo a b
      · exact (hB x hxi).trans (le_max_left _ _)
      · have hxe : x = a ∨ x = b := by
          rcases not_and_or.mp hxi with hleft | hright
          · exact Or.inl (le_antisymm (le_of_not_gt hleft) hx.1)
          · exact Or.inr (le_antisymm hx.2 (le_of_not_gt hright))
        rcases hxe with rfl | rfl
        · exact (le_max_left _ _).trans (le_max_right _ _)
        · exact (le_max_right _ _).trans (le_max_right _ _)
    have hzero : Tendsto w (𝓝[Icc a b] r) (𝓝 0) := by
      have hc : ContinuousWithinAt w (Icc a b) r := hw.continuousAt.continuousWithinAt
      simpa only [hwzero] using hc.tendsto
    have hlimit : Tendsto (fun x => w x * ur x) (𝓝[Icc a b] r)
        (𝓝 (w r * ur r)) := by
      rw [hwzero, zero_mul]
      exact hzero.zero_mul_isBoundedUnder_le hbounded
    exact hlimit

theorem n07a_referenceNormalFlux_continuousOn_closed {D : ReferenceData}
    {v : PolarPoint → ℝ} (hw : EndpointFlat D D.w)
    (hv : ContDiffOn ℝ 1 v (annularOpen D)) (θ : ℝ)
    {B : ℝ} (hB : ∀ r ∈ radialCore D, |radialPartial v (r, θ)| ≤ B) :
    ContinuousOn (fun r => n07aReferenceNormalFlux D v (r, θ)) (Icc D.a D.b) := by
  have hopen : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hdf : ContinuousOn (fderiv ℝ v) (annularOpen D) :=
    hv.continuousOn_fderiv_of_isOpen hopen (by norm_num)
  have hvr : ContinuousOn (fun r => radialPartial v (r, θ)) (Ioo D.a D.b) :=
    (hdf.clm_apply continuousOn_const).comp
      (continuous_id.prodMk continuous_const).continuousOn (fun r hr => ⟨hr, mem_univ _⟩)
  exact n07a_continuousOn_flat_flux hw.1.continuous
    (hw.2 D.a (Or.inl le_rfl)) (hw.2 D.b (Or.inr le_rfl))
    (hw.1.continuous.continuousOn.mul hvr) hB

/-- The actual right flux derivative has zero total radial integral.
Its integrability is supplied by the genuine piecewise source estimates. -/
theorem n07a_referenceRightFluxDerivative_integral_zero {D : ReferenceData}
    {v : PolarPoint → ℝ} (hab : D.a ≤ D.b) (hw : EndpointFlat D D.w)
    (hv : ContDiffOn ℝ 1 v (annularOpen D))
    (hright : ∀ p ∈ annularOpen D, ∃ u : PolarPoint → ℝ,
      ContDiffAt ℝ ∞ u p ∧ ∀ᶠ q in 𝓝 p, p.1 ≤ q.1 → v q = u q)
    (θ : ℝ) {B : ℝ} (hB : ∀ r ∈ radialCore D, |radialPartial v (r, θ)| ≤ B)
    (hg : IntervalIntegrable (fun r => n07aReferenceRightFluxDerivative D v (r, θ))
      volume D.a D.b) :
    (∫ r in D.a..D.b, n07aReferenceRightFluxDerivative D v (r, θ)) = 0 := by
  have hcont := n07a_referenceNormalFlux_continuousOn_closed hw hv θ hB
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hcont
    (fun r hr => n07a_referenceNormalFlux_hasDerivWithinAt_right
      (hw.1.differentiable (by simp) r) hv ⟨hr, mem_univ _⟩
      (hright (r, θ) ⟨hr, mem_univ _⟩)) hg
  simpa only [n07aReferenceNormalFlux, hw.2 D.a (Or.inl le_rfl),
    hw.2 D.b (Or.inr le_rfl), zero_mul, sub_self] using hFTC

end ContinuousFlexibility.Analysis
