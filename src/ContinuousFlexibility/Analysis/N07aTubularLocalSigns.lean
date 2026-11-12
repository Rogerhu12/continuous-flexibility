import ContinuousFlexibility.Scalar.Coordinates
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.DenselyOrdered

/-!
# A uniform local side test from a positive transverse derivative

A scalar defining function with positive radial derivative at the center
is strictly increasing on every radial line of one closed rectangle.
Only finite C¹ regularity near the center is used for this side test.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

theorem n07a_closedRectangle_subset_nhds {R θ : ℝ} {U : Set PolarPoint}
    (hU : U ∈ 𝓝 (R, θ)) :
    ∃ l r a b : ℝ, l < R ∧ R < r ∧ a < θ ∧ θ < b ∧
      Icc l r ×ˢ Icc a b ⊆ U := by
  obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.mp hU
  obtain ⟨l, r, _, hlr, hsubr⟩ := exists_Icc_mem_subset_of_mem_nhds hV
  obtain ⟨a, b, _, hab, hsubθ⟩ := exists_Icc_mem_subset_of_mem_nhds hW
  have hR := Icc_mem_nhds_iff.mp hlr
  have hθ := Icc_mem_nhds_iff.mp hab
  exact ⟨l, r, a, b, hR.1, hR.2, hθ.1, hθ.2,
    (Set.prod_mono hsubr hsubθ).trans hVW⟩

theorem n07a_exists_closedRectangle_radialSigns
    {ψ : PolarPoint → ℝ} {R θ₀ : ℝ}
    (hψ : ContDiffAt ℝ 1 ψ (R, θ₀))
    (hpos : 0 < radialPartial ψ (R, θ₀))
    (hline : ∀ θ, ψ (R, θ) = R)
    {U : Set PolarPoint} (hU : U ∈ 𝓝 (R, θ₀)) :
    ∃ l r a b : ℝ, l < R ∧ R < r ∧ a < θ₀ ∧ θ₀ < b ∧
      Icc l r ×ˢ Icc a b ⊆ U ∧
      ∀ s ∈ Icc l r, ∀ θ ∈ Icc a b,
        (ψ (s, θ) < R ↔ s < R) ∧ (R < ψ (s, θ) ↔ R < s) := by
  have hrad : ContinuousAt (radialPartial ψ) (R, θ₀) :=
    (hψ.fderiv_right (by simp : (0 : ℕ∞ω) + 1 ≤ 1)).continuousAt.clm_apply
      continuousAt_const
  have hnear : {p : PolarPoint | p ∈ U ∧ DifferentiableAt ℝ ψ p ∧
      0 < radialPartial ψ p} ∈ 𝓝 (R, θ₀) := by
    filter_upwards [hU, hψ.eventually (by simp : (1 : ℕ∞ω) ≠ ∞),
      hrad.eventually (Ioi_mem_nhds hpos)] with p hpU hps hpD
    exact ⟨hpU, hps.differentiableAt one_ne_zero, hpD⟩
  obtain ⟨l, r, a, b, hl, hr, ha, hb, hrect⟩ :=
    n07a_closedRectangle_subset_nhds hnear
  refine ⟨l, r, a, b, hl, hr, ha, hb, fun p hp => (hrect hp).1, ?_⟩
  intro s hs θ hθ
  have hd (t : ℝ) (ht : t ∈ Icc l r) :
      HasDerivAt (fun q => ψ (q, θ)) (radialPartial ψ (t, θ)) t :=
    (hrect ⟨ht, hθ⟩).2.1.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id' t).prodMk (hasDerivAt_const t θ))
  have hmono : StrictMonoOn (fun t => ψ (t, θ)) (Icc l r) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc l r)
    · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [(hd t (interior_subset ht)).deriv]
      exact (hrect ⟨interior_subset ht, hθ⟩).2.2
  have hR : R ∈ Icc l r := ⟨hl.le, hr.le⟩
  constructor
  · simpa only [hline θ] using hmono.lt_iff_lt hs hR
  · simpa only [hline θ] using hmono.lt_iff_lt hR hs

end ContinuousFlexibility.Analysis
