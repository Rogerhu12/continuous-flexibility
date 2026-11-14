module

public import ContinuousFlexibility.Radial.SeedGluedPair
public import ContinuousFlexibility.Radial.TwoTailReferenceAssembly

/-!
# Exhaustiveness of the negative pieces in the glued seed

Every negative derivative of the actual glued profile comes from one
retained old tail or the retained central model. The increasing
connectors cannot introduce additional negative components.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real Filter
open ContinuousFlexibility.Statements
open scoped Topology

private theorem negative_deriv_of_scaled_interval
    {old new : ℝ → ℝ} {R H l h r : ℝ}
    (hR : 0 < R) (hH : 0 < H)
    (heq : ∀ s ∈ Ioo l h, new (R * s) = H * R * old s)
    (hr : r ∈ Ioo (R * l) (R * h))
    (hneg : deriv new r < 0) :
    ∃ s ∈ Ioo l h, r = R * s ∧ deriv old s < 0 := by
  have hg : new =ᶠ[𝓝 r] seedRescale R (H * R) old :=
    scaled_profile_germ_of_interval_identity hR heq hr
  have hs : R⁻¹ * r ∈ Ioo l h := by
    constructor
    · have h : l < r / R := (lt_div_iff₀ hR).mpr
        (by simpa only [mul_comm] using hr.1)
      simpa only [div_eq_mul_inv, mul_comm] using h
    · have h : r / R < h := (div_lt_iff₀ hR).mpr
        (by simpa only [mul_comm] using hr.2)
      simpa only [div_eq_mul_inv, mul_comm] using h
  refine ⟨R⁻¹ * r, hs, ?_, ?_⟩
  · rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]
  · rw [hg.deriv_eq, deriv_seedRescale] at hneg
    have hc : 0 < H * R * R⁻¹ := mul_pos (mul_pos hH hR) (inv_pos.mpr hR)
    by_contra h
    have hn := mul_nonneg hc.le (le_of_not_gt h)
    linarith only [hneg, hn]

/-- A negative point is retained from an old tail or from the exact
central profile. This is proved from the concrete connector signs. -/
theorem SeedGluedPair.negative_deriv_cases
    {D : ReferenceData} {c d : ℝ} {uL uR : ℝ → ℝ}
    {K : SeedCentralCutoff} {q : ℝ}
    (G : SeedGluedPair D c d uL uR K q) (hq : 0 < q)
    {r : ℝ} (hr : r ∈ Ioo (G.radiusL * D.a) (G.radiusR * D.b))
    (hneg : deriv G.profile r < 0) :
    (∃ s ∈ Ioo D.a c, r = G.radiusL * s ∧ deriv D.w s < 0) ∨
    (r ∈ Ioo (exp K.left) (exp K.right) ∧
      deriv (centralRadialProfile 1) r < 0) ∨
    (∃ s ∈ Ioo d D.b, r = G.radiusR * s ∧ deriv D.w s < 0) := by
  by_cases hleft : r < G.radiusL * c
  · exact Or.inl (negative_deriv_of_scaled_interval G.radiusL_pos G.heightL_pos
      (fun s hs => (G.left_tail s hs).1) ⟨hr.1, hleft⟩ hneg)
  by_cases hright : G.radiusR * d < r
  · have hRR : 0 < G.radiusR := G.radiusL_pos.trans_le G.radius_order
    exact Or.inr (Or.inr (negative_deriv_of_scaled_interval hRR G.heightR_pos
      (fun s hs => (G.right_tail s hs).1) ⟨hright, hr.2⟩ hneg))
  have hentryL : G.radiusL * c ≤ r := le_of_not_gt hleft
  have hentryR : r ≤ G.radiusR * d := le_of_not_gt hright
  have hretL : exp K.left < r := by
    apply lt_of_not_ge
    intro h
    have hp := G.left_increasing r hentryL h
    linarith only [hneg, hp]
  have hretR : r < exp K.right := by
    apply lt_of_not_ge
    intro h
    have hp := G.right_increasing r h hentryR
    linarith only [hneg, hp]
  have hp : 0 < r := (exp_pos K.left).trans hretL
  have hy : log r ∈ Ioo K.left K.right :=
    ⟨(lt_log_iff_exp_lt hp).mpr hretL, (log_lt_iff_lt_exp hp).mpr hretR⟩
  have hcentral : K.profile =ᶠ[𝓝 r] centralRadialProfile 1 := by
    simpa only [exp_log hp] using K.profile_retained_germ hy
  have hm : r ∈ Ioo (exp (K.left - q - 4)) (exp (K.right + q + 4)) := by
    constructor
    · exact (exp_lt_exp.mpr (by linarith only [hq])).trans hretL
    · exact hretR.trans (exp_lt_exp.mpr (by linarith only [hq]))
  rw [(G.middle_germ r hm).1.deriv_eq, hcentral.deriv_eq] at hneg
  exact Or.inr (Or.inl ⟨⟨hretL, hretR⟩, hneg⟩)

end ContinuousFlexibility.Radial
