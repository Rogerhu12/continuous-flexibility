import ContinuousFlexibility.Analysis.CanonicalInteriorInverse
import ContinuousFlexibility.Analysis.PlanarInverseRegularity

/-!
# Actual canonical density extensions at an endpoint

Physical finite-order vanishing is transported by a genuine smooth local
inverse. Its agreement with the actual open-strip inverse identifies the
result with the canonical density remainder on a full interior
neighborhood. Values of the chosen total inverse at the boundary are
irrelevant. A common open smoothness domain for the constructed chart
and its nonzero Jacobian gives a genuinely smooth extension on a ball.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- An actual physical remainder yields a smooth canonical extension with
the same finite order of vanishing. The physical zero jets are supplied,
for the concrete Taylor construction, by
`boundaryTaylorPrincipalRemainder_smooth_zeroJets`. -/
theorem exists_canonicalDensity_extension_of_physical_zeroJets
    {a b α β : ℝ} (hab : a < b) {F G : PolarPoint → PolarPoint}
    (hmap : MapsTo F (Ioo a b ×ˢ (univ : Set ℝ))
      (Ioo α β ×ˢ (univ : Set ℝ)))
    (hboundary : ∀ x : PolarPoint, x.1 = a ∨ x.1 = b →
      (F x).1 ∉ Ioo α β)
    (hinj : InjOn F (Ioo a b ×ˢ (univ : Set ℝ)))
    (hG : MapsTo G (Ioo α β ×ˢ (univ : Set ℝ))
      (Ioo a b ×ˢ (univ : Set ℝ)))
    (hright : ∀ q ∈ Ioo α β ×ˢ (univ : Set ℝ), F (G q) = q)
    {U : Set PolarPoint} (hU : IsOpen U) {ρ : PolarPoint → ℝ} {N : ℝ → ℝ}
    (hR : ContDiffOn ℝ ∞ (fun p => ρ p - N ((F p).1)) U)
    (c : ℝ) (hc : ∀ θ : ℝ, (c, θ) ∈ U) (hcc : c ∈ Icc a b) {n : ℕ}
    (hzero : ∀ j ≤ n, ∀ θ : ℝ,
      radialBoundaryJet (fun p => ρ p - N ((F p).1)) c j θ = 0)
    (θ : ℝ) (hF : ContDiffOn ℝ ∞ F U)
    (hJ : ∀ p ∈ U, planeJacobian F p ≠ 0) :
    ∃ (E : PolarPoint → ℝ) (δ : ℝ), 0 < δ ∧
      ContDiffOn ℝ ∞ E (Metric.ball (F (c, θ)) δ) ∧
      EqOn E (fun q => ρ (G q) - N q.1)
        (Metric.ball (F (c, θ)) δ ∩ (Ioo α β ×ˢ (univ : Set ℝ))) ∧
      ∀ k ≤ n, iteratedDeriv k (fun r => E (r, (F (c, θ)).2))
        (F (c, θ)).1 = 0 := by
  obtain ⟨e, heF, hpe, hinv⟩ :=
    exists_smooth_localInverse_of_planeJacobian_ne_zero
      (hF.contDiffAt (hU.mem_nhds (hc θ))) (hJ (c, θ) (hc θ))
  obtain ⟨δ, hδ, htarget, _, heq⟩ :=
    exists_rightInverse_eq_localInverse_on_openStrip
      hab hmap hboundary hinj hG hright e heF hpe hcc
  let R : PolarPoint → ℝ := fun p => ρ p - N ((F p).1)
  let E : PolarPoint → ℝ := fun q => R (e.symm q)
  have hbase : e.symm (F (c, θ)) = (c, θ) := by
    rw [← heF]
    exact e.left_inv hpe
  let T : Set PolarPoint := e.target ∩ e.symm ⁻¹' U
  have hT : IsOpen T := e.isOpen_inter_preimage_symm hU
  have hTp : F (c, θ) ∈ T := by
    refine ⟨?_, ?_⟩
    · rw [← heF]
      exact e.map_source hpe
    · have hu : e.symm (F (c, θ)) ∈ U := by
        rw [hbase]
        exact hc θ
      exact hu
  have hlocalInj : InjOn F (U ∩ e.source) := by
    intro x hx y hy hxy
    apply e.injOn hx.2 hy.2
    simpa only [heF] using hxy
  have hlocalMap : MapsTo e.symm T (U ∩ e.source) :=
    fun q hq => ⟨hq.2, e.map_target hq.1⟩
  have hlocalRight : RightInvOn e.symm F T := by
    intro q hq
    rw [← heF]
    exact e.right_inv hq.1
  have hInvT : ContDiffOn ℝ ∞ e.symm T :=
    contDiffOn_planar_rightInverse_of_injOn (hU.inter e.open_source) hT
      (hF.mono inter_subset_left) (fun q hq => hJ q hq.1)
      hlocalInj hlocalMap hlocalRight
  have hET : ContDiffOn ℝ ∞ E T :=
    hR.comp hInvT (fun _ hq => hq.2)
  obtain ⟨η, hη, hηT⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds hTp)
  have hballδ : Metric.ball (F (c, θ)) (min δ η) ⊆ Metric.ball (F (c, θ)) δ :=
    Metric.ball_subset_ball (min_le_left δ η)
  have hballT : Metric.ball (F (c, θ)) (min δ η) ⊆ T :=
    (Metric.ball_subset_ball (min_le_right δ η)).trans hηT
  refine ⟨E, min δ η, lt_min hδ hη, hET.mono hballT, ?_, ?_⟩
  · intro q hq
    have hq' : q ∈ Metric.ball (F (c, θ)) δ ∩ (Ioo α β ×ˢ (univ : Set ℝ)) :=
      ⟨hballδ hq.1, hq.2⟩
    have hrightE : F (e.symm q) = q := by
      rw [← heF]
      exact e.right_inv (htarget hq'.1)
    dsimp only [E, R]
    rw [hrightE, heq hq']
  · intro k hk
    have hinv' : ContDiffAt ℝ ∞ e.symm (e (c, θ)) := by
      rw [heF]
      exact hinv
    have hz := iteratedDeriv_localInverse_radialCurve_eq_zero
      hU hR c hc hzero e θ hpe hinv' hk
    simpa only [E, R, heF] using hz

end ContinuousFlexibility.Analysis

