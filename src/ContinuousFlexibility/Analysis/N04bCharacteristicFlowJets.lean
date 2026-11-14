module

public import ContinuousFlexibility.Analysis.AngularRegularity

/-!
# Patching actual angular jets across radial endpoints

Only derivatives of one-dimensional angular slices occur here. A full
neighborhood equality of scalar fields transfers all these jets, even
when neither field has a radial derivative at the base point.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A genuine planar germ equality transfers every actual angular jet. -/
theorem n04b_angularJet_eventuallyEq
    {F G : PolarPoint → ℝ} {p : PolarPoint} (h : F =ᶠ[𝓝 p] G) (n : ℕ) :
    (fun q : PolarPoint => iteratedDeriv n (fun θ => F (q.1, θ)) q.2) =ᶠ[𝓝 p]
      (fun q : PolarPoint => iteratedDeriv n (fun θ => G (q.1, θ)) q.2) := by
  filter_upwards [h.eventuallyEq_nhds] with q hq
  have hs : (fun θ => F (q.1, θ)) =ᶠ[𝓝 q.2] (fun θ => G (q.1, θ)) :=
    (continuous_const.prodMk continuous_id).continuousAt.tendsto.eventually hq
  exact (hs.iteratedDeriv n).eq_of_nhds

/-- Smooth angular slices and jointly continuous actual jets give the
recursive angular-regularity certificate. -/
theorem n04b_angularRegular_of_jets
    {F : ℝ → ℝ → ℝ}
    (hs : ∀ r, ContDiff ℝ ∞ (F r))
    (hj : ∀ n : ℕ,
      Continuous (fun p : PolarPoint => iteratedDeriv n (F p.1) p.2))
    (n : ℕ) : AngularRegular n F := by
  induction n generalizing F with
  | zero => simpa only [AngularRegular, iteratedDeriv_zero] using hj 0
  | succ n ih =>
    refine ⟨?_, fun r => (hs r).differentiable (by simp), ?_⟩
    · simpa only [iteratedDeriv_zero] using hj 0
    · apply ih (fun r => (contDiff_infty_iff_deriv.mp (hs r)).2)
      intro k
      simpa only [iteratedDeriv_succ'] using hj (k + 1)

/-- The radial clamp preserves all angular jets and their continuity.
No radial differentiability at the closed endpoints is required. -/
theorem n04b_angularRegular_closedStrip_of_jets
    {F : PolarPoint → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hs : ∀ r ∈ Icc a b, ContDiff ℝ ∞ (fun θ => F (r, θ)))
    (hj : ∀ n : ℕ,
      ContinuousOn (fun p : PolarPoint => iteratedDeriv n (fun θ => F (p.1, θ)) p.2)
        (Icc a b ×ˢ univ))
    (n : ℕ) :
    AngularRegular n (fun r θ => closedStripExtend hab F (r, θ)) := by
  apply n04b_angularRegular_of_jets
    (fun r => hs (projIcc a b hab r) (projIcc a b hab r).property)
  intro k
  exact continuous_closedStripExtend hab (hj k)

/-- Inside the unclamped radial interval, the continuous clamped jet is
the actual angular jet of the original field. -/
theorem n04b_angularJet_continuousAt_of_clamp
    {F : PolarPoint → ℝ} {a b : ℝ} (hab : a ≤ b) {n : ℕ}
    (hF : AngularRegular n (fun r θ => closedStripExtend hab F (r, θ)))
    {p : PolarPoint} (hp : p.1 ∈ Ioo a b) :
    ContinuousAt (fun q : PolarPoint => iteratedDeriv n (fun θ => F (q.1, θ)) q.2) p := by
  apply hF.iteratedDeriv_continuous.continuousAt.congr_of_eventuallyEq
  have hnear : ∀ᶠ q : PolarPoint in 𝓝 p, q.1 ∈ Ioo a b :=
    continuous_fst.continuousAt.preimage_mem_nhds (Ioo_mem_nhds hp.1 hp.2)
  filter_upwards [hnear] with q hq
  apply congrArg (fun f : ℝ → ℝ => iteratedDeriv n f q.2)
  funext θ
  exact (closedStripExtend_eq hab F (p := (q.1, θ)) ⟨hq.1.le, hq.2.le⟩).symm

end ContinuousFlexibility.Analysis
