import ContinuousFlexibility.Analysis.N01cFlowParameterContinuity
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Actual periodic flows with arbitrary topological parameters

Compact-fiber continuity of the speed gives uniformly small speed
differences on a closed time strip and one angular period. The genuine
two-speed estimate then gives uniform convergence of actual trajectories.
Together with each trajectory's time continuity this proves joint
parameter/time continuity. The final wrapper includes the initial angle.

Only the speed slices are assumed smooth. No parameter derivative, norm,
local compactness or pre-existing joint continuity of the flows is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

theorem circleTrajectory_twoSpeeds_uniform_difference_bound
    {G H : PolarPoint → ℝ} {u v : ℝ → ℝ} {a b M N t : ℝ}
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hdu : ∀ r ∈ Ioo a b, HasDerivAt u (G (r, u r)) r)
    (hdv : ∀ r ∈ Ioo a b, HasDerivAt v (H (r, v r)) r)
    (ha : u a = v a) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hangle : ∀ r ∈ Icc a b, ∀ θ, |angularPartial H (r, θ)| ≤ M)
    (hspeed : ∀ r ∈ Icc a b, ∀ θ, |G (r, θ) - H (r, θ)| ≤ N)
    (ht : t ∈ Icc a b) :
    |u t - v t| ≤ ((b - a) * Real.exp ((b - a) * M) ^ 2) * N := by
  have h := circleTrajectory_twoSpeeds_difference_bound ht.1 hG hH
    (hu.mono (Icc_subset_Icc le_rfl ht.2))
    (hv.mono (Icc_subset_Icc le_rfl ht.2))
    (fun r hr => hdu r ⟨hr.1, hr.2.trans_le ht.2⟩)
    (fun r hr => hdv r ⟨hr.1, hr.2.trans_le ht.2⟩) ha hM hN
    (fun r hr => hangle r ⟨hr.1, hr.2.trans ht.2⟩)
    (fun r hr => hspeed r ⟨hr.1, hr.2.trans ht.2⟩)
  have he : Real.exp ((t - a) * M) ≤ Real.exp ((b - a) * M) :=
    Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (sub_le_sub_right ht.2 a) hM)
  have he₂ : Real.exp ((t - a) * M) ^ 2 ≤ Real.exp ((b - a) * M) ^ 2 := by
    simpa only [pow_two] using mul_le_mul he he (Real.exp_pos _).le (Real.exp_pos _).le
  have hc : (t - a) * Real.exp ((t - a) * M) ^ 2 ≤
      (b - a) * Real.exp ((b - a) * M) ^ 2 :=
    mul_le_mul (sub_le_sub_right ht.2 a) he₂ (sq_nonneg _)
      (sub_nonneg.mpr (ht.1.trans ht.2))
  exact h.trans (mul_le_mul_of_nonneg_right hc hN)

variable {X : Type*} [TopologicalSpace X]

theorem circleTopologicalSpeed_eventually_uniform_difference_lt
    {G : X × PolarPoint → ℝ} {U : Set X} {a b P ε : ℝ} {q₀ : X}
    (hjoint : ContinuousOn G (U ×ˢ (Icc a b ×ˢ (univ : Set ℝ))))
    (hP : 0 < P)
    (hperiod : ∀ q ∈ U, ∀ t, Function.Periodic (fun θ => G (q, (t, θ))) P)
    (hq₀ : q₀ ∈ U) (hε : 0 < ε) :
    ∀ᶠ q in 𝓝[U] q₀, ∀ t ∈ Icc a b, ∀ θ,
      |G (q, (t, θ)) - G (q₀, (t, θ))| < ε := by
  have hc : ContinuousOn G (U ×ˢ (Icc a b ×ˢ Icc (0 : ℝ) P)) :=
    hjoint.mono (fun p hp => ⟨hp.1, hp.2.1, mem_univ _⟩)
  obtain ⟨V, hV, hclose⟩ :
      ∃ V ∈ 𝓝[U] q₀, ∀ q ∈ V, ∀ p ∈ Icc a b ×ˢ Icc (0 : ℝ) P,
        dist (G (q, p)) (G (q₀, p)) < ε :=
    (isCompact_Icc.prod isCompact_Icc).mem_uniformity_of_prod
      hc hq₀ (dist_mem_uniformity hε)
  filter_upwards [hV, self_mem_nhdsWithin] with q hq hqU
  intro t ht θ
  have hp : Function.Periodic (fun η => G (q, (t, η)) - G (q₀, (t, η))) P :=
    (hperiod q hqU t).sub (hperiod q₀ hq₀ t)
  obtain ⟨η, hη, he⟩ := hp.exists_mem_Ico₀ hP θ
  rw [he]
  simpa only [Real.dist_eq] using hclose q hq (t, η) ⟨ht, hη.1, hη.2.le⟩

theorem circleTopologicalTrajectory_eventually_uniform_difference_lt
    {G : X × PolarPoint → ℝ} {Θ : X × ℝ → ℝ} {U : Set X}
    {a b θ₀ P ε : ℝ} {q₀ : X}
    (hG : ∀ q ∈ U, ContDiff ℝ ∞ (fun p => G (q, p)))
    (hjoint : ContinuousOn G (U ×ˢ (Icc a b ×ˢ (univ : Set ℝ))))
    (hP : 0 < P)
    (hperiod : ∀ q ∈ U, ∀ t, Function.Periodic (fun θ => G (q, (t, θ))) P)
    (htime : ∀ q ∈ U, ContinuousOn (fun t => Θ (q, t)) (Icc a b))
    (hinit : ∀ q ∈ U, Θ (q, a) = θ₀)
    (hflow : ∀ q ∈ U, ∀ t ∈ Ioo a b,
      HasDerivAt (fun r => Θ (q, r)) (G (q, (t, Θ (q, t)))) t)
    (hq₀ : q₀ ∈ U) (hε : 0 < ε) :
    ∀ᶠ q in 𝓝[U] q₀, ∀ t ∈ Icc a b, |Θ (q, t) - Θ (q₀, t)| < ε := by
  obtain ⟨M, hM, hangle⟩ :=
    exists_circleSpeed_angular_bound (hG q₀ hq₀) hP (hperiod q₀ hq₀) a b
  obtain ⟨δ, hδ, hsmall⟩ :=
    exists_pos_mul_lt hε ((b - a) * Real.exp ((b - a) * M) ^ 2)
  have hspeed := circleTopologicalSpeed_eventually_uniform_difference_lt
    hjoint hP hperiod hq₀ hδ
  filter_upwards [hspeed, self_mem_nhdsWithin] with q hspeedq hq
  intro t ht
  exact (circleTrajectory_twoSpeeds_uniform_difference_bound
    (hG q hq) (hG q₀ hq₀) (htime q hq) (htime q₀ hq₀)
    (hflow q hq) (hflow q₀ hq₀) ((hinit q hq).trans (hinit q₀ hq₀).symm)
    hM hδ.le hangle (fun r hr θ => (hspeedq r hr θ).le) ht).trans_lt hsmall

theorem circleTopologicalTrajectory_continuousOn
    {G : X × PolarPoint → ℝ} {Θ : X × ℝ → ℝ} {U : Set X} {a b θ₀ P : ℝ}
    (hG : ∀ q ∈ U, ContDiff ℝ ∞ (fun p => G (q, p)))
    (hjoint : ContinuousOn G (U ×ˢ (Icc a b ×ˢ (univ : Set ℝ))))
    (hP : 0 < P)
    (hperiod : ∀ q ∈ U, ∀ t, Function.Periodic (fun θ => G (q, (t, θ))) P)
    (htime : ∀ q ∈ U, ContinuousOn (fun t => Θ (q, t)) (Icc a b))
    (hinit : ∀ q ∈ U, Θ (q, a) = θ₀)
    (hflow : ∀ q ∈ U, ∀ t ∈ Ioo a b,
      HasDerivAt (fun r => Θ (q, r)) (G (q, (t, Θ (q, t)))) t) :
    ContinuousOn Θ (U ×ˢ Icc a b) := by
  intro p hp
  apply Metric.continuousWithinAt_iff'.mpr
  intro ε hε
  have hparam := circleTopologicalTrajectory_eventually_uniform_difference_lt
    hG hjoint hP hperiod htime hinit hflow hp.1 (half_pos hε)
  have ht : {t : ℝ | dist (Θ (p.1, t)) (Θ p) < ε / 2} ∈ 𝓝[Icc a b] p.2 :=
    Metric.continuousWithinAt_iff'.mp (htime p.1 hp.1 p.2 hp.2) (ε / 2) (half_pos hε)
  filter_upwards [nhdsWithin_prod hparam ht, self_mem_nhdsWithin] with q hclose hq
  calc
    dist (Θ q) (Θ p) ≤ dist (Θ q) (Θ (p.1, q.2)) +
        dist (Θ (p.1, q.2)) (Θ p) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add
      (by simpa only [Real.dist_eq] using hclose.1 q.2 hq.2) hclose.2
    _ = ε := add_halves ε

/-- Joint continuity also in the actual initial angle, obtained by
translation to a zero-initial-value trajectory. -/
theorem circleTopologicalFlow_continuousOn
    {G Θ : X × PolarPoint → ℝ} {U : Set X} {a b P : ℝ}
    (hG : ∀ q ∈ U, ContDiff ℝ ∞ (fun p => G (q, p)))
    (hjoint : ContinuousOn G (U ×ˢ (Icc a b ×ˢ (univ : Set ℝ))))
    (hP : 0 < P)
    (hperiod : ∀ q ∈ U, ∀ t, Function.Periodic (fun θ => G (q, (t, θ))) P)
    (htime : ∀ q ∈ U, ∀ θ, ContinuousOn (fun t => Θ (q, (t, θ))) (Icc a b))
    (hinit : ∀ q ∈ U, ∀ θ, Θ (q, (a, θ)) = θ)
    (hflow : ∀ q ∈ U, ∀ t ∈ Ioo a b, ∀ θ,
      HasDerivAt (fun r => Θ (q, (r, θ))) (G (q, (t, Θ (q, (t, θ))))) t) :
    ContinuousOn Θ (U ×ˢ (Icc a b ×ˢ (univ : Set ℝ))) := by
  let F : (X × ℝ) × PolarPoint → ℝ := fun p =>
    G (p.1.1, (p.2.1, p.2.2 + p.1.2))
  let Ψ : (X × ℝ) × ℝ → ℝ := fun p =>
    Θ (p.1.1, (p.2, p.1.2)) - p.1.2
  have hF (q : X × ℝ) (hq : q ∈ U ×ˢ (univ : Set ℝ)) :
      ContDiff ℝ ∞ (fun p => F (q, p)) :=
    (hG q.1 hq.1).comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const))
  have hFjoint : ContinuousOn F
      ((U ×ˢ (univ : Set ℝ)) ×ˢ (Icc a b ×ˢ (univ : Set ℝ))) :=
    hjoint.comp
      (continuous_fst.fst.prodMk (continuous_snd.fst.prodMk
        (continuous_snd.snd.add continuous_fst.snd))).continuousOn
      (fun p hp => ⟨hp.1.1, hp.2.1, mem_univ _⟩)
  have hFperiod (q : X × ℝ) (hq : q ∈ U ×ˢ (univ : Set ℝ)) (t : ℝ) :
      Function.Periodic (fun θ => F (q, (t, θ))) P := by
    intro θ
    change G (q.1, (t, θ + P + q.2)) = G (q.1, (t, θ + q.2))
    rw [add_right_comm θ P q.2]
    exact hperiod q.1 hq.1 t (θ + q.2)
  have hΨtime (q : X × ℝ) (hq : q ∈ U ×ˢ (univ : Set ℝ)) :
      ContinuousOn (fun t => Ψ (q, t)) (Icc a b) :=
    (htime q.1 hq.1 q.2).sub continuousOn_const
  have hΨinit (q : X × ℝ) (hq : q ∈ U ×ˢ (univ : Set ℝ)) : Ψ (q, a) = 0 := by
    dsimp only [Ψ]
    rw [hinit q.1 hq.1 q.2, sub_self]
  have hΨflow (q : X × ℝ) (hq : q ∈ U ×ˢ (univ : Set ℝ))
      (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun r => Ψ (q, r)) (F (q, (t, Ψ (q, t)))) t := by
    simpa only [F, Ψ, sub_add_cancel] using (hflow q.1 hq.1 t ht q.2).sub_const q.2
  have hc := circleTopologicalTrajectory_continuousOn
    hF hFjoint hP hFperiod hΨtime hΨinit hΨflow
  have hpre : ContinuousOn
      (fun p : X × PolarPoint => Ψ ((p.1, p.2.2), p.2.1))
      (U ×ˢ (Icc a b ×ˢ (univ : Set ℝ))) :=
    hc.comp
      ((continuous_fst.prodMk continuous_snd.snd).prodMk continuous_snd.fst).continuousOn
      (fun p hp => ⟨⟨hp.1, mem_univ _⟩, hp.2.1⟩)
  have hs : ContinuousOn
      (fun p : X × PolarPoint => Ψ ((p.1, p.2.2), p.2.1) + p.2.2)
      (U ×ˢ (Icc a b ×ˢ (univ : Set ℝ))) :=
    hpre.add continuous_snd.snd.continuousOn
  simpa only [Ψ, sub_add_cancel] using hs

end ContinuousFlexibility.Analysis
