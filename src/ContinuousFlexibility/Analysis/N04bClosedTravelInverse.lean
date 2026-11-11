import ContinuousFlexibility.Analysis.N04bClosedTravelStrip
import Mathlib.Topology.MetricSpace.Basic

/-!
# Continuity of the actual inverse up to both travel endpoints

The physical radial coordinate stays in a compact interval. A bound on
angular displacement prevents an inverse image of a bounded target
neighborhood from escaping to angular infinity. Compactness and
injectivity then prove inverse continuity, including endpoint values.
For the actual circle lifts the displacement bound follows from period
equivariance; inverse continuity is not an additional hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

/-- Compact radial control and a genuine angular-displacement bound make
any actual right inverse continuous on its target. -/
theorem n04b_continuousOn_closedStrip_inverse_of_angular_bound
    {F G : PolarPoint → PolarPoint} {a b M : ℝ} {U : Set PolarPoint}
    (hF : ContinuousOn F (Icc a b ×ˢ univ))
    (hInj : InjOn F (Icc a b ×ˢ univ))
    (hG : MapsTo G U (Icc a b ×ˢ univ))
    (hRight : RightInvOn G F U)
    (hBound : ∀ p ∈ Icc a b ×ˢ (univ : Set ℝ), |(F p).2 - p.2| ≤ M) :
    ContinuousOn G U := by
  intro q hq
  apply Metric.continuousWithinAt_iff'.mpr
  intro ε hε
  let K : Set PolarPoint :=
    Icc a b ×ˢ Icc (q.2 - 1 - M) (q.2 + 1 + M)
  let B : Set PolarPoint := K ∩ (Metric.ball (G q) ε)ᶜ
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hB : IsCompact B := hK.inter_right Metric.isOpen_ball.isClosed_compl
  have hBS : B ⊆ Icc a b ×ˢ (univ : Set ℝ) := by
    intro p hp
    exact ⟨hp.1.1, mem_univ _⟩
  have hImage : IsCompact (F '' B) :=
    hB.image_of_continuousOn (hF.mono hBS)
  have hqNot : q ∉ F '' B := by
    rintro ⟨p, hp, hpq⟩
    have he : p = G q :=
      hInj (hBS hp) (hG hq) (hpq.trans (hRight hq).symm)
    rw [he] at hp
    exact hp.2 (Metric.mem_ball_self hε)
  have hAvoid : ∀ᶠ y in 𝓝 q, y ∉ F '' B :=
    hImage.isClosed.isOpen_compl.mem_nhds hqNot
  have hAngle : ∀ᶠ y : PolarPoint in 𝓝 q,
      y.2 ∈ Ioo (q.2 - 1) (q.2 + 1) :=
    continuous_snd.continuousAt.eventually
      (Ioo_mem_nhds (by linarith) (by linarith))
  have hMem : ∀ᶠ y in 𝓝[U] q, y ∈ U := self_mem_nhdsWithin
  filter_upwards [hMem, hAvoid.filter_mono nhdsWithin_le_nhds,
    hAngle.filter_mono nhdsWithin_le_nhds] with y hy havoid hangle
  have hb := hBound (G y) (hG hy)
  rw [hRight hy] at hb
  obtain ⟨hbL, hbR⟩ := abs_le.mp hb
  have hGyK : G y ∈ K := by
    refine ⟨(hG hy).1, ?_⟩
    constructor <;> linarith [hangle.1, hangle.2]
  by_contra hn
  have hGyB : G y ∈ B := ⟨hGyK, by simpa only [Metric.mem_ball] using hn⟩
  exact havoid ⟨G y, hGyB, hRight hy⟩

/-- The angular-displacement bound is derived from the actual lifted
period on the full closed physical strip. -/
theorem n04b_continuousOn_closedStrip_inverse_of_periodic
    {F G : PolarPoint → PolarPoint} {a b P : ℝ} {U : Set PolarPoint}
    (hP : P ≠ 0)
    (hF : ContinuousOn F (Icc a b ×ˢ univ))
    (hInj : InjOn F (Icc a b ×ˢ univ))
    (hG : MapsTo G U (Icc a b ×ˢ univ))
    (hRight : RightInvOn G F U)
    (hPeriod : ∀ r ∈ Icc a b, ∀ θ,
      (F (r, θ + P)).2 = (F (r, θ)).2 + P) :
    ContinuousOn G U := by
  obtain ⟨M, _, hM⟩ := exists_norm_bound_periodic_compact
    (S := Icc a b) (F := fun p : PolarPoint => (F p).2 - p.2)
    isCompact_Icc hP (hF.snd.sub continuous_snd.continuousOn)
    (fun r hr θ => by
      change (F (r, θ + P)).2 - (θ + P) = (F (r, θ)).2 - θ
      rw [hPeriod r hr θ]
      ring)
  apply n04b_continuousOn_closedStrip_inverse_of_angular_bound
    (M := M) hF hInj hG hRight
  intro p hp
  simpa only [Real.norm_eq_abs] using hM p.1 hp.1 p.2

/-- In particular, the actual inverse chosen on the closed strip is
continuous all the way to both boundary circles. -/
theorem n04b_closedTravelInverse_continuous
    {F : PolarPoint → PolarPoint} {a b T P : ℝ}
    (hP : P ≠ 0)
    (hF : ContinuousOn F (Icc a b ×ˢ univ))
    (hBij : BijOn F (Icc a b ×ˢ univ) (Icc (0 : ℝ) T ×ˢ univ))
    (hPeriod : ∀ r ∈ Icc a b, ∀ θ,
      (F (r, θ + P)).2 = (F (r, θ)).2 + P) :
    ContinuousOn (Function.invFunOn F (Icc a b ×ˢ univ))
      (Icc (0 : ℝ) T ×ˢ univ) :=
  n04b_continuousOn_closedStrip_inverse_of_periodic hP hF hBij.injOn
    hBij.surjOn.mapsTo_invFunOn hBij.surjOn.rightInvOn_invFunOn hPeriod

end ContinuousFlexibility.Analysis
