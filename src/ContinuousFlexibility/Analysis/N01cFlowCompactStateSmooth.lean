import ContinuousFlexibility.Analysis.N01cFlowStateSmooth

/-!
# State smoothness at every original closed-interval time

A flat compact time change acts on the supplied classical trajectories.
Its speed jets are the original state-and-angle jets multiplied by the
actual time derivative. The full real-time Volterra construction then
applies, and surjectivity of the same compact time change returns every
original time, including both endpoints.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem ContinuousTimeSpeedTower.continuousOn
    {U : Set E} {G : E × PolarPoint → ℝ}
    (J : ContinuousTimeSpeedTower U G) :
    ContinuousOn G (U ×ˢ (univ : Set PolarPoint)) := by
  have hc : ContinuousOn (fun p => J.D 0 p Fin.elim0)
      (U ×ˢ (univ : Set PolarPoint)) :=
    (J.continuous 0).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun p hp => ⟨hp, mem_univ _⟩)
  apply hc.congr
  intro p hp
  exact ((J.jet p.2.1).zero (p.1, p.2.2) ⟨hp.1, mem_univ _⟩).symm

def timeChangedTopologicalSpeed (G : E × PolarPoint → ℝ) (τ : ℝ → ℝ)
    (p : E × PolarPoint) : ℝ :=
  deriv τ p.2.1 * G (p.1, (τ p.2.1, p.2.2))

def ContinuousTimeSpeedTower.timeChange
    {U : Set E} {G : E × PolarPoint → ℝ}
    (J : ContinuousTimeSpeedTower U G) {τ : ℝ → ℝ}
    (hτ : ContDiff ℝ ∞ τ) :
    ContinuousTimeSpeedTower U (timeChangedTopologicalSpeed G τ) where
  jet t := (smoothDirections_postcompCLM (J.jet (τ t))
    (deriv τ t • ContinuousLinearMap.id ℝ ℝ)).congr (fun _ _ => rfl)
  continuous := by
    intro n
    change ContinuousOn (fun p : (E × PolarPoint) × (Fin n → E × ℝ) =>
      deriv τ p.1.2.1 * J.D n (p.1.1, (τ p.1.2.1, p.1.2.2)) p.2) _
    have hderiv : Continuous (deriv τ) := (contDiff_infty_iff_deriv.mp hτ).2.continuous
    exact (hderiv.comp continuous_fst.snd.fst).continuousOn.mul
      ((J.continuous n).comp
        (((continuous_fst.fst.prodMk
          ((hτ.continuous.comp continuous_fst.snd.fst).prodMk continuous_fst.snd.snd)).prodMk continuous_snd).continuousOn)
        (fun p hp => ⟨⟨hp.1.1, mem_univ _⟩, hp.2⟩))

theorem ContinuousTimeSpeedTower.timeChange_D_apply
    {U : Set E} {G : E × PolarPoint → ℝ}
    (J : ContinuousTimeSpeedTower U G) {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ)
    (n : ℕ) (p : E × PolarPoint) (v : Fin n → E × ℝ) :
    (J.timeChange hτ).D n p v =
      deriv τ p.2.1 * J.D n (p.1, (τ p.2.1, p.2.2)) v := rfl

/-- Genuine state smoothness of a supplied compact classical family
after any smooth time change staying inside its original interval. -/
def topologicalCircleTrajectoryTimeChangeSmoothDirections
    {U : Set E} {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ}
    {a b θ₀ : ℝ} (hU : IsOpen U) (J : ContinuousTimeSpeedTower U G)
    (hΘ : ContinuousOn Θ (U ×ˢ Icc a b))
    (hinit : ∀ x ∈ U, Θ (x, a) = θ₀)
    (hflow : ∀ x ∈ U, ∀ t ∈ Ioo a b,
      HasDerivAt (fun r => Θ (x, r)) (G (x, (t, Θ (x, t)))) t)
    (hspeed : ∀ m : ℕ, ∀ x ∈ U, ∀ L : (Fin m → ℝ) →L[ℝ] E,
      ContDiffOn ℝ ∞ (fun p : (Fin m → ℝ) × PolarPoint => G (x + L p.1, p.2))
        (((fun q => x + L q) ⁻¹' U) ×ˢ (univ : Set PolarPoint)))
    {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (hτ0 : τ 0 = a)
    (hτrange : ∀ r : ℝ, τ r ∈ Icc a b) (s : ℝ) :
    SmoothDirections U (fun x => Θ (x, τ s)) := by
  let H := timeChangedTopologicalSpeed G τ
  let Φ : E × ℝ → ℝ := fun p => Θ (p.1, τ p.2)
  have hΦ : ContinuousOn Φ (U ×ˢ (univ : Set ℝ)) :=
    hΘ.comp (continuous_fst.prodMk (hτ.continuous.comp continuous_snd)).continuousOn
      (fun p hp => ⟨hp.1, hτrange p.2⟩)
  have hΦ0 (x : E) (hx : x ∈ U) : Φ (x, 0) = θ₀ := by
    simpa only [Φ, hτ0] using hinit x hx
  have hΦflow (x : E) (hx : x ∈ U) (r : ℝ) :
      HasDerivAt (fun t => Φ (x, t)) (H (x, (r, Φ (x, r)))) r := by
    have hGx : Continuous (fun p : PolarPoint => G (x, p)) :=
      J.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
        (fun p => ⟨hx, mem_univ p⟩)
    have hΘx : ContinuousOn (fun t => Θ (x, t)) (Icc a b) :=
      hΘ.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun t ht => ⟨hx, ht⟩)
    exact hasDerivAt_timeChange_classicalTrajectory
      ((hτrange 0).1.trans (hτrange 0).2) hGx hΘx (hflow x hx) hτrange
      (hτ.differentiable (by simp) r).hasDerivAt
  have hspeed' (m : ℕ) (x : E) (hx : x ∈ U)
      (L : (Fin m → ℝ) →L[ℝ] E) :
      ContDiffOn ℝ ∞ (fun p : (Fin m → ℝ) × PolarPoint => H (x + L p.1, p.2))
        (((fun q => x + L q) ⁻¹' U) ×ˢ (univ : Set PolarPoint)) := by
    have hd : ContDiff ℝ ∞ (deriv τ) := (contDiff_infty_iff_deriv.mp hτ).2
    exact (hd.comp contDiff_snd.fst).contDiffOn.mul
      ((hspeed m x hx L).comp
        (contDiff_fst.prodMk ((hτ.comp contDiff_snd.fst).prodMk contDiff_snd.snd)).contDiffOn
        (fun p hp => ⟨hp.1, mem_univ _⟩))
  exact topologicalCircleTrajectorySmoothDirections hU (J.timeChange hτ)
    hΦ hΦ0 hΦflow hspeed' s

/-- Every time in the original closed interval has a genuine state
tower, without any endpoint parameter derivative premise. -/
def topologicalCircleTrajectoryCompactSmoothDirections
    {U : Set E} {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ}
    {a b θ₀ : ℝ} (hU : IsOpen U) (J : ContinuousTimeSpeedTower U G)
    (hΘ : ContinuousOn Θ (U ×ˢ Icc a b))
    (hinit : ∀ x ∈ U, Θ (x, a) = θ₀)
    (hflow : ∀ x ∈ U, ∀ t ∈ Ioo a b,
      HasDerivAt (fun r => Θ (x, r)) (G (x, (t, Θ (x, t)))) t)
    (hspeed : ∀ m : ℕ, ∀ x ∈ U, ∀ L : (Fin m → ℝ) →L[ℝ] E,
      ContDiffOn ℝ ∞ (fun p : (Fin m → ℝ) × PolarPoint => G (x + L p.1, p.2))
        (((fun q => x + L q) ⁻¹' U) ×ˢ (univ : Set PolarPoint)))
    {t : ℝ} (ht : t ∈ Icc a b) : SmoothDirections U (fun x => Θ (x, t)) := by
  have hpreimage := circleFlowCompactTime_surjOn a b ht
  let s : ℝ := Classical.choose hpreimage
  have hs : circleFlowCompactTime a b s = t := (Classical.choose_spec hpreimage).2
  let K := topologicalCircleTrajectoryTimeChangeSmoothDirections hU J hΘ hinit hflow hspeed
    (contDiff_circleFlowCompactTime a b) (circleFlowCompactTime_zero a b)
    (circleFlowCompactTime_mem (ht.1.trans ht.2)) s
  exact K.congr (fun x _ => by rw [hs])

end ContinuousFlexibility.Analysis

