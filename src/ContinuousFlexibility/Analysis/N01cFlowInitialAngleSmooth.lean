module

public import ContinuousFlexibility.Analysis.N01cFlowCompactStateSmooth

/-!
# Joint state and initial-angle smoothness of the supplied circle flow

An initial-angle translation turns the initial condition into zero.
The shifted speed uses the same genuine state-and-angle speed tower.
The compact-time theorem then supplies a genuine joint tower, and
adding back the initial angle recovers the actual supplied flow.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

def flowInitialAngleMap : ((E × ℝ) × ℝ) →L[ℝ] (E × ℝ) :=
  ((ContinuousLinearMap.fst ℝ E ℝ).comp (ContinuousLinearMap.fst ℝ (E × ℝ) ℝ)).prod
    ((ContinuousLinearMap.snd ℝ (E × ℝ) ℝ) +
      (ContinuousLinearMap.snd ℝ E ℝ).comp (ContinuousLinearMap.fst ℝ (E × ℝ) ℝ))

@[simp] theorem flowInitialAngleMap_apply (p : (E × ℝ) × ℝ) :
    flowInitialAngleMap p = (p.1.1, p.2 + p.1.2) := rfl

def initialAngleSpeed (G : E × PolarPoint → ℝ) (p : (E × ℝ) × PolarPoint) : ℝ :=
  G (p.1.1, (p.2.1, p.2.2 + p.1.2))

def ContinuousTimeSpeedTower.initialAngle
    {U : Set E} {G : E × PolarPoint → ℝ}
    (hU : IsOpen U) (J : ContinuousTimeSpeedTower U G) :
    ContinuousTimeSpeedTower (U ×ˢ (univ : Set ℝ)) (initialAngleSpeed G) where
  jet t := by
    let K := smoothDirections_precompCLM (J.jet t) (flowInitialAngleMap (E := E))
    refine
      { open_domain := (hU.prod isOpen_univ).prod isOpen_univ
        D := K.D
        zero := fun p hp => K.zero p ⟨hp.1.1, mem_univ _⟩
        continuous := fun n => (K.continuous n).mono
          (fun p hp => ⟨⟨hp.1.1.1, mem_univ _⟩, hp.2⟩)
        derivative := fun n p hp v w => K.derivative n p ⟨hp.1.1, mem_univ _⟩ v w }
  continuous := by
    intro n
    change ContinuousOn (fun p : ((E × ℝ) × PolarPoint) × (Fin n → (E × ℝ) × ℝ) =>
      J.D n (p.1.1.1, (p.1.2.1, p.1.2.2 + p.1.1.2))
        (fun i => flowInitialAngleMap (p.2 i))) _
    exact (J.continuous n).comp
      (((continuous_fst.fst.fst.prodMk
        (continuous_fst.snd.fst.prodMk
          (continuous_fst.snd.snd.add continuous_fst.fst.snd))).prodMk
        (continuous_pi (fun i => flowInitialAngleMap.continuous.comp
          ((continuous_apply i).comp continuous_snd)))).continuousOn)
      (fun p hp => ⟨⟨hp.1.1.1, mem_univ _⟩, mem_univ _⟩)

/-- At every original closed-interval time, the actual flow is genuinely
smooth jointly in the topological state and the real initial angle. -/
def topologicalCircleFlowCompactSmoothDirections
    {U : Set E} {G : E × PolarPoint → ℝ} {Θ : E × PolarPoint → ℝ}
    {a b : ℝ} (hU : IsOpen U) (J : ContinuousTimeSpeedTower U G)
    (hΘ : ContinuousOn Θ (U ×ˢ (Icc a b ×ˢ (univ : Set ℝ))))
    (hinit : ∀ x ∈ U, ∀ α : ℝ, Θ (x, (a, α)) = α)
    (hflow : ∀ x ∈ U, ∀ t ∈ Ioo a b, ∀ α : ℝ,
      HasDerivAt (fun r => Θ (x, (r, α))) (G (x, (t, Θ (x, (t, α))))) t)
    (hspeed : ∀ m : ℕ, ∀ x ∈ U, ∀ L : (Fin m → ℝ) →L[ℝ] E,
      ContDiffOn ℝ ∞ (fun p : (Fin m → ℝ) × PolarPoint => G (x + L p.1, p.2))
        (((fun q => x + L q) ⁻¹' U) ×ˢ (univ : Set PolarPoint)))
    {t : ℝ} (ht : t ∈ Icc a b) :
    SmoothDirections (U ×ˢ (univ : Set ℝ)) (fun p => Θ (p.1, (t, p.2))) := by
  let Ψ : (E × ℝ) × ℝ → ℝ := fun p => Θ (p.1.1, (p.2, p.1.2)) - p.1.2
  have hΨ : ContinuousOn Ψ ((U ×ˢ (univ : Set ℝ)) ×ˢ Icc a b) :=
    (hΘ.comp (continuous_fst.fst.prodMk
      (continuous_snd.prodMk continuous_fst.snd)).continuousOn
      (fun p hp => ⟨hp.1.1, hp.2, mem_univ _⟩)).sub continuous_fst.snd.continuousOn
  have hΨ0 (p : E × ℝ) (hp : p ∈ U ×ˢ (univ : Set ℝ)) : Ψ (p, a) = 0 := by
    dsimp only [Ψ]
    rw [hinit p.1 hp.1 p.2, sub_self]
  have hΨflow (p : E × ℝ) (hp : p ∈ U ×ˢ (univ : Set ℝ))
      (r : ℝ) (hr : r ∈ Ioo a b) :
      HasDerivAt (fun s => Ψ (p, s)) (initialAngleSpeed G (p, (r, Ψ (p, r)))) r := by
    simpa only [Ψ, initialAngleSpeed, sub_add_cancel] using
      (hflow p.1 hp.1 r hr p.2).sub_const p.2
  have hspeed' (m : ℕ) (p : E × ℝ) (hp : p ∈ U ×ˢ (univ : Set ℝ))
      (L : (Fin m → ℝ) →L[ℝ] (E × ℝ)) :
      ContDiffOn ℝ ∞
        (fun q : (Fin m → ℝ) × PolarPoint => initialAngleSpeed G (p + L q.1, q.2))
        (((fun q => p + L q) ⁻¹' (U ×ˢ (univ : Set ℝ))) ×ˢ
          (univ : Set PolarPoint)) := by
    let Lx := (ContinuousLinearMap.fst ℝ E ℝ).comp L
    let Lα := (ContinuousLinearMap.snd ℝ E ℝ).comp L
    exact (hspeed m p.1 hp.1 Lx).comp
      (contDiff_fst.prodMk (contDiff_snd.fst.prodMk
        (contDiff_snd.snd.add (contDiff_const.add (Lα.contDiff.comp contDiff_fst))))).contDiffOn
      (fun q hq => ⟨hq.1.1, mem_univ _⟩)
  let K := topologicalCircleTrajectoryCompactSmoothDirections
    (hU.prod isOpen_univ) (J.initialAngle hU) hΨ hΨ0 hΨflow hspeed' ht
  let A : SmoothDirections (U ×ˢ (univ : Set ℝ)) (ContinuousLinearMap.snd ℝ E ℝ) :=
    smoothDirectionsOfJets (hU.prod isOpen_univ)
      (continuousLinearJets (ContinuousLinearMap.snd ℝ E ℝ))
      (hasProjectiveJetsOn_continuousLinear (ContinuousLinearMap.snd ℝ E ℝ) _)
  exact (smoothDirectionsAdd K A).congr (fun p _ => by
    change Θ (p.1, (t, p.2)) - p.2 + p.2 = _
    exact sub_add_cancel _ _)

end ContinuousFlexibility.Analysis
