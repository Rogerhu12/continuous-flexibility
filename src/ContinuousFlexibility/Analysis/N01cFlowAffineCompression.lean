import ContinuousFlexibility.Analysis.N01cVolterraNaturality
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Finite affine flow germs inside the actual state neighbourhood

A smooth compression is the identity near zero and maps the entire
finite parameter space into the permitted neighbourhood. Both the speed
and the supplied classical trajectories are composed with this same
compression. The global finite-parameter theorem therefore applies to
actual trajectories. Local equality of the speeds identifies their jets,
and Volterra naturality transfers the result to the original state.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

section Compression

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]

/-- A finite-dimensional smooth compression into any neighbourhood of
zero, equal to the identity on a smaller neighbourhood. -/
theorem exists_smooth_neighbourhood_compression {V : Set P}
    (hV : IsOpen V) (h0 : (0 : P) ∈ V) :
    ∃ ρ : P → P, ContDiff ℝ ∞ ρ ∧ ρ 0 = 0 ∧
      (∀ q, ρ q ∈ V) ∧ ρ =ᶠ[𝓝 (0 : P)] id := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0)
  let χ : ContDiffBump (0 : P) :=
    { rIn := ε / 2
      rOut := ε
      rIn_pos := half_pos hε
      rIn_lt_rOut := half_lt_self hε }
  let ρ : P → P := fun q => χ q • q
  have hχ : ContDiff ℝ ∞ (fun q : P => χ q) := χ.contDiff
  refine ⟨ρ, hχ.smul contDiff_id, by simp [ρ], ?_, ?_⟩
  · intro q
    by_cases hz : χ q = 0
    · simpa only [ρ, hz, zero_smul] using h0
    · have hq : q ∈ Metric.ball (0 : P) ε := by
        change q ∈ Metric.ball (0 : P) χ.rOut
        rw [← χ.support_eq]
        exact hz
      have hq' : ‖q‖ < ε := by simpa only [Metric.mem_ball, dist_zero_right] using hq
      apply hball
      change dist (ρ q) 0 < ε
      rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg χ.nonneg]
      exact (mul_le_of_le_one_left (norm_nonneg q) χ.le_one).trans_lt hq'
  · filter_upwards [χ.eventuallyEq_one] with q hq
    simpa only [ρ, hq, Pi.one_apply, one_smul, id_eq]

def speedTimeSliceInjection : (P × ℝ) →L[ℝ] (P × PolarPoint) :=
  (ContinuousLinearMap.fst ℝ P ℝ).prod
    ((0 : (P × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ P ℝ))

@[simp] theorem speedTimeSliceInjection_apply (p : P × ℝ) :
    speedTimeSliceInjection p = (p.1, (0, p.2)) := rfl

theorem iteratedFDeriv_speed_timeSlice {G : P × PolarPoint → ℝ}
    (hG : ContDiff ℝ ∞ G) (n : ℕ) (t : ℝ) (q : P × ℝ)
    (v : Fin n → P × ℝ) :
    iteratedFDeriv ℝ n (fun y : P × ℝ => G (y.1, (t, y.2))) q v =
      iteratedFDeriv ℝ n G (q.1, (t, q.2))
        (fun i => speedTimeSliceInjection (v i)) := by
  let J : SmoothDirections (univ : Set (P × PolarPoint)) G :=
    smoothDirectionsOfJets isOpen_univ (fun k => iteratedFDeriv ℝ k G)
      (hasProjectiveJetsOn_of_contDiffOn isOpen_univ hG.contDiffOn)
  have h := smoothDirections_iteratedFDeriv_finiteAffine J (0, (t, 0))
    speedTimeSliceInjection n (y := q) (mem_univ _) v
  dsimp only [J, smoothDirectionsOfJets] at h
  simpa only [speedTimeSliceInjection_apply, Prod.mk_add_mk, zero_add, add_zero] using h

/-- A jointly smooth finite-parameter speed has the required genuine
time-indexed state-and-angle jets with joint evaluation continuity. -/
def continuousTimeSpeedTowerOfContDiff {G : P × PolarPoint → ℝ}
    (hG : ContDiff ℝ ∞ G) : ContinuousTimeSpeedTower (univ : Set P) G where
  jet t := smoothDirectionsOfJets (isOpen_univ.prod isOpen_univ)
    (fun k => iteratedFDeriv ℝ k (fun y : P × ℝ => G (y.1, (t, y.2))))
    (hasProjectiveJetsOn_of_contDiffOn (isOpen_univ.prod isOpen_univ)
      ((hG.comp (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd))).contDiffOn))
  continuous := by
    intro n
    dsimp only [smoothDirectionsOfJets]
    have hc : Continuous (fun p : (P × PolarPoint) × (Fin n → P × ℝ) =>
        iteratedFDeriv ℝ n G p.1 (fun i => speedTimeSliceInjection (p.2 i))) :=
      ((hG.continuous_iteratedFDeriv (by simp)).comp continuous_fst).eval
        (continuous_pi (fun i => speedTimeSliceInjection.continuous.comp
          ((continuous_apply i).comp continuous_snd)))
    simpa only [iteratedFDeriv_speed_timeSlice hG] using hc.continuousOn

theorem continuousTimeSpeedTowerOfContDiff_D_apply {G : P × PolarPoint → ℝ}
    (hG : ContDiff ℝ ∞ G) (n : ℕ) (p : P × PolarPoint)
    (v : Fin n → P × ℝ) :
    (continuousTimeSpeedTowerOfContDiff hG).D n p v =
      iteratedFDeriv ℝ n (fun y : P × ℝ => G (y.1, (p.2.1, y.2)))
        (p.1, p.2.2) v := rfl

end Compression

section AffineGerm

variable {E : Type*} {P : Type}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- Actual finite affine flow germs are smooth and their genuine jets
are the Volterra variations of the original topological state space.
The only finite-dimensional smoothness input concerns the speed. -/
theorem flow_finiteAffine_germ_jets
    {U : Set E} {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ} {θ₀ : ℝ}
    (hU : IsOpen U) (J : ContinuousTimeSpeedTower U G)
    (hΘ : ContinuousOn Θ (U ×ˢ (univ : Set ℝ)))
    (hinit : ∀ x ∈ U, Θ (x, 0) = θ₀)
    (hflow : ∀ x ∈ U, ∀ t : ℝ,
      HasDerivAt (fun r => Θ (x, r)) (G (x, (t, Θ (x, t)))) t)
    (x : E) (hx : x ∈ U) (L : P →L[ℝ] E)
    (hspeed : ContDiffOn ℝ ∞ (fun p : P × PolarPoint => G (x + L p.1, p.2))
      (((fun q => x + L q) ⁻¹' U) ×ˢ (univ : Set PolarPoint))) :
    (∀ t : ℝ, ContDiffAt ℝ ∞ (fun q : P => Θ (x + L q, t)) 0) ∧
      ∀ n : ℕ, ∀ t : ℝ, ∀ v : Fin n → P,
        iteratedFDeriv ℝ n (fun q : P => Θ (x + L q, t)) 0 v =
          (volterraStateVariation J hΘ n).value (x, t) (fun i => L (v i)) := by
  let V : Set P := (fun q => x + L q) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_const.add L.continuous)
  have h0 : (0 : P) ∈ V := by simpa only [V, mem_preimage, map_zero, add_zero] using hx
  obtain ⟨ρ, hρ, hρ0, hρV, hρid⟩ := exists_smooth_neighbourhood_compression hV h0
  let H : P × PolarPoint → ℝ := fun p => G (x + L (ρ p.1), p.2)
  let Φ : P × ℝ → ℝ := fun p => Θ (x + L (ρ p.1), p.2)
  have hH : ContDiff ℝ ∞ H :=
    hspeed.comp_contDiff ((hρ.comp contDiff_fst).prodMk contDiff_snd)
      (fun p => ⟨hρV p.1, mem_univ p.2⟩)
  have hΦ : Continuous Φ :=
    hΘ.comp_continuous
      ((continuous_const.add (L.continuous.comp (hρ.continuous.comp continuous_fst))).prodMk
        continuous_snd)
      (fun p => ⟨hρV p.1, mem_univ p.2⟩)
  have hΦ0 (q : P) : Φ (q, 0) = θ₀ := hinit _ (hρV q)
  have hΦflow (q : P) (t : ℝ) :
      HasDerivAt (fun r => Φ (q, r)) (H (q, (t, Φ (q, t)))) t :=
    hflow _ (hρV q) t
  have hΦsmooth := contDiff_globalCircleVectorTrajectory hH hΦ hΦ0 hΦflow
  let K := continuousTimeSpeedTowerOfContDiff hH
  have hbase (t : ℝ) : Φ (0, t) = Θ (x, t) := by simp only [Φ, hρ0, map_zero, add_zero]
  have hjets (t θ : ℝ) (n : ℕ) (v : Fin n → P × ℝ) :
      K.D n (0, (t, θ)) v =
        J.D n (x, (t, θ)) (fun i => flowStateAngleMap L (v i)) := by
    have he : (fun q : P × ℝ => H (q.1, (t, q.2))) =ᶠ[𝓝 ((0 : P), θ)]
        (fun q : P × ℝ => G (x + L q.1, (t, q.2))) := by
      filter_upwards [continuousAt_fst.tendsto.eventually hρid] with q hq
      simp only [H, hq, id_eq]
    have hejet := (he.iteratedFDeriv ℝ n).self_of_nhds
    have hpoint : (x, (0 : ℝ)) + flowStateAngleMap L (0, θ) ∈ U ×ˢ (univ : Set ℝ) := by
      simpa only [flowStateAngleMap_apply, map_zero, Prod.mk_add_mk, add_zero, zero_add] using
        (show (x, θ) ∈ U ×ˢ (univ : Set ℝ) from ⟨hx, mem_univ θ⟩)
    have ha := smoothDirections_iteratedFDeriv_finiteAffine (J.jet t) (x, (0 : ℝ))
      (flowStateAngleMap L) n hpoint v
    calc
      K.D n (0, (t, θ)) v =
          iteratedFDeriv ℝ n (fun q : P × ℝ => H (q.1, (t, q.2))) (0, θ) v := rfl
      _ = iteratedFDeriv ℝ n (fun q : P × ℝ => G (x + L q.1, (t, q.2))) (0, θ) v :=
        congrArg (fun B : (P × ℝ) [×n]→L[ℝ] ℝ => B v) hejet
      _ = J.D n (x, (t, θ)) (fun i => flowStateAngleMap L (v i)) := by
        simpa only [ContinuousTimeSpeedTower.D, flowStateAngleMap_apply, map_zero,
          Prod.mk_add_mk, add_zero, zero_add] using ha
  have htrajectory (t : ℝ) :
      (fun q : P => Φ (q, t)) =ᶠ[𝓝 (0 : P)] (fun q => Θ (x + L q, t)) := by
    filter_upwards [hρid] with q hq
    simp only [Φ, hq, id_eq]
  refine ⟨fun t => ?_, fun n t v => ?_⟩
  · exact ((hΦsmooth.comp (contDiff_id.prodMk contDiff_const)).contDiffAt).congr_of_eventuallyEq
      (htrajectory t).symm
  · have hcanonical := congrArg (fun B : P [×n]→L[ℝ] ℝ => B v)
      (volterraStateVariation_eq_iteratedFDeriv K hH hΦ hΦ0 hΦflow n (0, t))
    have hnatural := volterraStateVariation_natural_at J K hΘ hΦ.continuousOn
      L hx (mem_univ (0 : P)) hbase hjets n v t
    calc
      iteratedFDeriv ℝ n (fun q : P => Θ (x + L q, t)) 0 v =
          iteratedFDeriv ℝ n (fun q : P => Φ (q, t)) 0 v :=
        (congrArg (fun B : P [×n]→L[ℝ] ℝ => B v)
          (((htrajectory t).iteratedFDeriv ℝ n).self_of_nhds)).symm
      _ = (volterraStateVariation K hΦ.continuousOn n).value (0, t) v := hcanonical.symm
      _ = (volterraStateVariation J hΘ n).value (x, t) (fun i => L (v i)) := hnatural

end AffineGerm

end ContinuousFlexibility.Analysis

