import ContinuousFlexibility.Radial.OuterGreenKernel
import Mathlib.Analysis.Real.Sqrt

/-!
# Full-state normalization at the outer entrance

The entrance state is `(u, w u' / λ)`.  Its Euclidean length, rather than
its first coordinate, normalizes the natural solution.  In particular the
construction remains meaningful when the natural solution vanishes at the
entrance.  The perpendicular initial state fixes the weighted Wronskian
exactly and gives both boundary traces of variation of parameters.

The ordinary product type has the maximum norm.  All Euclidean assertions
in this file are therefore explicit coordinate identities.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set

/-- Value and scaled outward flux, in the coordinates of Lemma 6.5. -/
def outerFluxState (lam : ℝ) (w u : ℝ → ℝ) (r : ℝ) : ℝ × ℝ :=
  (u r, w r * deriv u r / lam)

/-- The Euclidean pairing of two value/flux states. -/
def outerStatePair (v x : ℝ × ℝ) : ℝ := v.1 * x.1 + v.2 * x.2

/-- The positively oriented perpendicular to an entrance state. -/
def outerStatePerp (v : ℝ × ℝ) : ℝ × ℝ := (-v.2, v.1)

/-- Normalize the full state; no boundary value is a denominator. -/
def outerUnitState (v : ℝ × ℝ) : ℝ × ℝ :=
  (v.1 / Real.sqrt (v.1 ^ 2 + v.2 ^ 2),
    v.2 / Real.sqrt (v.1 ^ 2 + v.2 ^ 2))

theorem outerState_sq_pos {v : ℝ × ℝ} (hv : v ≠ 0) :
    0 < v.1 ^ 2 + v.2 ^ 2 := by
  have hx := sq_nonneg v.1
  have hy := sq_nonneg v.2
  by_contra h
  have hzero : v.1 ^ 2 + v.2 ^ 2 = 0 :=
    le_antisymm (le_of_not_gt h) (add_nonneg hx hy)
  have h₁ : v.1 = 0 := by nlinarith
  have h₂ : v.2 = 0 := by nlinarith
  exact hv (Prod.ext h₁ h₂)

/-- A nonzero natural state has a unit full-state normalization. -/
theorem outerUnitState_unit {v : ℝ × ℝ} (hv : v ≠ 0) :
    (outerUnitState v).1 ^ 2 + (outerUnitState v).2 ^ 2 = 1 := by
  have hpos := outerState_sq_pos hv
  dsimp only [outerUnitState]
  rw [div_pow, div_pow, ← add_div, Real.sq_sqrt hpos.le, div_self hpos.ne']

theorem outerStatePair_perp (v : ℝ × ℝ) :
    outerStatePair v (outerStatePerp v) = 0 := by
  dsimp only [outerStatePair, outerStatePerp]
  ring

theorem outerStatePerp_unit {v : ℝ × ℝ} (hv : v.1 ^ 2 + v.2 ^ 2 = 1) :
    (outerStatePerp v).1 ^ 2 + (outerStatePerp v).2 ^ 2 = 1 := by
  dsimp only [outerStatePerp]
  nlinarith

theorem outerStatePair_perp_self {v : ℝ × ℝ}
    (hv : v.1 ^ 2 + v.2 ^ 2 = 1) :
    outerStatePair (outerStatePerp v) (outerStatePerp v) = 1 := by
  dsimp only [outerStatePair, outerStatePerp]
  nlinarith

/-- The two boundary traces determine the state. -/
theorem outerState_boundary_coordinates {v x : ℝ × ℝ}
    (hv : v.1 ^ 2 + v.2 ^ 2 = 1) :
    x = (outerStatePair v x) • v +
      (outerStatePair (outerStatePerp v) x) • outerStatePerp v := by
  apply Prod.ext
  · change x.1 = (v.1 * x.1 + v.2 * x.2) * v.1 +
      ((-v.2) * x.1 + v.1 * x.2) * (-v.2)
    nlinarith [congrArg (fun t : ℝ => t * x.1) hv]
  · change x.2 = (v.1 * x.1 + v.2 * x.2) * v.2 +
      ((-v.2) * x.1 + v.1 * x.2) * v.1
    nlinarith [congrArg (fun t : ℝ => t * x.2) hv]

/-- Orthogonal unit initial states give the exact Wronskian `-λ`. -/
theorem radialWronskian_of_outerStates {lam c : ℝ} {w U V : ℝ → ℝ}
    {v : ℝ × ℝ} (hlam : lam ≠ 0) (hv : v.1 ^ 2 + v.2 ^ 2 = 1)
    (hU : outerFluxState lam w U c = outerStatePerp v)
    (hV : outerFluxState lam w V c = v) :
    radialWronskian w U V c = -lam := by
  have hU₁ : U c = -v.2 := congrArg Prod.fst hU
  have hU₂ : w c * deriv U c / lam = v.1 := congrArg Prod.snd hU
  have hV₁ : V c = v.1 := congrArg Prod.fst hV
  have hV₂ : w c * deriv V c / lam = v.2 := congrArg Prod.snd hV
  have hfU : w c * deriv U c = v.1 * lam := (div_eq_iff hlam).mp hU₂
  have hfV : w c * deriv V c = v.2 * lam := (div_eq_iff hlam).mp hV₂
  calc
    radialWronskian w U V c =
        U c * (w c * deriv V c) - (w c * deriv U c) * V c := by
      unfold radialWronskian
      ring
    _ = -(v.1 ^ 2 + v.2 ^ 2) * lam := by rw [hU₁, hV₁, hfU, hfV]; ring
    _ = -lam := by rw [hv]; ring

/-- Propagation preserves the normalized Wronskian throughout the interval. -/
theorem radialWronskian_eq_neg_scale {α β J lam c : ℝ} {w U V : ℝ → ℝ}
    {v : ℝ × ℝ} (hlam : lam ≠ 0) (hv : v.1 ^ 2 + v.2 ^ 2 = 1)
    (hc : c ∈ Ioo α β)
    (hreg : ∀ r ∈ Ioo α β, DifferentiableAt ℝ w r ∧ DifferentiableAt ℝ U r ∧
      DifferentiableAt ℝ (deriv U) r ∧ DifferentiableAt ℝ V r ∧
      DifferentiableAt ℝ (deriv V) r)
    (hUeq : ∀ r ∈ Ioo α β, radialJacobi J w U r = 0)
    (hVeq : ∀ r ∈ Ioo α β, radialJacobi J w V r = 0)
    (hU : outerFluxState lam w U c = outerStatePerp v)
    (hV : outerFluxState lam w V c = v) :
    ∀ r ∈ Ioo α β, radialWronskian w U V r = -lam := by
  intro r hr
  exact (radialWronskian_const hreg hUeq hVeq r hr c hc).trans
    (radialWronskian_of_outerStates hlam hv hU hV)

/-- At the entrance the solution is a scalar multiple of the perpendicular state. -/
theorem outerSolution_base_state {α β lam cB c : ℝ} {w U V f : ℝ → ℝ}
    (hUd : ∀ r ∈ Ioo α β, DifferentiableAt ℝ U r)
    (hVd : ∀ r ∈ Ioo α β, DifferentiableAt ℝ V r)
    (hf : ContinuousOn f (Ioo α β)) (hc : c ∈ Ioo α β) :
    outerFluxState lam w (outerSolution lam 0 cB c U V f) c =
      (-(cB / lam)) • outerFluxState lam w U c := by
  apply Prod.ext
  · exact outerSolution_base
  · change w c * deriv (outerSolution lam 0 cB c U V f) c / lam =
      (-(cB / lam)) * (w c * deriv U c / lam)
    rw [deriv_outerSolution_base hUd hVd hf hc]
    ring

/-- The Robin trace vanishes even when `V c = 0`. -/
theorem outerSolution_normalized_robin {α β lam cB c : ℝ} {w U V f : ℝ → ℝ}
    {v : ℝ × ℝ}
    (hUd : ∀ r ∈ Ioo α β, DifferentiableAt ℝ U r)
    (hVd : ∀ r ∈ Ioo α β, DifferentiableAt ℝ V r)
    (hf : ContinuousOn f (Ioo α β)) (hc : c ∈ Ioo α β)
    (hU : outerFluxState lam w U c = outerStatePerp v) :
    outerStatePair v (outerFluxState lam w (outerSolution lam 0 cB c U V f) c) = 0 := by
  rw [outerSolution_base_state hUd hVd hf hc, hU]
  change v.1 * (-(cB / lam) * (-v.2)) + v.2 * (-(cB / lam) * v.1) = 0
  ring

/-- The complementary entrance trace has exactly the source coefficient. -/
theorem outerSolution_complementary_trace {α β lam cB c : ℝ} {w U V f : ℝ → ℝ}
    {v : ℝ × ℝ} (hv : v.1 ^ 2 + v.2 ^ 2 = 1)
    (hUd : ∀ r ∈ Ioo α β, DifferentiableAt ℝ U r)
    (hVd : ∀ r ∈ Ioo α β, DifferentiableAt ℝ V r)
    (hf : ContinuousOn f (Ioo α β)) (hc : c ∈ Ioo α β)
    (hU : outerFluxState lam w U c = outerStatePerp v) :
    outerStatePair (outerStatePerp v)
      (outerFluxState lam w (outerSolution lam 0 cB c U V f) c) = -(cB / lam) := by
  rw [outerSolution_base_state hUd hVd hf hc, hU]
  change (-v.2) * (-(cB / lam) * (-v.2)) + v.1 * (-(cB / lam) * v.1) = -(cB / lam)
  nlinarith [congrArg (fun t : ℝ => -(cB / lam) * t) hv]

end ContinuousFlexibility.Radial
