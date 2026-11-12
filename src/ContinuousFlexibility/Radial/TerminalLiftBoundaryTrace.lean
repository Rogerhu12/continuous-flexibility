import ContinuousFlexibility.Radial.TerminalPoissonFluxIdentity
import ContinuousFlexibility.Radial.TerminalCapLift
import ContinuousFlexibility.Radial.StandInBoundarySlope

/-!
# Boundary traces of the actual terminal lifts

Constant cutoff germs preserve the normalized value and the physical
outward slope at the lift's own matching cut. The zero germ at the other
cut gives both zero value and zero conormal flux.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem terminalCapLift_matching_trace {D : ReferenceData}
    (M : RadialMatchingData D) (χ u : Fin 2 → ℝ → ℝ)
    (hown : ∀ i, χ i =ᶠ[𝓝 (matchingCut D M i)] fun _ => (1 : ℝ))
    (hother : ∀ i k, i ≠ k → χ i =ᶠ[𝓝 (matchingCut D M k)] fun _ => (0 : ℝ))
    (hu : ∀ i, u i (matchingCut D M i) = 1) :
    ∀ i k, terminalCapLift (M.boundaryScale i) (χ i) (u i) (matchingCut D M k) =
      (if i = k then 1 else 0) / sqrt (M.boundaryScale k) := by
  intro i k
  by_cases hik : i = k
  · subst k
    rw [if_pos rfl, terminalCapLift_value (hown i).eq_of_nhds, hu i]
  · rw [if_neg hik]
    simp only [terminalCapLift, (hother i k hik).eq_of_nhds, zero_mul, zero_div]

theorem terminalCapLift_matching_flux {D : ReferenceData}
    (M : RadialMatchingData D) (hlh : M.innerLeft < M.innerRight)
    (χ u : Fin 2 → ℝ → ℝ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i)) (hu : ∀ i, ContDiff ℝ ∞ (u i))
    (hown : ∀ i, χ i =ᶠ[𝓝 (matchingCut D M i)] fun _ => (1 : ℝ))
    (hother : ∀ i k, i ≠ k → χ i =ᶠ[𝓝 (matchingCut D M k)] fun _ => (0 : ℝ))
    (hvalue : ∀ i, u i (matchingCut D M i) = 1)
    (hscale : ∀ i, M.boundaryScale i = standInBoundaryScale ((M.frequency : ℝ) ^ 2)
      (D.w (matchingCut D M i)) (matchingCut D M i))
    (hfreq : (0 : ℝ) < M.frequency)
    (hw : ∀ i, 0 < D.w (matchingCut D M i))
    (hr : ∀ i, 0 < matchingCut D M i) :
    ∀ i k, matchingInnerFlux D M (terminalCapLift (M.boundaryScale i) (χ i) (u i)) k =
      if i = k then standInBoundarySlope (bufferSign i) ((M.frequency : ℝ) ^ 2)
        (matchingCut D M i) (u i) else 0 := by
  intro i k
  have hdiff := (terminalCapLift_smooth (M.boundaryScale i) (hχ i) (hu i)).differentiable (by simp)
  have hwithin := (hdiff (matchingCut D M k)).derivWithin
    ((uniqueDiffOn_Icc hlh).uniqueDiffWithinAt (matchingCut_mem_innerIcc hlh k))
  by_cases hik : i = k
  · subst k
    rw [if_pos rfl]
    have hlam : 0 < M.boundaryScale i := by
      rw [hscale i]
      exact standInBoundaryScale_pos (sq_pos_of_pos hfreq) (hw i) (hr i)
    calc
      _ = bufferSign i * (D.w (matchingCut D M i) *
          deriv (terminalCapLift (M.boundaryScale i) (χ i) (u i)) (matchingCut D M i) /
            sqrt (M.boundaryScale i)) := by
        unfold matchingInnerFlux
        rw [hwithin]
        ring
      _ = bufferSign i * (D.w (matchingCut D M i) * deriv (u i) (matchingCut D M i) /
          M.boundaryScale i) := by rw [terminalCapLift_normalized_flux hlam (hown i)]
      _ = _ := by
        rw [standInBoundarySlope_eq_impedance (sq_pos_of_pos hfreq).ne' (hw i).ne'
          (hr i).ne' (by rw [hvalue i]; exact one_ne_zero), hvalue i, div_one, ← hscale i]
        ring
  · rw [if_neg hik]
    have hzero : terminalCapLift (M.boundaryScale i) (χ i) (u i) =ᶠ[𝓝 (matchingCut D M k)]
        fun _ => (0 : ℝ) := by
      filter_upwards [hother i k hik] with x hx
      simp only [terminalCapLift, hx, zero_mul, zero_div]
    have hderiv : deriv (terminalCapLift (M.boundaryScale i) (χ i) (u i)) (matchingCut D M k) = 0 := by
      simpa only [deriv_const] using hzero.deriv_eq
    unfold matchingInnerFlux
    rw [hwithin, hderiv, mul_zero, zero_div]

end ContinuousFlexibility.Radial

