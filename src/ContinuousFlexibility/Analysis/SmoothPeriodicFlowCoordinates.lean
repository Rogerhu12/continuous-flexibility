module

public import ContinuousFlexibility.Analysis.SmoothPeriodicScalarFlowEndpoint
public import ContinuousFlexibility.Analysis.ParameterizedCircleInverse

/-!
# Actual inverse-flow coordinates

The smooth periodic field constructs the chosen trajectories. Their
endpoint map has a positive angular derivative and a genuine inverse.
Composing a smooth boundary coordinate with this actual inverse gives
the smooth coordinate used on the characteristic chart. Every flow
regularity assertion in this construction is a conclusion.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

/-- Construct the actual forward flow, its smooth inverse, and the
boundary coordinate composed with that inverse. -/
theorem exists_smooth_periodicFlowCoordinates
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {F : ℝ × (P × ℝ) → ℝ} {hL : P × ℝ → ℝ} {a b T : ℝ}
    (hab : a ≤ b) (hT : T ≠ 0) (hF : ContDiff ℝ ∞ F)
    (hL_smooth : ContDiff ℝ ∞ hL)
    (hperiod : ∀ t ∈ Icc a b, ∀ p : P,
      Function.Periodic (fun θ => F (t, (p, θ))) T) :
    ∃ Θ : P → ℝ → ℝ → ℝ,
      (∀ p θ, Θ p a θ = θ) ∧
      (∀ p θ t, t ∈ Icc a b →
        HasDerivWithinAt (fun r => Θ p r θ)
          (F (t, (p, Θ p t θ))) (Icc a b) t) ∧
      (∀ p θ t, t ∈ Icc a b → Θ p t (θ + T) = Θ p t θ + T) ∧
      ContinuousOn (fun z : (P × ℝ) × ℝ => Θ z.1.1 z.2 z.1.2)
        (univ ×ˢ Icc a b) ∧
      let forward : P × ℝ → ℝ := fun z => Θ z.1 b z.2
      let inverse : P × ℝ → ℝ := parameterizedCircleInverse forward
      let coordinate : P × ℝ → ℝ := fun z => hL (z.1, inverse z)
      ContDiff ℝ ∞ forward ∧
      (∀ z : P × ℝ, 0 < deriv (fun θ => forward (z.1, θ)) z.2) ∧
      ContDiff ℝ ∞ inverse ∧ ContDiff ℝ ∞ coordinate ∧
      ∀ z : P × ℝ,
        forward (z.1, inverse z) = z.2 ∧
        inverse (z.1, forward z) = z.2 ∧
        coordinate (z.1, forward z) = hL z := by
  obtain ⟨Θ, hinit, hflow, hper, hcont, hsmooth, hpositive⟩ :=
    exists_smooth_periodicScalarFlowFamily hab hT hF hperiod
  let forward : P × ℝ → ℝ := fun z => Θ z.1 b z.2
  have hp : ∀ z : P × ℝ, 0 < deriv (fun θ => forward (z.1, θ)) z.2 :=
    fun z => hpositive z.1 z.2
  have he : ∀ p θ, forward (p, θ + T) = forward (p, θ) + T :=
    fun p θ => hper p θ b ⟨hab, le_rfl⟩
  have hi : ContDiff ℝ ∞ (parameterizedCircleInverse forward) :=
    contDiff_parameterizedCircleInverse (F := forward) hT hsmooth hp he
  have hc : ContDiff ℝ ∞
      (fun z : P × ℝ => hL (z.1, parameterizedCircleInverse forward z)) :=
    hL_smooth.comp (contDiff_fst.prodMk hi)
  refine ⟨Θ, hinit, hflow, hper, hcont, hsmooth, hp, hi, hc, ?_⟩
  intro z
  have hright := parameterizedCircleInverse_right_inverse (F := forward) hT hsmooth he z
  have hleft := parameterizedCircleInverse_left_inverse (F := forward) hp z
  refine ⟨hright, hleft, ?_⟩
  exact congrArg (fun θ => hL (z.1, θ)) hleft

end ContinuousFlexibility.Analysis
