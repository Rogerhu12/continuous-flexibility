module

public import ContinuousFlexibility.Analysis.SmoothPeriodicScalarFlow
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Actual flows for the regularized root characteristic field

After the radial substitution r = x t² and the independent root
parameter ζ, the characteristic speed is
  2 x t d(x t², θ) + 2 ζ t² c₀(x t², θ).
This is a smooth, periodic field whenever the extended coefficient
functions d and c₀ are smooth and periodic.  The general periodic-flow
construction therefore gives actual solutions, angular equivariance,
and joint continuity in (x, ζ), initial angle, and time.

These statements concern the displayed regularized field itself.
Smooth extension of physical coefficient germs is a separate input.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff Topology

/-- The root-regularized characteristic speed, with coordinates
(time, ((radial parameter, independent root parameter), angle)). -/
def rootRegularizedField (d c₀ : ℝ × ℝ → ℝ) :
    ℝ × ((ℝ × ℝ) × ℝ) → ℝ :=
  fun q =>
    2 * q.2.1.1 * q.1 * d (q.2.1.1 * q.1 ^ 2, q.2.2) +
      2 * q.2.1.2 * q.1 ^ 2 * c₀ (q.2.1.1 * q.1 ^ 2, q.2.2)

/-- Smoothness of the actual polynomially regularized speed follows
from smoothness of the coefficient functions. -/
theorem contDiff_rootRegularizedField
    {d c₀ : ℝ × ℝ → ℝ}
    (hd : ContDiff ℝ ∞ d) (hc₀ : ContDiff ℝ ∞ c₀) :
    ContDiff ℝ ∞ (rootRegularizedField d c₀) := by
  have ht : ContDiff ℝ ∞
      (fun q : ℝ × ((ℝ × ℝ) × ℝ) => q.1) := contDiff_fst
  have hx : ContDiff ℝ ∞
      (fun q : ℝ × ((ℝ × ℝ) × ℝ) => q.2.1.1) := contDiff_snd.fst.fst
  have hz : ContDiff ℝ ∞
      (fun q : ℝ × ((ℝ × ℝ) × ℝ) => q.2.1.2) := contDiff_snd.fst.snd
  have hθ : ContDiff ℝ ∞
      (fun q : ℝ × ((ℝ × ℝ) × ℝ) => q.2.2) := contDiff_snd.snd
  have htwo : ContDiff ℝ ∞
      (fun _ : ℝ × ((ℝ × ℝ) × ℝ) => (2 : ℝ)) := contDiff_const
  have harg : ContDiff ℝ ∞
      (fun q : ℝ × ((ℝ × ℝ) × ℝ) => (q.2.1.1 * q.1 ^ 2, q.2.2)) :=
    (hx.mul (ht.pow 2)).prodMk hθ
  exact (((htwo.mul hx).mul ht).mul (hd.comp harg)).add
    (((htwo.mul hz).mul (ht.pow 2)).mul (hc₀.comp harg))

/-- Angular periodicity is preserved by the root regularization. -/
theorem rootRegularizedField_periodic
    {d c₀ : ℝ × ℝ → ℝ} {T : ℝ}
    (hd : ∀ r : ℝ, Function.Periodic (fun θ => d (r, θ)) T)
    (hc₀ : ∀ r : ℝ, Function.Periodic (fun θ => c₀ (r, θ)) T)
    (t : ℝ) (p : ℝ × ℝ) :
    Function.Periodic (fun θ => rootRegularizedField d c₀ (t, (p, θ))) T := by
  intro θ
  simp only [rootRegularizedField, hd (p.1 * t ^ 2) θ, hc₀ (p.1 * t ^ 2) θ]

/-- The regularized root field has actual solutions on [0,1], jointly
continuous in both independent parameters, the initial angle, and time.
No regularity of a preselected solution family is assumed. -/
theorem exists_continuous_rootRegularizedFlow
    {d c₀ : ℝ × ℝ → ℝ} {T : ℝ}
    (hT : T ≠ 0)
    (hd : ContDiff ℝ ∞ d) (hc₀ : ContDiff ℝ ∞ c₀)
    (hdperiod : ∀ r : ℝ, Function.Periodic (fun θ => d (r, θ)) T)
    (hc₀period : ∀ r : ℝ, Function.Periodic (fun θ => c₀ (r, θ)) T) :
    ∃ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
      (∀ p θ, Θ p 0 θ = θ) ∧
      (∀ p θ t, t ∈ Icc (0 : ℝ) 1 →
        HasDerivWithinAt (fun r => Θ p r θ)
          (2 * p.1 * t * d (p.1 * t ^ 2, Θ p t θ) +
            2 * p.2 * t ^ 2 * c₀ (p.1 * t ^ 2, Θ p t θ))
          (Icc (0 : ℝ) 1) t) ∧
      (∀ p θ t, t ∈ Icc (0 : ℝ) 1 →
        Θ p t (θ + T) = Θ p t θ + T) ∧
      ContinuousOn
        (fun q : ((ℝ × ℝ) × ℝ) × ℝ => Θ q.1.1 q.2 q.1.2)
        (univ ×ˢ Icc (0 : ℝ) 1) := by
  simpa only [rootRegularizedField] using
    exists_continuous_periodicScalarFlowFamily
      (F := rootRegularizedField d c₀) (a := 0) (b := 1)
      (by norm_num) hT (contDiff_rootRegularizedField hd hc₀)
      (fun t _ p => rootRegularizedField_periodic hdperiod hc₀period t p)

end ContinuousFlexibility.Analysis
