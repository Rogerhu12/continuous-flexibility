module

public import ContinuousFlexibility.Analysis.RootFlowSymmetry
public import ContinuousFlexibility.Analysis.ScalarFlowParameterDerivative
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The actual root-parameter derivative at the zero parameters

On the radial slice x = 0 the actual regularized field is
2 ζ t² c₀(0, θ). The genuine parameter variation formula applies to
the continuous chosen family. At ζ = 0 its angular linearization
vanishes and the actual trajectory is constant. The forcing integral
therefore equals (2/3) c₀(0, θ).

No parameter differentiability of the flow is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff Topology

/-- The derivative in the independent root parameter at (0,0) follows
from the actual ODE and its continuous solution family. In applications
the required joint continuity is supplied by the periodic-flow factory. -/
theorem rootRegularizedFlow_hasDerivAt_rootParameter_zero
    {d c₀ : ℝ × ℝ → ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hc₀ : ContDiff ℝ ∞ c₀)
    (hinit : ∀ p θ, Θ p 0 θ = θ)
    (hflow : ∀ p θ t, t ∈ Icc (0 : ℝ) 1 →
      HasDerivWithinAt (fun r => Θ p r θ)
        (2 * p.1 * t * d (p.1 * t ^ 2, Θ p t θ) +
          2 * p.2 * t ^ 2 * c₀ (p.1 * t ^ 2, Θ p t θ))
        (Icc (0 : ℝ) 1) t)
    (hΘ : ContinuousOn
      (fun q : ((ℝ × ℝ) × ℝ) × ℝ => Θ q.1.1 q.2 q.1.2)
      (univ ×ˢ Icc (0 : ℝ) 1))
    (θ : ℝ) :
    HasDerivAt (fun ζ : ℝ => Θ (0, ζ) 1 θ)
      (((2 : ℝ) / 3) * c₀ (0, θ)) 0 := by
  have hslice : ContDiff ℝ ∞ (fun η : ℝ => ((0 : ℝ), η)) :=
    contDiff_const.prodMk contDiff_id
  have hc : ContDiff ℝ ∞ (fun η : ℝ => c₀ (0, η)) := hc₀.comp hslice
  let F : ℝ × (ℝ × ℝ) → ℝ :=
    fun q => 2 * q.1 * q.2.1 ^ 2 * c₀ (0, q.2.2)
  let Dθ : ℝ × (ℝ × ℝ) → ℝ :=
    fun q => 2 * q.1 * q.2.1 ^ 2 * deriv (fun η : ℝ => c₀ (0, η)) q.2.2
  let Dp : ℝ × (ℝ × ℝ) → ℝ :=
    fun q => 2 * q.2.1 ^ 2 * c₀ (0, q.2.2)
  have hcoefficient : Continuous
      (fun q : ℝ × (ℝ × ℝ) => 2 * q.1 * q.2.1 ^ 2) :=
    (continuous_const.mul continuous_fst).mul (continuous_snd.fst.pow 2)
  have hDθ : Continuous Dθ :=
    hcoefficient.mul
      ((hc.continuous_deriv (by simp)).comp continuous_snd.snd)
  have hDp : Continuous Dp :=
    (continuous_const.mul (continuous_snd.fst.pow 2)).mul
      (hc.continuous.comp continuous_snd.snd)
  have hangle (p t η : ℝ) :
      HasDerivAt (fun y => F (p, (t, y))) (Dθ (p, (t, η))) η := by
    simpa only [F, Dθ] using
      ((hc.differentiable (by simp) η).hasDerivAt.const_mul (2 * p * t ^ 2))
  have hparameter (p t η : ℝ) :
      HasDerivAt (fun q => F (q, (t, η))) (Dp (p, (t, η))) p := by
    simpa only [F, Dp, id_eq, mul_one] using
      ((((hasDerivAt_id p).const_mul (2 : ℝ)).mul_const (t ^ 2)).mul_const (c₀ (0, η)))
  have hmap : Continuous
      (fun q : ℝ × ℝ => ((((0 : ℝ), q.1), θ), q.2)) :=
    ((continuous_const.prodMk continuous_fst).prodMk continuous_const).prodMk continuous_snd
  have hfamily : ContinuousOn (fun q : ℝ × ℝ => Θ (0, q.1) q.2 θ)
      (univ ×ˢ uIcc (0 : ℝ) 1) :=
    hΘ.comp hmap.continuousOn (fun q hq =>
      ⟨mem_univ _, by simpa only [uIcc_of_le zero_le_one] using hq.2⟩)
  have htime (p t : ℝ) (ht : t ∈ uIoo (0 : ℝ) 1) :
      HasDerivAt (fun r => Θ (0, p) r θ) (F (p, (t, Θ (0, p) t θ))) t := by
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by
      simpa only [uIoo_of_le zero_le_one] using ht
    simpa only [F, mul_zero, zero_mul, zero_add] using
      (hflow (0, p) θ t ⟨ht'.1.le, ht'.2.le⟩).hasDerivAt
        (Icc_mem_nhds ht'.1 ht'.2)
  have hz := scalarFlow_hasDerivAt_parameter
    (F := F) (Dθ := Dθ) (Dp := Dp)
    (Θ := fun q : ℝ × ℝ => Θ (0, q.1) q.2 θ) (a := 0) (b := 1)
    hDθ hDp hangle hparameter hfamily (fun p => hinit (0, p) θ) htime 0
  have hIntegral :
      (∫ t in (0 : ℝ)..1, 2 * t ^ 2 * c₀ (0, Θ (0, 0) t θ)) =
        ((2 : ℝ) / 3) * c₀ (0, θ) := by
    calc
      _ = ∫ t in (0 : ℝ)..1, 2 * t ^ 2 * c₀ (0, θ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := by
          simpa only [uIcc_of_le zero_le_one] using ht
        dsimp only
        rw [rootRegularizedFlow_zero_parameters hinit hflow θ ht']
      _ = ((2 : ℝ) / 3) * c₀ (0, θ) := by
        rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
          integral_pow]
        norm_num
  apply hz.congr_deriv
  simpa only [Dθ, Dp, mul_zero, zero_mul, intervalIntegral.integral_zero,
    neg_zero, Real.exp_zero, one_mul] using hIntegral

end ContinuousFlexibility.Analysis
