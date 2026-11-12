import ContinuousFlexibility.Analysis.NeighborhoodCharacteristicSpeed
import ContinuousFlexibility.Analysis.OneHighCircleFlowLocalization
import ContinuousFlexibility.Analysis.ScalarSpatialRegularity

/-!
# All actual angular jets of the original characteristic speed

The existing corrected-determinant identity separates a merely continuous
radial square root from two genuinely smooth angular factors. One fixed
smooth radial clamp makes those factors globally smooth without changing
the speed anywhere on the original closed strip.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem polarAngularRegularity_continuousRadialFactor
    {w τ : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hτ : Continuous τ)
    (hτpos : ∀ t : ℝ, 0 < τ t) :
    Continuous (fun t => Real.sqrt (-w (τ t) * deriv w (τ t) / τ t)) := by
  have hw' : Continuous (deriv w) := (contDiff_infty_iff_deriv.mp hw).2.continuous
  exact (((hw.continuous.comp hτ).neg.mul (hw'.comp hτ)).div
    hτ (fun t => (hτpos t).ne')).sqrt

private theorem polarAngularRegularity_separated
    {F d c : PolarPoint → ℝ} {R : ℝ → ℝ}
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c) (hR : Continuous R)
    (he : F = fun p : PolarPoint => d p - R p.2 * c p) :
    ∀ n : ℕ, ScalarSpatialRegularity n F := by
  intro n
  rw [he]
  simpa only [sub_eq_add_neg] using
    (scalarSpatialRegularity_of_contDiff hd n).add
      (((ScalarSpatialRegularity.timeOnly hR n).mul
        (scalarSpatialRegularity_of_contDiff hc n)).neg)

/-- A genuine extension of the actual original speed, with spatial
coordinates first. No sign condition on `deriv w` is required. -/
theorem exists_spatiallyRegular_polarMinusCharacteristicSpeed
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {l u ρ P : ℝ}
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z)
    (hlu : l ≤ u) (hρ : 0 < ρ) (hl : 0 < l - ρ)
    (hadm : ∀ p ∈ Ioo (l - ρ) (u + ρ) ×ˢ (univ : Set ℝ),
      0 < polarDiscriminant w z p ∧
      heightQ (profileEnergy w p) (heightRadial z p)
        (angularPartial (heightAngular z) p) ≠ 0)
    (hperiod : Function.Periodic z (0, P)) :
    ∃ F : PolarPoint → ℝ, (∀ n : ℕ, ScalarSpatialRegularity n F) ∧
      (∀ t : ℝ, Function.Periodic (fun x => F (x, t)) P) ∧
      ∀ t ∈ Icc l u, ∀ x : ℝ,
        F (x, t) = minusCharacteristicSpeed
          ⟨polarLinearA w z, polarLinearB w z, polarCorrectedC w z⟩ (t, x) := by
  let τ : ℝ → ℝ := circleFlowSmoothTimeClamp l u ρ hlu hρ
  have hτ : ContDiff ℝ ∞ τ := contDiff_circleFlowSmoothTimeClamp hlu hρ
  have hτmem (t : ℝ) : τ t ∈ Ioo (l - ρ) (u + ρ) :=
    circleFlowSmoothTimeClamp_mem hlu hρ t
  have hτpos (t : ℝ) : 0 < τ t := hl.trans (hτmem t).1
  let drift : PolarPoint → ℝ := fun p => polarLinearB w z p / polarLinearA w z p
  let factor : PolarPoint → ℝ := fun p =>
    (polarDiscriminant w z p * polarLinearA w z p)⁻¹
  have hlocal (p : PolarPoint)
      (hp : p ∈ Ioo (l - ρ) (u + ρ) ×ˢ (univ : Set ℝ)) :
      ContDiffAt ℝ ∞ drift p ∧ ContDiffAt ℝ ∞ factor p :=
    contDiffAt_characteristicAngularFactors (w := w) (z := z) (p := p)
      hw.contDiffAt hz.contDiffAt
      (hl.trans hp.1.1).ne' (hadm p hp).1 (hadm p hp).2
  let d : PolarPoint → ℝ := fun p => drift (τ p.2, p.1)
  let c : PolarPoint → ℝ := fun p => factor (τ p.2, p.1)
  have hd : ContDiff ℝ ∞ d :=
    (contDiff_circleFlowLocalizedSpeed (G := drift) hlu hρ
      (fun p hp => (hlocal p hp).1.contDiffWithinAt)).comp
        (contDiff_snd.prodMk contDiff_fst)
  have hc : ContDiff ℝ ∞ c :=
    (contDiff_circleFlowLocalizedSpeed (G := factor) hlu hρ
      (fun p hp => (hlocal p hp).2.contDiffWithinAt)).comp
        (contDiff_snd.prodMk contDiff_fst)
  let R : ℝ → ℝ := fun t => Real.sqrt (-w (τ t) * deriv w (τ t) / τ t)
  have hR : Continuous R :=
    polarAngularRegularity_continuousRadialFactor (w := w) (τ := τ)
      hw hτ.continuous hτpos
  let F : PolarPoint → ℝ := fun p => minusCharacteristicSpeed
    ⟨polarLinearA w z, polarLinearB w z, polarCorrectedC w z⟩ (τ p.2, p.1)
  have he : F = fun p : PolarPoint => d p - R p.2 * c p := by
    funext p
    have hp : (τ p.2, p.1) ∈ Ioo (l - ρ) (u + ρ) ×ˢ (univ : Set ℝ) :=
      ⟨hτmem p.2, mem_univ p.1⟩
    exact polarMinusCharacteristicSpeed_eq_separated (w := w) (p := (τ p.2, p.1)) z
      (hw.differentiable (by simp) (τ p.2)) (hτpos p.2).ne'
      (hadm (τ p.2, p.1) hp).1 (hadm (τ p.2, p.1) hp).2
  refine ⟨F, polarAngularRegularity_separated
    (F := F) (d := d) (c := c) (R := R) hd hc hR he, ?_, ?_⟩
  · intro t x
    have hp := polarMinusCharacteristicSpeed_periodic w hperiod (τ t, x)
    change minusCharacteristicSpeed
      ⟨polarLinearA w z, polarLinearB w z, polarCorrectedC w z⟩ (τ t, x + P) = _
    simpa only [Prod.mk_add_mk, add_zero] using hp
  · intro t ht x
    change minusCharacteristicSpeed
      ⟨polarLinearA w z, polarLinearB w z, polarCorrectedC w z⟩ (τ t, x) = _
    rw [show τ t = t from circleFlowSmoothTimeClamp_eq hlu hρ ht]

end ContinuousFlexibility.Analysis
