module

public import ContinuousFlexibility.Radial.TailEdgePerturbedGreen
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Resistance coordinate on a positive edge

The chart is the actual integral of the reciprocal density. Its inverse
gives the transformed mass density, and the flux identity yields the
actual forced equation in resistance coordinates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory

def tailResistanceChart (p : ℝ → ℝ) (a x : ℝ) : ℝ := ∫ t in a..x, (p t)⁻¹

def tailResistanceInverse (p : ℝ → ℝ) (a : ℝ) : ℝ → ℝ :=
  Function.invFun (tailResistanceChart p a)

def tailResistanceDensity (p : ℝ → ℝ) (a s : ℝ) : ℝ :=
  p (tailResistanceInverse p a s) ^ 2

theorem hasDerivAt_tailResistanceChart {p : ℝ → ℝ} (hp : Continuous p)
    (hpos : ∀ x, 0 < p x) (a x : ℝ) :
    HasDerivAt (tailResistanceChart p a) (p x)⁻¹ x := by
  have hi : Continuous (fun t => (p t)⁻¹) := hp.inv₀ (fun t => (hpos t).ne')
  exact intervalIntegral.integral_hasDerivAt_right (hi.intervalIntegrable a x)
    hi.aestronglyMeasurable.stronglyMeasurableAtFilter hi.continuousAt

theorem tailResistanceChart_strictMono {p : ℝ → ℝ} (hp : Continuous p)
    (hpos : ∀ x, 0 < p x) (a : ℝ) : StrictMono (tailResistanceChart p a) := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(hasDerivAt_tailResistanceChart hp hpos a x).deriv]
  exact inv_pos.mpr (hpos x)

theorem tailResistanceInverse_chart {p : ℝ → ℝ} (hp : Continuous p)
    (hpos : ∀ x, 0 < p x) (a x : ℝ) :
    tailResistanceInverse p a (tailResistanceChart p a x) = x :=
  Function.leftInverse_invFun (tailResistanceChart_strictMono hp hpos a).injective x

theorem tailResistanceInverse_continuousOn {p : ℝ → ℝ} (hp : Continuous p)
    (hpos : ∀ x, 0 < p x) (a : ℝ) :
    ContinuousOn (tailResistanceInverse p a) (range (tailResistanceChart p a)) := by
  have hC : ContDiff ℝ 1 (tailResistanceChart p a) := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun x => (hasDerivAt_tailResistanceChart hp hpos a x).differentiableAt, ?_⟩
    rw [show deriv (tailResistanceChart p a) = (fun x => (p x)⁻¹) from
      funext fun x => (hasDerivAt_tailResistanceChart hp hpos a x).deriv]
    exact hp.inv₀ (fun x => (hpos x).ne')
  have hOpen : IsOpenMap (tailResistanceChart p a) :=
    isOpenMap_of_hasStrictDerivAt (fun x => hC.hasStrictDerivAt (x := x) (by norm_num))
      (fun x => by rw [(hasDerivAt_tailResistanceChart hp hpos a x).deriv]
                   exact (inv_pos.mpr (hpos x)).ne')
  exact hOpen.continuousOn_range_of_leftInverse (tailResistanceInverse_chart hp hpos a)

/-- Integration with the actual transformed density is integration with
the original mass density in the original coordinate. -/
theorem tailResistance_mass_change {p V : ℝ → ℝ} (hp : Continuous p)
    (hpos : ∀ x, 0 < p x) (hV : Continuous V) (a l r : ℝ) :
    (∫ s in tailResistanceChart p a l..tailResistanceChart p a r,
      tailResistanceDensity p a s * V s) =
      ∫ x in l..r, p x * V (tailResistanceChart p a x) := by
  have hi : Continuous (fun x => (p x)⁻¹) := hp.inv₀ (fun x => (hpos x).ne')
  have hW : ContinuousOn (fun s => tailResistanceDensity p a s * V s)
      (range (tailResistanceChart p a)) :=
    ((hp.comp_continuousOn (tailResistanceInverse_continuousOn hp hpos a)).pow 2).mul
      hV.continuousOn
  have hs := intervalIntegral.integral_comp_mul_deriv'
    (a := l) (b := r) (f := tailResistanceChart p a) (f' := fun x => (p x)⁻¹)
    (fun x _ => hasDerivAt_tailResistanceChart hp hpos a x) hi.continuousOn
    (hW.mono (image_subset_range _ _))
  rw [← hs]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only [Function.comp_apply, tailResistanceDensity]
  rw [tailResistanceInverse_chart hp hpos]
  field_simp [(hpos x).ne']

/-- The actual radial flux is the derivative in resistance coordinates. -/
theorem tailResistance_flux {p V : ℝ → ℝ} (hp : Continuous p)
    (hpos : ∀ x, 0 < p x) (hV : Differentiable ℝ V) (a : ℝ) :
    (fun x => p x * deriv (V ∘ tailResistanceChart p a) x) =
      deriv V ∘ tailResistanceChart p a := by
  funext x
  rw [((hV (tailResistanceChart p a x)).hasDerivAt.comp x
    (hasDerivAt_tailResistanceChart hp hpos a x)).deriv]
  simp only [Function.comp_apply]
  field_simp [(hpos x).ne']

/-- Exact inhomogeneous operator identity after the resistance change. -/
theorem tailResistance_equation {p V f : ℝ → ℝ} (hp : Continuous p)
    (hpos : ∀ x, 0 < p x) (hV : Differentiable ℝ V) (a Λ x : ℝ)
    (hV₂ : DifferentiableAt ℝ (deriv V) (tailResistanceChart p a x)) :
    -deriv (fun y => p y * deriv (V ∘ tailResistanceChart p a) y) x / p x -
        Λ * (V ∘ tailResistanceChart p a) x = f x ↔
      -deriv (deriv V) (tailResistanceChart p a x) -
        Λ * tailResistanceDensity p a (tailResistanceChart p a x) *
          V (tailResistanceChart p a x) = tailResistanceDensity p a (tailResistanceChart p a x) * f x := by
  rw [tailResistance_flux hp hpos hV,
    (hV₂.hasDerivAt.comp x (hasDerivAt_tailResistanceChart hp hpos a x)).deriv]
  simp only [Function.comp_apply, tailResistanceDensity, tailResistanceInverse_chart hp hpos]
  have he : -(deriv (deriv V) (tailResistanceChart p a x) * (p x)⁻¹) / p x -
      Λ * V (tailResistanceChart p a x) =
        (-deriv (deriv V) (tailResistanceChart p a x) -
          Λ * p x ^ 2 * V (tailResistanceChart p a x)) / p x ^ 2 := by
    field_simp [(hpos x).ne']
  rw [he, div_eq_iff (pow_ne_zero 2 (hpos x).ne'), mul_comm (f x)]

end ContinuousFlexibility.Radial
