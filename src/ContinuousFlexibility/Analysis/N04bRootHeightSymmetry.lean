module

public import ContinuousFlexibility.Analysis.N04bActualRootHeightCollar
public import ContinuousFlexibility.Scalar.Conservation

/-!
# Actual angular symmetries of the root height

The parity of actual first derivatives follows from the ordinary chain
rule on radial and angular slices. It gives the even Jacobian of the
reflected chart and the even angular-product denominator. The genuine
root height is therefore periodic and even whenever the actual leading
coefficient is, as supplied by N03 and raw field regularity.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The true partial derivatives of a reflected scalar field. -/
theorem n04b_polar_partials_reflection
    {f : PolarPoint → ℝ} {e r θ : ℝ}
    (hparity : ∀ x η, f (x, -η) = e * f (x, η))
    (hf : DifferentiableAt ℝ f (r, θ))
    (hfr : DifferentiableAt ℝ f (r, -θ)) :
    radialPartial f (r, -θ) = e * radialPartial f (r, θ) ∧
      angularPartial f (r, -θ) = -e * angularPartial f (r, θ) := by
  constructor
  · have he : (fun x => f (x, -θ)) = (fun x => e * f (x, θ)) :=
      funext fun x => hparity x θ
    have hd := (hasDerivAt_radial_slice hf).const_mul e
    rw [← he] at hd
    exact (hasDerivAt_radial_slice hfr).unique hd
  · have he : (fun η => f (r, -η)) = (fun η => e * f (r, η)) :=
      funext fun η => hparity r η
    have hd : HasDerivAt (fun η => f (r, -η))
        (-angularPartial f (r, -θ)) θ := by
      simpa only [Function.comp_def, mul_neg_one] using
        (hasDerivAt_angular_slice hfr).comp θ (hasDerivAt_neg θ)
    rw [he] at hd
    have hh := hd.unique ((hasDerivAt_angular_slice hf).const_mul e)
    linarith

theorem n04b_planeJacobian_eq_componentPartials
    {F : PolarPoint → PolarPoint} {p : PolarPoint}
    (hF : DifferentiableAt ℝ F p) :
    planeJacobian F p =
      radialPartial (fun q => (F q).1) p * angularPartial (fun q => (F q).2) p -
        radialPartial (fun q => (F q).2) p * angularPartial (fun q => (F q).1) p := by
  unfold planeJacobian radialPartial angularPartial
  rw [(hF.hasFDerivAt.fst).fderiv, (hF.hasFDerivAt.snd).fderiv]
  rfl

/-- A true reflected coordinate map has an even ordinary Jacobian at
every pair of differentiability points. -/
theorem n04b_planeJacobian_reflection
    {F : PolarPoint → PolarPoint} {r θ : ℝ}
    (hreflection : ∀ x η, F (x, -η) = ((F (x, η)).1, -(F (x, η)).2))
    (hF : DifferentiableAt ℝ F (r, θ))
    (hFr : DifferentiableAt ℝ F (r, -θ)) :
    planeJacobian F (r, -θ) = planeJacobian F (r, θ) := by
  have hfirst : ∀ x η, (F (x, -η)).1 = (1 : ℝ) * (F (x, η)).1 := by
    intro x η
    simpa only [one_mul] using congrArg Prod.fst (hreflection x η)
  have hsecond : ∀ x η, (F (x, -η)).2 = (-1 : ℝ) * (F (x, η)).2 := by
    intro x η
    simpa only [neg_one_mul] using congrArg Prod.snd (hreflection x η)
  have hf := n04b_polar_partials_reflection hfirst hF.fst hFr.fst
  have hs := n04b_polar_partials_reflection hsecond hF.snd hFr.snd
  rw [n04b_planeJacobian_eq_componentPartials hFr,
    n04b_planeJacobian_eq_componentPartials hF, hf.1, hf.2, hs.1, hs.2]
  ring

namespace N04bRootCoordinateProperties

variable {d c₀ : PolarPoint → ℝ} {hL : ℝ → ℝ} {Φ : ℝ → ℝ → ℝ}
  {R σ : ℝ} {G : ℝ × ℝ × ℝ → ℝ}
  (H : N04bRootCoordinateProperties d c₀ hL Φ R σ G)

include H

theorem angularProduct_reflection (r θ : ℝ) :
    rootAngularProduct G (r, -θ) = rootAngularProduct G (r, θ) := by
  have hφ : ContDiff ℝ ∞ (extendedRootEven G) :=
    contDiff_extendedRootEven H.smooth Real.pi_ne_zero (fun r _ => H.even_period r)
  have hχ : ContDiff ℝ ∞ (extendedRootOddCoefficient G) :=
    contDiff_extendedRootOddCoefficient H.smooth Real.pi_ne_zero (fun r _ => H.odd_period r)
  have hφodd : ∀ x η, extendedRootEven G (x, -η) =
      (-1 : ℝ) * extendedRootEven G (x, η) := by
    intro x η
    simpa only [neg_one_mul] using extendedRootEven_reflect
      (fun r _ => rootEven_reflect H.reflection r) x η
  have hχeven : ∀ x η, extendedRootOddCoefficient G (x, -η) =
      (1 : ℝ) * extendedRootOddCoefficient G (x, η) := by
    intro x η
    simpa only [one_mul] using extendedRootOddCoefficient_reflect
      (fun r _ => rootOddCoefficient_reflect H.smooth H.reflection r) x η
  have hp := n04b_polar_partials_reflection hφodd
    (hφ.differentiable (by simp) (r, θ)) (hφ.differentiable (by simp) (r, -θ))
  have hc := n04b_polar_partials_reflection hχeven
    (hχ.differentiable (by simp) (r, θ)) (hχ.differentiable (by simp) (r, -θ))
  simp only [rootAngularProduct, hp.2, hc.2]
  ring

theorem height_period {a : PolarPoint → ℝ} {r : ℝ}
    (ha : Function.Periodic (fun θ => a (r, θ)) Real.pi) :
    Function.Periodic (fun θ => rootSmoothHeight a G (r, θ)) Real.pi := by
  intro θ
  simp only [rootSmoothHeight, rootHeightFactor, ha θ,
    planeJacobian_periodic_snd H.extended_chart_period r θ, H.angularProduct_period r θ]

theorem height_reflection {a : PolarPoint → ℝ} {r θ : ℝ}
    (ha : a (r, -θ) = a (r, θ))
    (hF : DifferentiableAt ℝ (extendedRootEvenOddChart G) (r, θ))
    (hFr : DifferentiableAt ℝ (extendedRootEvenOddChart G) (r, -θ)) :
    rootSmoothHeight a G (r, -θ) = rootSmoothHeight a G (r, θ) := by
  simp only [rootSmoothHeight, rootHeightFactor, ha,
    n04b_planeJacobian_reflection H.extended_chart_reflection hF hFr,
    H.angularProduct_reflection r θ]

end N04bRootCoordinateProperties

/-- The actual raw coefficient supplies the root height's period on
every oriented radial slice remaining inside the physical annulus. -/
theorem n04b_actual_root_height_period
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {base : ℕ} {ε : ℝ}
    (hfield : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {r₀ ι r : ℝ} (hr : r₀ + ι * r ∈ Ioo D.a D.b)
    {d c₀ : PolarPoint → ℝ} {hL : ℝ → ℝ} {Φ : ℝ → ℝ → ℝ}
    {R σ : ℝ} {G : ℝ × ℝ × ℝ → ℝ}
    (H : N04bRootCoordinateProperties d c₀ hL Φ R σ G) :
    Function.Periodic
      (fun θ => rootSmoothHeight (n04bRootLeadingCoefficient L z r₀ ι) G (r, θ)) Real.pi :=
  H.height_period (hfield.periodic_coefficients z hz hs (r₀ + ι * r) hr).1

/-- N03 supplies evenness of the actual root height throughout its
genuinely smooth two-sided chart collar. -/
theorem n04b_actual_root_height_reflection
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R₀ : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (h03 : NonlinearPropertiesThrough03 D T S C R₀ L base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {r₀ ι r θ : ℝ}
    {d c₀ : PolarPoint → ℝ} {hL : ℝ → ℝ} {Φ : ℝ → ℝ → ℝ}
    {R σ : ℝ} {G : ℝ × ℝ × ℝ → ℝ}
    (H : N04bRootCoordinateProperties d c₀ hL Φ R σ G)
    (hF : DifferentiableAt ℝ (extendedRootEvenOddChart G) (r, θ))
    (hFr : DifferentiableAt ℝ (extendedRootEvenOddChart G) (r, -θ)) :
    rootSmoothHeight (n04bRootLeadingCoefficient L z r₀ ι) G (r, -θ) =
      rootSmoothHeight (n04bRootLeadingCoefficient L z r₀ ι) G (r, θ) :=
  H.height_reflection (h03.2.2.2.2.1 z hz hs (r₀ + ι * r) θ).1 hF hFr

end ContinuousFlexibility.Analysis
