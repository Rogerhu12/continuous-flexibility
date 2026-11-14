module

public import ContinuousFlexibility.Statements.Radial
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Radius and height changes on the actual radial equation

The profile pullback is `W (R * r) = H * R * w r`. The operator
identity includes its exact source factor; the negative components and
their travel integrals are preserved by the same radius change.
The germ hypotheses are local equalities of the actual profiles.
-/

@[expose] public section

namespace ContinuousFlexibility.Radial

noncomputable section

open Filter Real Set
open scoped Topology

/-- Differentiating an actual radius pullback. -/
theorem deriv_radius_pullback_of_germ {f g : ℝ → ℝ} {R a r : ℝ}
    (hR : R ≠ 0) (hf : DifferentiableAt ℝ f r)
    (hg : DifferentiableAt ℝ g (R * r))
    (heq : (fun s => g (R * s)) =ᶠ[𝓝 r] fun s => a * f s) :
    deriv g (R * r) = (a / R) * deriv f r := by
  have hc := hg.hasDerivAt.comp r (hasDerivAt_const_mul R)
  have he : deriv g (R * r) * R = a * deriv f r :=
    hc.unique ((hf.hasDerivAt.const_mul a).congr_of_eventuallyEq heq)
  calc
    _ = (a * deriv f r) / R := (eq_div_iff hR).mpr he
    _ = _ := by ring

/-- Exact Jacobi scaling, including the ordinary radial source factor. -/
theorem radialJacobi_radius_pullback {w u W U : ℝ → ℝ} {R H A a r : ℝ}
    (hR : R ≠ 0) (hr : r ≠ 0)
    (hw : DifferentiableAt ℝ w r)
    (hW : DifferentiableAt ℝ W (R * r))
    (hdu : ∀ᶠ s in 𝓝 r, DifferentiableAt ℝ u s)
    (hdU : ∀ᶠ s in 𝓝 r, DifferentiableAt ℝ U (R * s))
    (hfu : DifferentiableAt ℝ (fun s => w s * deriv u s) r)
    (hfU : DifferentiableAt ℝ (fun s => W s * deriv U s) (R * r))
    (hew : (fun s => W (R * s)) =ᶠ[𝓝 r] fun s => H * R * w s)
    (heu : (fun s => U (R * s)) =ᶠ[𝓝 r] fun s => A * u s) :
    radialJacobi a W U (R * r) = (H * A / R) * radialJacobi a w u r := by
  have hderU : (fun s => deriv U (R * s)) =ᶠ[𝓝 r]
      (fun s => (A / R) * deriv u s) := by
    filter_upwards [hdu, hdU, heu.eventuallyEq_nhds] with s hus hUs hes
    exact deriv_radius_pullback_of_germ hR hus hUs hes
  have hflux : (fun s => W (R * s) * deriv U (R * s)) =ᶠ[𝓝 r]
      (fun s => (H * A) * (w s * deriv u s)) := by
    filter_upwards [hew, hderU] with s hws hus
    rw [hws, hus]
    field_simp [hR]
    <;> ring
  have hfluxDeriv := deriv_radius_pullback_of_germ hR hfu hfU hflux
  have hprofileDeriv := deriv_radius_pullback_of_germ hR hw hW hew
  unfold radialJacobi
  rw [hfluxDeriv, hprofileDeriv, heu.eq_of_nhds]
  field_simp [hR, hr]
  <;> ring

/-- The square-root density transforms by the inverse radius factor. -/
theorem travelDensity_radius_height_change {R H r w w' : ℝ}
    (hR : 0 < R) (hH : H ≠ 0) :
    sqrt (-(H * w') / ((R * r) * (H * R * w))) =
      sqrt (-w' / (r * w)) / R := by
  have he : -(H * w') / ((R * r) * (H * R * w)) =
      (-w' / (r * w)) / R ^ 2 := by
    by_cases hr : r = 0
    · simp [hr]
    by_cases hw : w = 0
    · simp [hw]
    field_simp [hR.ne', hH, hr, hw]
    <;> ring
  rw [he, Real.sqrt_div' _ (sq_nonneg R), Real.sqrt_sq hR.le]

open ContinuousFlexibility.Statements

/-- The actual characteristic integral is preserved under radius/height scaling. -/
theorem radialTravel_radius_height_change {D E : ReferenceData} {R H l h : ℝ}
    (hR : 0 < R) (hH : H ≠ 0)
    (hw : ∀ r ∈ uIcc l h, E.w (R * r) = H * R * D.w r)
    (hdw : ∀ r ∈ uIcc l h, deriv E.w (R * r) = H * deriv D.w r) :
    radialTravel E (R * l) (R * h) = radialTravel D l h := by
  unfold radialTravel
  have hchange := intervalIntegral.smul_integral_comp_mul_left
    (a := l) (b := h) (fun r => sqrt (-deriv E.w r / (r * E.w r))) R
  simp only [smul_eq_mul] at hchange
  rw [← hchange]
  calc
    R * (∫ r in l..h, sqrt (-deriv E.w (R * r) / ((R * r) * E.w (R * r)))) =
        R * (∫ r in l..h, sqrt (-deriv D.w r / (r * D.w r)) / R) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro r hr
      dsimp only
      rw [hw r hr, hdw r hr]
      exact travelDensity_radius_height_change hR hH
    _ = R * ((∫ r in l..h, sqrt (-deriv D.w r / (r * D.w r))) / R) := by
      rw [intervalIntegral.integral_div]
    _ = _ := by field_simp [hR.ne']

/-- The endpoints and the sign of the derivative are transported together. -/
theorem negativeRadialComponent_radius_height_change
    {D E : ReferenceData} {R H l h : ℝ}
    (hR : 0 < R) (hH : 0 < H) (hneg : NegativeRadialComponent D l h)
    (ha : E.a < R * l) (hb : R * h < E.b)
    (hdw : ∀ r ∈ Icc l h, deriv E.w (R * r) = H * deriv D.w r) :
    NegativeRadialComponent E (R * l) (R * h) := by
  rcases hneg with ⟨_, hlh, _, hdl, hdh, hn⟩
  refine ⟨ha, mul_lt_mul_of_pos_left hlh hR, hb, ?_, ?_, ?_⟩
  · rw [hdw l ⟨le_rfl, hlh.le⟩, hdl, mul_zero]
  · rw [hdw h ⟨hlh.le, le_rfl⟩, hdh, mul_zero]
  · intro r hr
    have hrl : l < r / R := by
      apply (lt_div_iff₀ hR).mpr
      simpa only [mul_comm l R] using hr.1
    have hrh : r / R < h := by
      apply (div_lt_iff₀ hR).mpr
      simpa only [mul_comm h R] using hr.2
    have hcancel : R * (r / R) = r := by field_simp [hR.ne']
    have he : deriv E.w r = H * deriv D.w (r / R) := by
      simpa only [hcancel] using hdw (r / R) ⟨hrl.le, hrh.le⟩
    rw [he]
    exact mul_neg_of_pos_of_neg hH (hn (r / R) ⟨hrl, hrh⟩)

/-- The two geometric conclusions of R08 from actual profile germs. -/
theorem negativeRadialComponent_travel_of_scaled_germs
    {D E : ReferenceData} {R H l h : ℝ}
    (hR : 0 < R) (hH : 0 < H) (hneg : NegativeRadialComponent D l h)
    (ha : E.a < R * l) (hb : R * h < E.b)
    (hD : Differentiable ℝ D.w) (hE : Differentiable ℝ E.w)
    (heq : ∀ r ∈ Icc l h,
      (fun s => E.w (R * s)) =ᶠ[𝓝 r] fun s => H * R * D.w s) :
    NegativeRadialComponent E (R * l) (R * h) ∧
      radialTravel E (R * l) (R * h) = radialTravel D l h := by
  have hd : ∀ r ∈ Icc l h, deriv E.w (R * r) = H * deriv D.w r := by
    intro r hr
    calc
      _ = ((H * R) / R) * deriv D.w r :=
        deriv_radius_pullback_of_germ hR.ne' (hD r) (hE (R * r)) (heq r hr)
      _ = _ := by field_simp [hR.ne']
  refine ⟨negativeRadialComponent_radius_height_change hR hH hneg ha hb hd,
    radialTravel_radius_height_change hR hH.ne' ?_ ?_⟩
  · intro r hr
    have hr' : r ∈ Icc l h := by
      simpa only [uIcc_of_le hneg.2.1.le] using hr
    exact (heq r hr').eq_of_nhds
  · intro r hr
    apply hd r
    simpa only [uIcc_of_le hneg.2.1.le] using hr

end

end ContinuousFlexibility.Radial
