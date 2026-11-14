module

public import ContinuousFlexibility.Scalar.GreenIdentity
public import ContinuousFlexibility.Scalar.SecondProduct
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# First jets and physical conormals at a common root boundary

The two reconstructed fields are the actual functions `h * (W ∘ F)`.
Their first derivatives follow from the Frechet chain rule. The angular
chart and height jets are derived from their values on the whole boundary;
they are not additional independent data.

When the radial chart jets have opposite inward orientations, equality of
the canonical value traces and cancellation of the canonical inward
derivatives imply equality of the physical value and conormal traces.
This is a smooth interface calculation, not a closed weak-domain theorem.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The actual directional derivative of a height pullback, in the fixed
polar coordinate basis. Only differentiability at the point is used. -/
theorem n06_fderiv_height_pullback
    {F : PolarPoint → PolarPoint} {h W : PolarPoint → ℝ} {p : PolarPoint}
    (hh : DifferentiableAt ℝ h p) (hF : DifferentiableAt ℝ F p)
    (hW : DifferentiableAt ℝ W (F p)) (v : PolarPoint) :
    fderiv ℝ (fun q => h q * W (F q)) p v =
      fderiv ℝ h p v * W (F p) + h p *
        ((fderiv ℝ F p v).1 * radialPartial W (F p) +
          (fderiv ℝ F p v).2 * angularPartial W (F p)) := by
  rw [polar_directional_mul (g := fun q => W (F q)) hh (hW.comp p hF) v,
    fderiv_fun_comp p hW hF, ContinuousLinearMap.comp_apply,
    polarCLM_apply_decompose (fderiv ℝ W (F p)) (fderiv ℝ F p v)]
  rfl

/-- A scalar boundary value identity determines its actual tangential jet.
In particular, the boundary trace is differentiable without a separate
regularity assumption on its chosen scalar representative. -/
theorem n06_angularPartial_of_boundary_value
    {h : PolarPoint → ℝ} {H : ℝ → ℝ} {r θ : ℝ}
    (hh : DifferentiableAt ℝ h (r, θ))
    (hvalue : ∀ η : ℝ, h (r, η) = H η) :
    angularPartial h (r, θ) = deriv H θ := by
  have hd : HasDerivAt (fun η : ℝ => h (r, η))
      (angularPartial h (r, θ)) θ :=
    hh.hasFDerivAt.comp_hasDerivAt θ
      ((hasDerivAt_const θ r).prodMk (hasDerivAt_id θ))
  have he : (fun η : ℝ => h (r, η)) = H := funext hvalue
  rw [he] at hd
  exact hd.deriv.symm

/-- The tangential derivative of a chart whose boundary is
`(y, β θ)` is forced by that same boundary value formula. -/
theorem n06_fderiv_angular_of_boundary_value
    {F : PolarPoint → PolarPoint} {β : ℝ → ℝ} {r y θ : ℝ}
    (hF : DifferentiableAt ℝ F (r, θ))
    (hvalue : ∀ η : ℝ, F (r, η) = (y, β η)) :
    fderiv ℝ F (r, θ) (0, 1) = (0, deriv β θ) := by
  have hy : angularPartial (fun p => (F p).1) (r, θ) = 0 := by
    have he := n06_angularPartial_of_boundary_value hF.fst
      (H := fun _ => y) (fun η => congrArg Prod.fst (hvalue η))
    simpa only [deriv_const] using he
  have hβ : angularPartial (fun p => (F p).2) (r, θ) = deriv β θ :=
    n06_angularPartial_of_boundary_value hF.snd
      (fun η => congrArg Prod.snd (hvalue η))
  apply Prod.ext
  · simpa only [angularPartial, fderiv.fst hF, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst'] using hy
  · simpa only [angularPartial, fderiv.snd hF, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd'] using hβ

/-- Concrete value and radial first-jet data of one actual chart and height.
The parameter `σ` records the orientation of the canonical radial variable.
The shared functions describe the physical boundary, not freely assigned
jets of the reconstructed field. -/
structure N06RootFirstJets (F : PolarPoint → PolarPoint) (h : PolarPoint → ℝ)
    (r y σ : ℝ) (β H ρ κ Hr : ℝ → ℝ) : Prop where
  chart_differentiable : ∀ θ, DifferentiableAt ℝ F (r, θ)
  height_differentiable : ∀ θ, DifferentiableAt ℝ h (r, θ)
  chart_value : ∀ θ, F (r, θ) = (y, β θ)
  height_value : ∀ θ, h (r, θ) = H θ
  chart_radial : ∀ θ, fderiv ℝ F (r, θ) (1, 0) = (σ * ρ θ, κ θ)
  height_radial : ∀ θ, radialPartial h (r, θ) = Hr θ

namespace N06RootFirstJets

variable {F : PolarPoint → PolarPoint} {h : PolarPoint → ℝ}
  {r y σ : ℝ} {β H ρ κ Hr : ℝ → ℝ}
  (J : N06RootFirstJets F h r y σ β H ρ κ Hr)

include J

theorem chart_angular (θ : ℝ) :
    fderiv ℝ F (r, θ) (0, 1) = (0, deriv β θ) :=
  n06_fderiv_angular_of_boundary_value (J.chart_differentiable θ) J.chart_value

theorem height_angular (θ : ℝ) :
    angularPartial h (r, θ) = deriv H θ :=
  n06_angularPartial_of_boundary_value (J.height_differentiable θ) J.height_value

theorem reconstruction_value (W : PolarPoint → ℝ) (θ : ℝ) :
    h (r, θ) * W (F (r, θ)) = H θ * W (y, β θ) := by
  rw [J.height_value θ, J.chart_value θ]

/-- The radial jet contains the common height jet and the signed inward
canonical derivative. The angular drift `κ` is retained. -/
theorem reconstruction_radial {W : PolarPoint → ℝ} (θ : ℝ)
    (hW : DifferentiableAt ℝ W (y, β θ)) :
    radialPartial (fun p => h p * W (F p)) (r, θ) =
      Hr θ * W (y, β θ) + H θ *
        (σ * ρ θ * radialPartial W (y, β θ) +
          κ θ * angularPartial W (y, β θ)) := by
  have hW' : DifferentiableAt ℝ W (F (r, θ)) := by
    simpa only [J.chart_value θ] using hW
  have he := n06_fderiv_height_pullback
    (J.height_differentiable θ) (J.chart_differentiable θ) hW' (1, 0)
  change radialPartial (fun p => h p * W (F p)) (r, θ) =
    radialPartial h (r, θ) * W (F (r, θ)) + h (r, θ) *
      ((fderiv ℝ F (r, θ) (1, 0)).1 * radialPartial W (F (r, θ)) +
        (fderiv ℝ F (r, θ) (1, 0)).2 * angularPartial W (F (r, θ))) at he
  simpa only [J.height_radial θ, J.height_value θ, J.chart_value θ,
    J.chart_radial θ] using he

theorem reconstruction_angular {W : PolarPoint → ℝ} (θ : ℝ)
    (hW : DifferentiableAt ℝ W (y, β θ)) :
    angularPartial (fun p => h p * W (F p)) (r, θ) =
      deriv H θ * W (y, β θ) +
        H θ * deriv β θ * angularPartial W (y, β θ) := by
  have hW' : DifferentiableAt ℝ W (F (r, θ)) := by
    simpa only [J.chart_value θ] using hW
  have he := n06_fderiv_height_pullback
    (J.height_differentiable θ) (J.chart_differentiable θ) hW' (0, 1)
  change angularPartial (fun p => h p * W (F p)) (r, θ) =
    angularPartial h (r, θ) * W (F (r, θ)) + h (r, θ) *
      ((fderiv ℝ F (r, θ) (0, 1)).1 * radialPartial W (F (r, θ)) +
        (fderiv ℝ F (r, θ) (0, 1)).2 * angularPartial W (F (r, θ))) at he
  simpa only [J.height_angular θ, J.height_value θ, J.chart_value θ,
    J.chart_angular θ, zero_mul, zero_add, mul_assoc] using he

/-- The genuine physical conormal. Both the angular drift and the
angular derivative of the common height remain in the formula. -/
theorem reconstruction_conormal (A B : PolarPoint → ℝ)
    {W : PolarPoint → ℝ} (θ : ℝ)
    (hW : DifferentiableAt ℝ W (y, β θ)) :
    symmetricNormalFlux A B (fun p => h p * W (F p)) (r, θ) =
      (A (r, θ) * Hr θ + B (r, θ) * deriv H θ) * W (y, β θ) +
        H θ * (A (r, θ) * σ * ρ θ * radialPartial W (y, β θ) +
          (A (r, θ) * κ θ + B (r, θ) * deriv β θ) *
            angularPartial W (y, β θ)) := by
  unfold symmetricNormalFlux
  rw [J.reconstruction_radial θ hW, J.reconstruction_angular θ hW]
  ring

end N06RootFirstJets

/-- Matching canonical value traces also matches their genuine angular
derivatives; the two canonical radial boundary locations may differ. -/
theorem n06_angularPartial_eq_of_boundary_values
    {Wl Wr : PolarPoint → ℝ} {yl yr η : ℝ}
    (hl : DifferentiableAt ℝ Wl (yl, η))
    (hr : DifferentiableAt ℝ Wr (yr, η))
    (hvalue : ∀ θ : ℝ, Wl (yl, θ) = Wr (yr, θ)) :
    angularPartial Wl (yl, η) = angularPartial Wr (yr, η) := by
  exact (n06_angularPartial_of_boundary_value hl hvalue).trans
    (n06_angularPartial_of_boundary_value hr (fun _ => rfl)).symm

/-- The common actual coordinate and height jets transport matching
canonical values and oriented normal derivatives to matching physical
first jets. This formulation permits either common orientation. -/
theorem n06_root_reconstruction_firstJets_match
    {Fl Fr : PolarPoint → PolarPoint} {hl hr Wl Wr : PolarPoint → ℝ}
    {r yl yr σl σr : ℝ} {β H ρ κ Hr : ℝ → ℝ}
    (Jl : N06RootFirstJets Fl hl r yl σl β H ρ κ Hr)
    (Jr : N06RootFirstJets Fr hr r yr σr β H ρ κ Hr)
    (hWl : ∀ η, DifferentiableAt ℝ Wl (yl, η))
    (hWr : ∀ η, DifferentiableAt ℝ Wr (yr, η))
    (hvalue : ∀ η, Wl (yl, η) = Wr (yr, η))
    (hnormal : ∀ η,
      σl * radialPartial Wl (yl, η) = σr * radialPartial Wr (yr, η))
    (θ : ℝ) :
    hl (r, θ) * Wl (Fl (r, θ)) = hr (r, θ) * Wr (Fr (r, θ)) ∧
      radialPartial (fun p => hl p * Wl (Fl p)) (r, θ) =
        radialPartial (fun p => hr p * Wr (Fr p)) (r, θ) ∧
      angularPartial (fun p => hl p * Wl (Fl p)) (r, θ) =
        angularPartial (fun p => hr p * Wr (Fr p)) (r, θ) := by
  have ht := n06_angularPartial_eq_of_boundary_values
    (hWl (β θ)) (hWr (β θ)) hvalue
  have hn : σl * ρ θ * radialPartial Wl (yl, β θ) =
      σr * ρ θ * radialPartial Wr (yr, β θ) := by
    calc
      _ = ρ θ * (σl * radialPartial Wl (yl, β θ)) := by ring
      _ = ρ θ * (σr * radialPartial Wr (yr, β θ)) := by rw [hnormal (β θ)]
      _ = _ := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [Jl.reconstruction_value Wl θ, Jr.reconstruction_value Wr θ, hvalue (β θ)]
  · rw [Jl.reconstruction_radial θ (hWl (β θ)),
      Jr.reconstruction_radial θ (hWr (β θ)), hvalue (β θ), ht, hn]
  · rw [Jl.reconstruction_angular θ (hWl (β θ)),
      Jr.reconstruction_angular θ (hWr (β θ)), hvalue (β θ), ht]

/-- Opposite inward orientations turn the sum-zero canonical normal
condition into equality of the actual physical value and conormal.
No ellipticity or division by a coefficient is needed for this direction. -/
theorem n06_root_inward_value_conormal
    (A B : PolarPoint → ℝ)
    {Fl Fr : PolarPoint → PolarPoint} {hl hr Wl Wr : PolarPoint → ℝ}
    {r yl yr σ : ℝ} {β H ρ κ Hr : ℝ → ℝ}
    (Jl : N06RootFirstJets Fl hl r yl σ β H ρ κ Hr)
    (Jr : N06RootFirstJets Fr hr r yr (-σ) β H ρ κ Hr)
    (hWl : ∀ η, DifferentiableAt ℝ Wl (yl, η))
    (hWr : ∀ η, DifferentiableAt ℝ Wr (yr, η))
    (hvalue : ∀ η, Wl (yl, η) = Wr (yr, η))
    (hnormal : ∀ η, radialPartial Wl (yl, η) + radialPartial Wr (yr, η) = 0)
    (θ : ℝ) :
    hl (r, θ) * Wl (Fl (r, θ)) = hr (r, θ) * Wr (Fr (r, θ)) ∧
      symmetricNormalFlux A B (fun p => hl p * Wl (Fl p)) (r, θ) =
        symmetricNormalFlux A B (fun p => hr p * Wr (Fr p)) (r, θ) := by
  have hn (η : ℝ) : σ * radialPartial Wl (yl, η) =
      (-σ) * radialPartial Wr (yr, η) := by
    have he : radialPartial Wl (yl, η) = -radialPartial Wr (yr, η) :=
      add_eq_zero_iff_eq_neg.mp (hnormal η)
    rw [he]
    ring
  have hj := n06_root_reconstruction_firstJets_match Jl Jr hWl hWr hvalue hn θ
  exact ⟨hj.1, by simp only [symmetricNormalFlux, hj.2.1, hj.2.2]⟩

/-- The same value/conormal identities cancel the actual Green boundary
term against every common physical test function. -/
theorem n06_greenNormalFlux_eq_of_value_conormal
    {A B ul ur : PolarPoint → ℝ} {p : PolarPoint}
    (hvalue : ul p = ur p)
    (hflux : symmetricNormalFlux A B ul p = symmetricNormalFlux A B ur p)
    (φ : PolarPoint → ℝ) :
    greenNormalFlux A B φ ul p = greenNormalFlux A B φ ur p := by
  simp only [greenNormalFlux, hvalue, hflux]

end ContinuousFlexibility.Analysis
