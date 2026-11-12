import ContinuousFlexibility.Analysis.N06RootTransmissionJets
import ContinuousFlexibility.Scalar.FormPullback

/-!
# Root transmission inherited from one reference physical field

The reference angular coordinate is the physical angle. Two actual
reference reconstructions which have the germ of one physical field
therefore have the same canonical value and oriented normal traces.
Nonvanishing of the height and actual chart Jacobian justifies cancellation.
The common current root jets then transport those same traces to matching
physical values and conormals. No canonical matching condition is an input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open scoped Topology ContDiff

theorem N06RootFirstJets.jacobian
    {F : PolarPoint → PolarPoint} {h : PolarPoint → ℝ}
    {r y σ : ℝ} {β H ρ κ Hr : ℝ → ℝ}
    (J : N06RootFirstJets F h r y σ β H ρ κ Hr) (θ : ℝ) :
    planeJacobian F (r, θ) = σ * ρ θ * deriv β θ := by
  unfold planeJacobian
  rw [J.chart_radial θ, J.chart_angular θ]
  simp only [mul_zero, sub_zero]

/-- At reference angle identity, the nonzero actual Jacobian supplies the
nonzero radial scale needed to recover the canonical normal trace. -/
theorem N06RootFirstJets.reference_scale_ne_zero
    {F : PolarPoint → PolarPoint} {h : PolarPoint → ℝ}
    {r y σ : ℝ} {H ρ κ Hr : ℝ → ℝ}
    (J : N06RootFirstJets F h r y σ (fun θ => θ) H ρ κ Hr)
    {θ : ℝ} (hJ : planeJacobian F (r, θ) ≠ 0) : ρ θ ≠ 0 := by
  intro hzero
  apply hJ
  rw [J.jacobian θ, hzero, mul_zero, zero_mul]

/-- Equality of the actual physical value and radial derivative forces
the canonical value and oriented normal traces to coincide. -/
theorem n06_reference_root_canonical_traces_of_firstJets
    {Fl Fr : PolarPoint → PolarPoint} {hl hr Wl Wr : PolarPoint → ℝ}
    {r yl yr σl σr : ℝ} {H ρ κ Hr : ℝ → ℝ}
    (Jl : N06RootFirstJets Fl hl r yl σl (fun θ => θ) H ρ κ Hr)
    (Jr : N06RootFirstJets Fr hr r yr σr (fun θ => θ) H ρ κ Hr)
    (hH : ∀ θ, H θ ≠ 0)
    (hJac : ∀ θ, planeJacobian Fl (r, θ) ≠ 0)
    (hWl : ∀ θ, DifferentiableAt ℝ Wl (yl, θ))
    (hWr : ∀ θ, DifferentiableAt ℝ Wr (yr, θ))
    (hphysical : ∀ θ, hl (r, θ) * Wl (Fl (r, θ)) = hr (r, θ) * Wr (Fr (r, θ)))
    (hradial : ∀ θ, radialPartial (fun p => hl p * Wl (Fl p)) (r, θ) =
      radialPartial (fun p => hr p * Wr (Fr p)) (r, θ)) :
    (∀ θ, Wl (yl, θ) = Wr (yr, θ)) ∧
      ∀ θ, σl * radialPartial Wl (yl, θ) = σr * radialPartial Wr (yr, θ) := by
  have hvalue (θ : ℝ) : Wl (yl, θ) = Wr (yr, θ) := by
    apply mul_left_cancel₀ (hH θ)
    calc
      H θ * Wl (yl, θ) = hl (r, θ) * Wl (Fl (r, θ)) :=
        (Jl.reconstruction_value Wl θ).symm
      _ = hr (r, θ) * Wr (Fr (r, θ)) := hphysical θ
      _ = H θ * Wr (yr, θ) := Jr.reconstruction_value Wr θ
  refine ⟨hvalue, ?_⟩
  intro θ
  have hrad := hradial θ
  have hangular := n06_angularPartial_eq_of_boundary_values
    (hWl θ) (hWr θ) hvalue
  rw [Jl.reconstruction_radial θ (hWl θ), Jr.reconstruction_radial θ (hWr θ)] at hrad
  change Hr θ * Wl (yl, θ) + H θ *
      (σl * ρ θ * radialPartial Wl (yl, θ) + κ θ * angularPartial Wl (yl, θ)) =
    Hr θ * Wr (yr, θ) + H θ *
      (σr * ρ θ * radialPartial Wr (yr, θ) + κ θ * angularPartial Wr (yr, θ)) at hrad
  rw [hvalue θ, hangular] at hrad
  apply mul_left_cancel₀ (mul_ne_zero (hH θ) (Jl.reference_scale_ne_zero (hJac θ)))
  change (H θ * ρ θ) * (σl * radialPartial Wl (yl, θ)) =
    (H θ * ρ θ) * (σr * radialPartial Wr (yr, θ))
  linear_combination hrad

/-- Actual reconstructions with one common physical germ determine the
canonical traces without separate trace-matching assumptions. -/
theorem n06_reference_root_canonical_traces
    {Fl Fr : PolarPoint → PolarPoint} {hl hr Wl Wr η : PolarPoint → ℝ}
    {r yl yr σl σr : ℝ} {H ρ κ Hr : ℝ → ℝ}
    (Jl : N06RootFirstJets Fl hl r yl σl (fun θ => θ) H ρ κ Hr)
    (Jr : N06RootFirstJets Fr hr r yr σr (fun θ => θ) H ρ κ Hr)
    (hH : ∀ θ, H θ ≠ 0)
    (hJac : ∀ θ, planeJacobian Fl (r, θ) ≠ 0)
    (hWl : ∀ θ, DifferentiableAt ℝ Wl (yl, θ))
    (hWr : ∀ θ, DifferentiableAt ℝ Wr (yr, θ))
    (hleft : ∀ θ, (fun p => hl p * Wl (Fl p)) =ᶠ[𝓝 (r, θ)] η)
    (hright : ∀ θ, (fun p => hr p * Wr (Fr p)) =ᶠ[𝓝 (r, θ)] η) :
    (∀ θ, Wl (yl, θ) = Wr (yr, θ)) ∧
      ∀ θ, σl * radialPartial Wl (yl, θ) = σr * radialPartial Wr (yr, θ) := by
  apply n06_reference_root_canonical_traces_of_firstJets Jl Jr hH hJac hWl hWr
  · intro θ
    exact (hleft θ).eq_of_nhds.trans (hright θ).eq_of_nhds.symm
  · intro θ
    exact congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (1, 0))
      (((hleft θ).fderiv_eq (𝕜 := ℝ)).trans ((hright θ).fderiv_eq (𝕜 := ℝ)).symm)

/-- One actual reference physical field gives the common current value
and conormal, after only the actual shared root chart/height jets. -/
theorem n06_root_transmission_from_reference_field
    (A B : PolarPoint → ℝ)
    {Fl₀ Fr₀ Fl Fr : PolarPoint → PolarPoint}
    {hl₀ hr₀ hl hr Wl Wr η : PolarPoint → ℝ}
    {r yl yr σl σr : ℝ}
    {H₀ ρ₀ κ₀ Hr₀ β H ρ κ Hr : ℝ → ℝ}
    (Jl₀ : N06RootFirstJets Fl₀ hl₀ r yl σl (fun θ => θ) H₀ ρ₀ κ₀ Hr₀)
    (Jr₀ : N06RootFirstJets Fr₀ hr₀ r yr σr (fun θ => θ) H₀ ρ₀ κ₀ Hr₀)
    (Jl : N06RootFirstJets Fl hl r yl σl β H ρ κ Hr)
    (Jr : N06RootFirstJets Fr hr r yr σr β H ρ κ Hr)
    (hH : ∀ θ, H₀ θ ≠ 0)
    (hJac : ∀ θ, planeJacobian Fl₀ (r, θ) ≠ 0)
    (hWl : ∀ θ, DifferentiableAt ℝ Wl (yl, θ))
    (hWr : ∀ θ, DifferentiableAt ℝ Wr (yr, θ))
    (hleft : ∀ θ, (fun p => hl₀ p * Wl (Fl₀ p)) =ᶠ[𝓝 (r, θ)] η)
    (hright : ∀ θ, (fun p => hr₀ p * Wr (Fr₀ p)) =ᶠ[𝓝 (r, θ)] η)
    (θ : ℝ) :
    hl (r, θ) * Wl (Fl (r, θ)) = hr (r, θ) * Wr (Fr (r, θ)) ∧
      symmetricNormalFlux A B (fun p => hl p * Wl (Fl p)) (r, θ) =
        symmetricNormalFlux A B (fun p => hr p * Wr (Fr p)) (r, θ) := by
  have htraces := n06_reference_root_canonical_traces Jl₀ Jr₀ hH hJac
    hWl hWr hleft hright
  have hmatch := n06_root_reconstruction_firstJets_match Jl Jr hWl hWr
    htraces.1 htraces.2 θ
  exact ⟨hmatch.1, by simp only [symmetricNormalFlux, hmatch.2.1, hmatch.2.2]⟩

end ContinuousFlexibility.Analysis
