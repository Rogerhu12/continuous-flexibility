module

public import ContinuousFlexibility.Radial.Gauge
public import Mathlib.Analysis.Real.Sqrt

/-!
# Liouville transformation of the actual radial operator

This is the differential identity in Section 4, `eq:rad-eq-sc0`.
The positive density is represented as `P = s²`; in the manuscript
`s = sqrt P`. Identities between functions are required on a neighborhood,
not merely at one point, so that they can genuinely be differentiated.
No spectral statement or radius-existence statement is assumed or proved here.
-/

@[expose] public section

namespace ContinuousFlexibility.Radial

noncomputable section

open Filter
open scoped Topology

/-- The geometric spectral coefficient, with `P = s²`. -/
def liouvilleRho (R s : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(deriv (deriv R) x + (2 * deriv s x / s x) * deriv R x) / R x

/-- The density potential `(sqrt P)'' / sqrt P`. -/
def liouvilleV0 (s : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv s) x / s x

/-- The Schrödinger expression before multiplication by the radius factor. -/
def liouvilleSchrodinger (a : ℝ) (R s ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  -deriv (deriv ψ) x + (liouvilleV0 s x - a * liouvilleRho R s x) * ψ x

/-- Differentiating the pulled-back height gives the exact radial flux.
The identities are about actual functions and actual derivatives. -/
theorem liouville_flux_at {c x : ℝ} {R s ψ w u : ℝ → ℝ}
    (hR : DifferentiableAt ℝ R x) (hs : DifferentiableAt ℝ s x)
    (hψ : DifferentiableAt ℝ ψ x) (hu : DifferentiableAt ℝ u (R x))
    (hs₀ : s x ≠ 0)
    (hw : w (R x) = c * s x ^ 2 * deriv R x)
    (hheight : (fun t => u (R t)) =ᶠ[𝓝 x] (fun t => ψ t / s t)) :
    w (R x) * deriv u (R x) =
      c * (s x * deriv ψ x - deriv s x * ψ x) := by
  have hcomp := hu.hasDerivAt.comp x hR.hasDerivAt
  have hquot := hψ.hasDerivAt.div hs.hasDerivAt hs₀
  have hder : deriv u (R x) * deriv R x =
      (deriv ψ x * s x - ψ x * deriv s x) / s x ^ 2 :=
    hcomp.unique (hquot.congr_of_eventuallyEq hheight)
  have hscaled := (eq_div_iff (pow_ne_zero 2 hs₀)).mp hder
  rw [hw]
  calc
    _ = c * ((deriv u (R x) * deriv R x) * s x ^ 2) := by ring
    _ = _ := by rw [hscaled]; ring

/-- The actual Liouville identity on a model neighborhood.

The assumptions on the radial flux are ordinary second-order regularity of
the radial height. All other derivative assumptions are local to the model
point. In particular, no global invertibility of `R` is needed for this
differential identity; constructing the increasing radius is a separate task.
-/
theorem radialJacobi_liouville {a c x : ℝ} {R s ψ w u : ℝ → ℝ}
    (hR : ∀ᶠ t in 𝓝 x, DifferentiableAt ℝ R t)
    (hs : ∀ᶠ t in 𝓝 x, DifferentiableAt ℝ s t)
    (hψ : ∀ᶠ t in 𝓝 x, DifferentiableAt ℝ ψ t)
    (hu : ∀ᶠ t in 𝓝 x, DifferentiableAt ℝ u (R t))
    (hR₂ : DifferentiableAt ℝ (deriv R) x)
    (hs₂ : DifferentiableAt ℝ (deriv s) x)
    (hψ₂ : DifferentiableAt ℝ (deriv ψ) x)
    (hw : DifferentiableAt ℝ w (R x))
    (hflux : DifferentiableAt ℝ (fun r => w r * deriv u r) (R x))
    (hR₀ : R x ≠ 0) (hv₀ : deriv R x ≠ 0) (hs₀ : s x ≠ 0)
    (hweight : (fun t => w (R t)) =ᶠ[𝓝 x]
      (fun t => c * s t ^ 2 * deriv R t))
    (hheight : (fun t => u (R t)) =ᶠ[𝓝 x] (fun t => ψ t / s t)) :
    radialJacobi a w u (R x) =
      -(c * s x / deriv R x) * liouvilleSchrodinger a R s ψ x := by
  have hRx := hR.self_of_nhds
  have hsx := hs.self_of_nhds
  have hψx := hψ.self_of_nhds
  have hfluxeq : (fun t => w (R t) * deriv u (R t)) =ᶠ[𝓝 x]
      (fun t => c * (s t * deriv ψ t - deriv s t * ψ t)) := by
    filter_upwards [hR, hs, hψ, hu, hsx.continuousAt.eventually_ne hs₀,
      hweight, hheight.eventuallyEq_nhds] with t hRt hst hψt hut hs₀t hwt hheightt
    exact liouville_flux_at hRt hst hψt hut hs₀t hwt hheightt
  have hmodelFlux : HasDerivAt
      (fun t => c * (s t * deriv ψ t - deriv s t * ψ t))
      (c * (s x * deriv (deriv ψ) x - deriv (deriv s) x * ψ x)) x := by
    convert ((hsx.hasDerivAt.mul hψ₂.hasDerivAt).sub
      (hs₂.hasDerivAt.mul hψx.hasDerivAt)).const_mul c using 1
    ring
  have hfluxder :
      deriv (fun r => w r * deriv u r) (R x) * deriv R x =
        c * (s x * deriv (deriv ψ) x - deriv (deriv s) x * ψ x) :=
    (hflux.hasDerivAt.comp x hRx.hasDerivAt).unique
      (hmodelFlux.congr_of_eventuallyEq hfluxeq)
  have hmodelWeight : HasDerivAt (fun t => c * s t ^ 2 * deriv R t)
      (c * (2 * s x * deriv s x * deriv R x + s x ^ 2 * deriv (deriv R) x)) x := by
    convert ((hsx.hasDerivAt.pow 2).mul hR₂.hasDerivAt).const_mul c using 1
    · funext t
      simp only [Pi.mul_apply, Pi.pow_apply]
      ring
    · simp only [Pi.pow_apply]
      ring
  have hweightder : deriv w (R x) * deriv R x =
      c * (2 * s x * deriv s x * deriv R x + s x ^ 2 * deriv (deriv R) x) :=
    (hw.hasDerivAt.comp x hRx.hasDerivAt).unique
      (hmodelWeight.congr_of_eventuallyEq hweight)
  have hf := (eq_div_iff hv₀).mpr hfluxder
  have hw' := (eq_div_iff hv₀).mpr hweightder
  unfold radialJacobi
  rw [hf, hw', hheight.eq_of_nhds]
  unfold liouvilleSchrodinger liouvilleRho liouvilleV0
  field_simp [hR₀, hv₀, hs₀]
  ring

/-- The density is the square of the chosen positive square-root density. -/
def liouvilleDensity (s : ℝ → ℝ) (x : ℝ) : ℝ := s x ^ 2

theorem deriv_liouvilleDensity {s : ℝ → ℝ} {x : ℝ}
    (hs : DifferentiableAt ℝ s x) :
    deriv (liouvilleDensity s) x = 2 * s x * deriv s x := by
  change deriv (fun t => s t ^ 2) x = 2 * s x * deriv s x
  convert (hs.hasDerivAt.fun_pow 2).deriv using 1
  ring

/-- This identifies `2 s'/s` with the manuscript's actual `P'/P`. -/
theorem liouville_density_log_derivative {s : ℝ → ℝ} {x : ℝ}
    (hs : DifferentiableAt ℝ s x) (hs₀ : s x ≠ 0) :
    deriv (liouvilleDensity s) x / liouvilleDensity s x =
      2 * deriv s x / s x := by
  rw [deriv_liouvilleDensity hs]
  unfold liouvilleDensity
  field_simp [hs₀]

theorem liouvilleRho_eq_density {R s : ℝ → ℝ} {x : ℝ}
    (hs : DifferentiableAt ℝ s x) (hs₀ : s x ≠ 0) :
    liouvilleRho R s x =
      -(deriv (deriv R) x +
        (deriv (liouvilleDensity s) x / liouvilleDensity s x) * deriv R x) / R x := by
  rw [liouville_density_log_derivative hs hs₀]
  rfl

/-- On a positive model neighborhood, the chosen density really is `sqrt P`,
including the second derivative used in the potential. -/
theorem liouvilleV0_eq_sqrtDensity {s : ℝ → ℝ} {x : ℝ}
    (hs : ∀ᶠ t in 𝓝 x, 0 ≤ s t) :
    liouvilleV0 s x =
      deriv (deriv (fun t => Real.sqrt (liouvilleDensity s t))) x /
        Real.sqrt (liouvilleDensity s x) := by
  have heq : (fun t => Real.sqrt (liouvilleDensity s t)) =ᶠ[𝓝 x] s := by
    filter_upwards [hs] with t ht
    exact Real.sqrt_sq ht
  unfold liouvilleV0
  rw [heq.deriv.deriv_eq, heq.eq_of_nhds]

/-- The exact source factor for the Schrödinger equation. -/
def liouvilleSource (c : ℝ) (R s f : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(deriv R x / (c * s x)) * f (R x)

/-- Once the proved differential identity is applied, this converts an actual
radial forcing equation into its model forcing equation. -/
theorem liouville_forcing_iff {a c x : ℝ} {R s ψ w u f : ℝ → ℝ}
    (hc : c ≠ 0) (hs : s x ≠ 0) (hv : deriv R x ≠ 0)
    (hidentity : radialJacobi a w u (R x) =
      -(c * s x / deriv R x) * liouvilleSchrodinger a R s ψ x) :
    radialJacobi a w u (R x) = f (R x) ↔
      liouvilleSchrodinger a R s ψ x = liouvilleSource c R s f x := by
  rw [hidentity]
  unfold liouvilleSource
  constructor <;> intro h
  · calc
      _ = -(deriv R x / (c * s x)) *
          (-(c * s x / deriv R x) * liouvilleSchrodinger a R s ψ x) := by
        field_simp [hc, hs, hv]
      _ = _ := congrArg (fun z : ℝ => -(deriv R x / (c * s x)) * z) h
  · rw [h]
    field_simp [hc, hs, hv]

/-- Ordinary `dr` source pairings acquire the factor `v/s`, not the Hilbert
weight used for the self-adjoint model. -/
theorem liouville_source_pairing_density (R s ψ u f : ℝ → ℝ) (x v : ℝ)
    (hu : u (R x) = ψ x / s x) :
    (u (R x) * f (R x)) * v = ψ x * (v / s x * f (R x)) := by
  rw [hu]
  ring

/-- Pullback of the natural Hilbert density `12 w/r² dr`.
This is distinct from the ordinary `dr` pairing in the previous theorem. -/
theorem liouville_hilbert_density {c x v : ℝ} {R s ψ w u : ℝ → ℝ}
    (hs₀ : s x ≠ 0) (hw : w (R x) = c * s x ^ 2 * v)
    (hu : u (R x) = ψ x / s x) :
    (12 * w (R x) / R x ^ 2) * u (R x) ^ 2 * v =
      12 * c * (v / R x) ^ 2 * ψ x ^ 2 := by
  rw [hw, hu]
  by_cases hR : R x = 0
  · simp [hR]
  · field_simp [hs₀, hR]

end

end ContinuousFlexibility.Radial
