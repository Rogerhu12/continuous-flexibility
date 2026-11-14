module

public import ContinuousFlexibility.Radial.SelectedReferenceTransport

/-!
# The radial equation on an actually rescaled reference interval

R08 identifies the reference profile with a dilation only on its retained
tail. These lemmas pass from that local identity to the actual derivatives
in the Jacobi expression. The complete reference need not be a dilation.
Both orientations use the same open-set and interval statements.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- The Jacobi expression only depends on the germ of its profile. -/
theorem radialJacobi_eq_of_profile_eventuallyEq {J r : ℝ}
    {w w' u : ℝ → ℝ} (hw : w =ᶠ[𝓝 r] w') :
    radialJacobi J w u r = radialJacobi J w' u r := by
  have hflux : (fun t => w t * deriv u t) =ᶠ[𝓝 r]
      (fun t => w' t * deriv u t) := by
    filter_upwards [hw] with t ht
    rw [ht]
  unfold radialJacobi
  rw [hflux.deriv_eq, hw.deriv_eq]

/-- A profile identity on an open source interval gives the target germ
at every corresponding point, including the derivatives used by the ODE. -/
theorem referenceProfile_radiusScale_eventuallyEq
    {D E : ReferenceData} {I : Set ℝ} {κ β r : ℝ}
    (hκ : κ ≠ 0) (hI : IsOpen I) (hr : r ∈ I)
    (hprofile : ∀ t ∈ I, E.w (κ * t) = (β * κ) * D.w t) :
    E.w =ᶠ[𝓝 (κ * r)] radialRadiusScale κ (β * κ) D.w := by
  have hdiv : κ * r / κ = r := by field_simp [hκ] <;> ring
  have hcont : ContinuousAt (fun t : ℝ => t / κ) (κ * r) :=
    continuousAt_id.div_const κ
  have hsource : ∀ᶠ t : ℝ in 𝓝 (κ * r / κ), t ∈ I := by
    rw [hdiv]
    exact hI.mem_nhds hr
  have hmem : ∀ᶠ t : ℝ in 𝓝 (κ * r), t / κ ∈ I := hcont.eventually hsource
  filter_upwards [hmem] with t ht
  have hcancel : κ * (t / κ) = t := by field_simp [hκ] <;> ring
  have h := hprofile (t / κ) ht
  rw [hcancel] at h
  exact h

/-- Exact source covariance for the actual reference profile on the retained
open set. No global equality of references or profiles is assumed. -/
theorem radialJacobi_reference_radiusScale
    {D E : ReferenceData} {I : Set ℝ} {κ β r : ℝ}
    (hκ : κ ≠ 0) (hI : IsOpen I) (hr : r ∈ I)
    (hprofile : ∀ t ∈ I, E.w (κ * t) = (β * κ) * D.w t)
    (J α : ℝ) (u : ℝ → ℝ) :
    radialJacobi J E.w (radialRadiusScale κ α u) (κ * r) =
      (β * α / κ) * radialJacobi J D.w u r := by
  rw [radialJacobi_eq_of_profile_eventuallyEq
    (referenceProfile_radiusScale_eventuallyEq hκ hI hr hprofile)]
  exact radialJacobi_radialRadiusScale hκ J α β D.w u r

/-- Smoothness under the actual linear radius map, on its inverse-image
domain. Multiplication by the solution amplitude is independent. -/
theorem contDiffOn_radialRadiusScale {I : Set ℝ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ ∞ u I) (κ α : ℝ) :
    ContDiffOn ℝ ∞ (radialRadiusScale κ α u) ((fun t : ℝ => t / κ) ⁻¹' I) := by
  have hmap : MapsTo (fun t : ℝ => t / κ) ((fun t : ℝ => t / κ) ⁻¹' I) I :=
    fun _ ht => ht
  exact contDiffOn_const.mul (hu.comp (contDiff_id.div_const κ).contDiffOn hmap)

/-- Entrance smoothness is transported as an actual germ at the rescaled
entrance; it is stronger than smoothness inside the open tail alone. -/
theorem contDiffAt_radialRadiusScale {u : ℝ → ℝ} {r κ : ℝ}
    (hκ : κ ≠ 0) (hu : ContDiffAt ℝ ∞ u r) (α : ℝ) :
    ContDiffAt ℝ ∞ (radialRadiusScale κ α u) (κ * r) := by
  have hdiv : κ * r / κ = r := by field_simp [hκ] <;> ring
  have hu' : ContDiffAt ℝ ∞ u ((κ * r) / κ) := by simpa only [hdiv] using hu
  exact contDiffAt_const.mul (hu'.comp (κ * r) (contDiffAt_id.div_const κ))

/-- The full homogeneous predicate, with its actual derivatives and smoothness,
transports to the retained part of the same target reference. -/
theorem radialHomogeneousOn_reference_radiusScale
    {D E : ReferenceData} {I : Set ℝ} {κ β : ℝ}
    (hκ : κ ≠ 0) (hI : IsOpen I)
    (hprofile : ∀ t ∈ I, E.w (κ * t) = (β * κ) * D.w t)
    {j : ℕ} {u : ℝ → ℝ} (hu : RadialHomogeneousOn D j I u) (α : ℝ) :
    RadialHomogeneousOn E j ((fun t : ℝ => t / κ) ⁻¹' I)
      (radialRadiusScale κ α u) := by
  refine ⟨contDiffOn_radialRadiusScale hu.1 κ α, ?_⟩
  intro t ht
  have hcancel : κ * (t / κ) = t := by field_simp [hκ] <;> ring
  have h := radialJacobi_reference_radiusScale hκ hI ht hprofile
    ((j : ℝ) ^ 2) α u
  rw [hcancel, hu.2 (t / κ) ht, mul_zero] at h
  exact h

/-- Positive radius scaling gives the expected actual interval endpoints. -/
theorem preimage_div_Ioo_of_pos {κ : ℝ} (hκ : 0 < κ) (l h : ℝ) :
    (fun t : ℝ => t / κ) ⁻¹' Ioo l h = Ioo (κ * l) (κ * h) := by
  ext t
  change (l < t / κ ∧ t / κ < h) ↔ (κ * l < t ∧ t < κ * h)
  rw [lt_div_iff₀ hκ, div_lt_iff₀ hκ]
  simp only [mul_comm]

/-- The interval version used for both retained tails in R08. -/
theorem radialHomogeneousOn_reference_scaled_interval
    {D E : ReferenceData} {κ β l h : ℝ}
    (hκ : 0 < κ)
    (hprofile : ∀ t ∈ Ioo l h, E.w (κ * t) = (β * κ) * D.w t)
    {j : ℕ} {u : ℝ → ℝ} (hu : RadialHomogeneousOn D j (Ioo l h) u) (α : ℝ) :
    RadialHomogeneousOn E j (Ioo (κ * l) (κ * h)) (radialRadiusScale κ α u) := by
  have H := radialHomogeneousOn_reference_radiusScale hκ.ne' isOpen_Ioo hprofile hu α
  rw [preimage_div_Ioo_of_pos hκ l h] at H
  exact H

end ContinuousFlexibility.Radial
