import ContinuousFlexibility.Radial.RadialPositiveHardy
import ContinuousFlexibility.Radial.InnerGapPoissonL2

/-!
# Hardy bounds for the actual gap Poisson map

The bound keeps the complete conormal matrix of the original columns.
The only additional term is their actual left endpoint trace. It does
not use a uniform positive lower bound on the logarithmic slope.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

theorem innerGapPoisson_mass_hardy {a b j : ℝ} (hab : a ≤ b) (ha : 0 < a)
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (p : Fin 2 → ℝ → ℝ)
    (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (hb : ∀ i k, p k (innerGapEndpoint a b i) = if k = i then 1 else 0)
    (heq : ∀ i r, r ∈ Icc a b → radialJacobi (j ^ 2) w (p i) r = 0)
    (hpos : ∀ r ∈ Icc a b, 0 ≤ w r)
    (hwp : ∀ r ∈ Icc a b, 0 ≤ deriv w r) (hj : (1 / 2 : ℝ) ≤ j ^ 2)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    innerRadialGapMass w (innerGapPoisson p ξ) a b ≤
      48 * ⟪ξ, innerGapFluxOperator w a b p ξ⟫_ℝ +
        24 * (w a / a) * (ξ 0) ^ 2 := by
  have h := radialPositiveHardy_mass_le_energy_left hab ha hw
    (innerGapPoisson_contDiff p hp ξ) hpos hwp hj
  change innerRadialGapMass w (innerGapPoisson p ξ) a b ≤
    48 * innerRadialGapEnergy w (innerGapPoisson p ξ) j a b +
      24 * (w a / a) * innerGapPoisson p ξ a ^ 2 at h
  have hleft : innerGapPoisson p ξ a = ξ 0 := by
    simpa only [innerGapEndpoint_zero] using innerGapPoisson_boundary p hb ξ 0
  rw [innerGapPoisson_energy_eq hab ha hw p hp hb heq, hleft] at h
  exact h

/-- This estimate uses the same zero-extended Poisson operator and the
same physical radial measure as the gap assembly. -/
theorem innerGapPoissonL2_norm_sq_hardy (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j : ℝ} (hab : a ≤ b) (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 ≤ D.w r)
    (hwp : ∀ r ∈ Icc a b, 0 ≤ deriv D.w r) (hj : (1 / 2 : ℝ) ≤ j ^ 2)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (hb : ∀ i k, p k (innerGapEndpoint a b i) = if k = i then 1 else 0)
    (heq : ∀ i r, r ∈ Icc a b → radialJacobi (j ^ 2) D.w (p i) r = 0)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    ‖innerGapPoissonL2 D hw.continuous ha hcore
      (fun r hr => hpos r (Ioo_subset_Icc_self hr)) p hp ξ‖ ^ 2 ≤
      48 * ⟪ξ, innerGapFluxOperator D.w a b p ξ⟫_ℝ +
        24 * (D.w a / a) * (ξ 0) ^ 2 := by
  rw [innerGapPoissonL2_norm_sq D hw.continuous hab]
  exact innerGapPoisson_mass_hardy hab ha hw p hp hb heq hpos hwp hj ξ

/-- Normalization by a genuine adjacent-model energy preserves the
full gap form and divides the explicit left trace cost by that energy. -/
theorem innerGapPoissonL2_normalized_norm_sq_hardy (D : ReferenceData)
    (hw : ContDiff ℝ ∞ D.w) {a b j κ : ℝ} (hab : a ≤ b) (ha : 0 < a)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 ≤ D.w r)
    (hwp : ∀ r ∈ Icc a b, 0 ≤ deriv D.w r) (hj : (1 / 2 : ℝ) ≤ j ^ 2)
    (hκ : 0 < κ) (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (hb : ∀ i k, p k (innerGapEndpoint a b i) = if k = i then 1 else 0)
    (heq : ∀ i r, r ∈ Icc a b → radialJacobi (j ^ 2) D.w (p i) r = 0)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    ‖(sqrt κ)⁻¹ • innerGapPoissonL2 D hw.continuous ha hcore
      (fun r hr => hpos r (Ioo_subset_Icc_self hr)) p hp ξ‖ ^ 2 ≤
      (48 * ⟪ξ, innerGapFluxOperator D.w a b p ξ⟫_ℝ +
        24 * (D.w a / a) * (ξ 0) ^ 2) / κ := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (sqrt_nonneg κ)),
    mul_pow, inv_pow, sq_sqrt hκ.le, mul_comm, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right
    (innerGapPoissonL2_norm_sq_hardy D hw hab ha hcore hpos hwp hj p hp hb heq ξ) hκ.le

end ContinuousFlexibility.Radial
