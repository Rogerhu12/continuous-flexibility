module

public import ContinuousFlexibility.Analysis.N06NegativeWeakModes

/-!
# The finite negative principal field is the actual forcing cutoff

The modal equations obtained from the original graph identify the entire
finite principal field with the finite cosine synthesis of its actual L2
forcing. This identity is in the original canonical measure. It allows
the Green bulk terms to pass to a limit using only value and source L2
convergence, without an infinite boundary trace or a full second-jet limit.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The actual finite principal field is the synthesis of the modal
forcing, with the sign dictated by the negative normal form. -/
theorem n06_negative_finite_principal_eq_synthesis
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (s : Finset ℕ) (v f : ℕ → ℝ → ℝ)
    (hode : ∀ i ∈ s, ∀ᵐ y ∂volume.restrict (Ioo (K.left m) (K.right m)),
      deriv (deriv (v i)) y + (((2 * i : ℕ) : ℝ)) ^ 2 * y * v i y = f i y) :
    (fun p : PolarPoint =>
      n06FiniteMixedField s v 2 0 p - p.1 * n06FiniteMixedField s v 0 2 p)
      =ᵐ[canonicalMeasure S K m] r11bFiniteSynthesis s f referenceAngularBasis := by
  have hall : ∀ᵐ y ∂volume.restrict (Ioo (K.left m) (K.right m)),
      ∀ i ∈ s, deriv (deriv (v i)) y + (((2 * i : ℕ) : ℝ)) ^ 2 * y * v i y = f i y :=
    (eventually_all_finset s).mpr hode
  have hp : ∀ᵐ p : PolarPoint ∂canonicalMeasure S K m,
      ∀ i ∈ s, deriv (deriv (v i)) p.1 + (((2 * i : ℕ) : ℝ)) ^ 2 * p.1 * v i p.1 = f i p.1 := by
    rw [n06_canonicalMeasure_eq_radial_prod]
    exact Measure.quasiMeasurePreserving_fst.ae hall
  filter_upwards [hp] with p hmode
  simp only [n06FiniteMixedField, r11bFiniteSynthesis, iteratedDeriv_zero,
    show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [deriv_deriv_referenceAngularBasis, ← hmode i hi]
  ring

/-- The same principal-field identification for the forcing of one
canonical L2 class, on every finite cutoff. -/
theorem n06_negative_finite_principal_eq_forcingCut
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (G : CanonicalL2 S K m) (v : ℕ → ℝ → ℝ)
    (hode : ∀ i, ∀ᵐ y ∂volume.restrict (Ioo (K.left m) (K.right m)),
      deriv (deriv (v i)) y + (((2 * i : ℕ) : ℝ)) ^ 2 * y * v i y =
        n06HalfCosineCoefficient G i y) (s : Finset ℕ) :
    (fun p : PolarPoint =>
      n06FiniteMixedField s v 2 0 p - p.1 * n06FiniteMixedField s v 0 2 p)
      =ᵐ[canonicalMeasure S K m]
        r11bFiniteSynthesis s (n06HalfCosineCoefficient G) referenceAngularBasis :=
  n06_negative_finite_principal_eq_synthesis s v (n06HalfCosineCoefficient G)
    (fun i _ => hode i)

end ContinuousFlexibility.Analysis
