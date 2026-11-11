import ContinuousFlexibility.Analysis.N07aCanonicalOpenProduct

/-!
# The bounded jet algebra of actual open-piece coefficients

This record retains the actual scalar function, its interior smoothness,
periodicity, and bounded spatial jets on one fixed piece. Derivative and
multiplication operations use those same functions. No regularity of an
unknown or extension of a coefficient across an endpoint is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

structure N07aCanonicalOpenCoefficient (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) where
  value : PolarPoint → ℝ
  smooth : ContDiffOn ℝ ∞ value (canonicalOpen S K m)
  periodic : ∀ p ∈ canonicalOpen S K m, value (p + (0, Real.pi)) = value p
  bounded : ∀ a b : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᵐ p ∂canonicalMeasure S K m, |mixedDerivative a b value p| ≤ C

namespace N07aCanonicalOpenCoefficient

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

def jet (χ : N07aCanonicalOpenCoefficient S K m) (a b : ℕ) :
    N07aCanonicalOpenCoefficient S K m where
  value := mixedDerivative a b χ.value
  smooth := contDiffOn_mixedDerivative (isOpen_Ioo.prod isOpen_univ) χ.smooth a b
  periodic := n07a_mixedDerivative_periodic_on χ.periodic a b
  bounded := by
    intro c d
    obtain ⟨C, hC, hbound⟩ := χ.bounded (c + a) (d + b)
    refine ⟨C, hC, ?_⟩
    filter_upwards [hbound, n07a_canonicalOpen_ae (S := S) (K := K) (m := m)]
      with p hp hpU
    rw [n07a_mixedDerivative_mixedDerivative_on (isOpen_Ioo.prod isOpen_univ)
      χ.smooth c d a b hpU]
    exact hp

def bound (χ : N07aCanonicalOpenCoefficient S K m) : ℝ := (χ.bounded 0 0).choose

theorem bound_nonneg (χ : N07aCanonicalOpenCoefficient S K m) : 0 ≤ χ.bound :=
  (χ.bounded 0 0).choose_spec.1

theorem bound_ae (χ : N07aCanonicalOpenCoefficient S K m) :
    ∀ᵐ p ∂canonicalMeasure S K m, |χ.value p| ≤ χ.bound := by
  filter_upwards [(χ.bounded 0 0).choose_spec.2] with p hp
  calc
    |χ.value p| = |mixedDerivative 0 0 χ.value p| := by
      rw [spaces_mixedDerivative_zero]
    _ ≤ χ.bound := hp

def mul (χ : N07aCanonicalOpenCoefficient S K m) :
    CanonicalL2 S K m →L[ℝ] CanonicalL2 S K m :=
  n07aCanonicalMultiplier χ.value
    (n07a_canonicalOpen_aestronglyMeasurable χ.smooth.continuousOn) χ.bound χ.bound_ae

theorem mul_ae (χ : N07aCanonicalOpenCoefficient S K m) (u : CanonicalL2 S K m) :
    (χ.mul u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] fun p => χ.value p * u p :=
  n07aCanonicalMultiplier_ae _ _ _ _ u

theorem mul_norm_le (χ : N07aCanonicalOpenCoefficient S K m) (u : CanonicalL2 S K m) :
    ‖χ.mul u‖ ≤ χ.bound * ‖u‖ :=
  n07aCanonicalMultiplier_norm_le _ _ _ _ u

theorem first_product (χ : N07aCanonicalOpenCoefficient S K m) (j : Fin 2)
    {u du : CanonicalL2 S K m}
    (hu : N07aWeakCanonicalMixedDerivative S K m u du
      (n07aFirstOrder j).1 (n07aFirstOrder j).2) :
    N07aWeakCanonicalMixedDerivative S K m (χ.mul u)
      (χ.mul du + (χ.jet (n07aFirstOrder j).1 (n07aFirstOrder j).2).mul u)
      (n07aFirstOrder j).1 (n07aFirstOrder j).2 :=
  n07a_weakCanonical_first_product_on χ.smooth χ.periodic j
    χ.bound (χ.jet (n07aFirstOrder j).1 (n07aFirstOrder j).2).bound
    χ.bound_ae (χ.jet (n07aFirstOrder j).1 (n07aFirstOrder j).2).bound_ae hu

private theorem angularJet (k : ℕ) :
    ∀ (χ : N07aCanonicalOpenCoefficient S K m) (u : CanonicalL2 S K m),
      N07aCanonicalNormalRegular S K m u 0 →
      ∃ v : CanonicalL2 S K m, N07aWeakCanonicalMixedDerivative S K m (χ.mul u) v 0 k := by
  induction k with
  | zero =>
    intro χ u _
    exact ⟨_, n07a_weakCanonicalMixed_refl _⟩
  | succ k ih =>
    intro χ u hu
    obtain ⟨uθ, huθ⟩ := hu 0 le_rfl 1
    have huθreg : N07aCanonicalNormalRegular S K m uθ 0 := hu.derivative huθ
    obtain ⟨v, hv⟩ := ih χ uθ huθreg
    obtain ⟨w, hw⟩ := ih (χ.jet 0 1) u hu
    have hfirst := χ.first_product (1 : Fin 2) huθ
    refine ⟨v + w, ?_⟩
    simpa [n07aFirstOrder, Nat.add_comm] using hfirst.comp (hv.add hw)

theorem angularRegular (χ : N07aCanonicalOpenCoefficient S K m)
    {u : CanonicalL2 S K m} (hu : N07aCanonicalNormalRegular S K m u 0) :
    N07aCanonicalNormalRegular S K m (χ.mul u) 0 := by
  intro a ha b
  have : a = 0 := Nat.eq_zero_of_le_zero ha
  subst a
  exact angularJet b χ u hu

/-- Multiplication by an actual coefficient with bounded interior jets
preserves all angular orders and every finite weak normal order. -/
theorem normalRegular (n : ℕ) :
    ∀ (χ : N07aCanonicalOpenCoefficient S K m) (u : CanonicalL2 S K m),
      N07aCanonicalNormalRegular S K m u n →
      N07aCanonicalNormalRegular S K m (χ.mul u) n := by
  induction n with
  | zero =>
    intro χ u hu
    exact χ.angularRegular hu
  | succ n ih =>
    intro χ u hu
    obtain ⟨ur, hur⟩ := hu 1 (by omega) 0
    have hurreg : N07aCanonicalNormalRegular S K m ur n := hu.derivative hur
    have hureg : N07aCanonicalNormalRegular S K m u n := hu.mono (by omega)
    have hprod := χ.first_product (0 : Fin 2) hur
    apply n07aCanonicalNormalRegular_of_first
      (χ.angularRegular (hu.mono (Nat.zero_le _))) hprod
    exact (ih χ ur hurreg).add (ih (χ.jet 1 0) u hureg)

end N07aCanonicalOpenCoefficient

end ContinuousFlexibility.Analysis
