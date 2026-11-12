import ContinuousFlexibility.Analysis.N06WeakPartialProduct

/-!
# The actual six weak partial fields of the finite cosine synthesis

One C1 radial representative with an absolutely continuous first
derivative determines the value, two first partials, and three second
partials. All six are genuine L2 functions and satisfy the original
distributional identities on the entire unit test class.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

structure N06UnitWeakH2Row (U Ur Ut Urr Urt Utt : PolarPoint → ℝ) : Prop where
  value_memLp : MemLp U 2 (cylinderWindowMeasure 0)
  radial_memLp : MemLp Ur 2 (cylinderWindowMeasure 0)
  angular_memLp : MemLp Ut 2 (cylinderWindowMeasure 0)
  radial_radial_memLp : MemLp Urr 2 (cylinderWindowMeasure 0)
  radial_angular_memLp : MemLp Urt 2 (cylinderWindowMeasure 0)
  angular_angular_memLp : MemLp Utt 2 (cylinderWindowMeasure 0)
  radial : N06UnitWeakRadialDerivative U Ur
  angular : N06UnitWeakAngularDerivative U Ut
  radial_radial : N06UnitWeakRadialDerivative Ur Urr
  radial_angular : N06UnitWeakAngularDerivative Ur Urt
  angular_radial : N06UnitWeakRadialDerivative Ut Urt
  angular_angular : N06UnitWeakAngularDerivative Ut Utt

def n06FiniteMixedField (s : Finset ℕ) (v : ℕ → ℝ → ℝ) (a b : ℕ) :
    PolarPoint → ℝ :=
  r11bFiniteSynthesis s (fun i => iteratedDeriv a (v i))
    (fun i => iteratedDeriv b (referenceAngularBasis i))

theorem n06_finiteMixedField_memLp (s : Finset ℕ) (v : ℕ → ℝ → ℝ) (a b : ℕ)
    (hv : ∀ i ∈ s, MemLp (iteratedDeriv a (v i)) 2
      (volume.restrict (Ioo (0 : ℝ) 1))) :
    MemLp (n06FiniteMixedField s v a b) 2 (cylinderWindowMeasure 0) :=
  n06_weak_finiteSynthesis_memLp s _ _ hv (fun i _ =>
    (circleFourier_contDiff_iteratedDeriv (contDiff_referenceAngularBasis i) b).continuous)

theorem n06_finiteMixedField_weak_radial (s : Finset ℕ) (v : ℕ → ℝ → ℝ) (a b : ℕ)
    (hAC : ∀ i ∈ s, AbsolutelyContinuousOnInterval (iteratedDeriv a (v i)) 0 1)
    (hv : ∀ i ∈ s, MemLp (iteratedDeriv a (v i)) 2
      (volume.restrict (Ioo (0 : ℝ) 1)))
    (hvd : ∀ i ∈ s, MemLp (iteratedDeriv (a + 1) (v i)) 2
      (volume.restrict (Ioo (0 : ℝ) 1))) :
    N06UnitWeakRadialDerivative (n06FiniteMixedField s v a b)
      (n06FiniteMixedField s v (a + 1) b) := by
  intro φ hφ
  simpa only [n06FiniteMixedField, iteratedDeriv_succ] using
    n06_finiteSynthesis_weak_radial s (fun i => iteratedDeriv a (v i))
      (fun i => iteratedDeriv b (referenceAngularBasis i)) hAC hv
      (fun i hi => by simpa only [iteratedDeriv_succ] using hvd i hi)
      (fun i _ => (circleFourier_contDiff_iteratedDeriv
        (contDiff_referenceAngularBasis i) b).continuous) hφ

theorem n06_finiteMixedField_weak_angular (s : Finset ℕ) (v : ℕ → ℝ → ℝ) (a b : ℕ)
    (hv : ∀ i ∈ s, MemLp (iteratedDeriv a (v i)) 2
      (volume.restrict (Ioo (0 : ℝ) 1))) :
    N06UnitWeakAngularDerivative (n06FiniteMixedField s v a b)
      (n06FiniteMixedField s v a (b + 1)) := by
  intro φ hφ
  simpa only [n06FiniteMixedField, iteratedDeriv_succ] using
    n06_finiteSynthesis_weak_angular s (fun i => iteratedDeriv a (v i))
      (fun i => iteratedDeriv b (referenceAngularBasis i)) hv
      (fun i _ => circleFourier_contDiff_iteratedDeriv (contDiff_referenceAngularBasis i) b)
      (fun i _ => circleFourier_periodic_iteratedDeriv (referenceAngularBasis_periodic i) b) hφ

/-- No second classical radial differentiability is assumed. The actual
L2 second derivative and the AC first derivative suffice. -/
theorem n06_finiteMixedField_weakH2 (s : Finset ℕ) (v : ℕ → ℝ → ℝ)
    (hC : ∀ i ∈ s, ContDiff ℝ 1 (v i))
    (hAC : ∀ i ∈ s, AbsolutelyContinuousOnInterval (deriv (v i)) 0 1)
    (hv : ∀ i ∈ s, MemLp (v i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₁ : ∀ i ∈ s, MemLp (deriv (v i)) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₂ : ∀ i ∈ s, MemLp (deriv (deriv (v i))) 2
      (volume.restrict (Ioo (0 : ℝ) 1))) :
    N06UnitWeakH2Row (n06FiniteMixedField s v 0 0)
      (n06FiniteMixedField s v 1 0) (n06FiniteMixedField s v 0 1)
      (n06FiniteMixedField s v 2 0) (n06FiniteMixedField s v 1 1)
      (n06FiniteMixedField s v 0 2) := by
  have h₀ : ∀ i ∈ s, MemLp (iteratedDeriv 0 (v i)) 2
      (volume.restrict (Ioo (0 : ℝ) 1)) := by simpa only [iteratedDeriv_zero] using hv
  have h₁ : ∀ i ∈ s, MemLp (iteratedDeriv 1 (v i)) 2
      (volume.restrict (Ioo (0 : ℝ) 1)) := by simpa only [iteratedDeriv_one] using hv₁
  have h₂ : ∀ i ∈ s, MemLp (iteratedDeriv 2 (v i)) 2
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_one, iteratedDeriv_zero] using hv₂
  have hAC₀ : ∀ i ∈ s, AbsolutelyContinuousOnInterval (iteratedDeriv 0 (v i)) 0 1 := by
    intro i hi
    simpa only [iteratedDeriv_zero] using (hC i hi).contDiffOn.absolutelyContinuousOnInterval
  have hAC₁ : ∀ i ∈ s, AbsolutelyContinuousOnInterval (iteratedDeriv 1 (v i)) 0 1 := by
    simpa only [iteratedDeriv_one] using hAC
  exact ⟨n06_finiteMixedField_memLp s v 0 0 h₀,
    n06_finiteMixedField_memLp s v 1 0 h₁,
    n06_finiteMixedField_memLp s v 0 1 h₀,
    n06_finiteMixedField_memLp s v 2 0 h₂,
    n06_finiteMixedField_memLp s v 1 1 h₁,
    n06_finiteMixedField_memLp s v 0 2 h₀,
    n06_finiteMixedField_weak_radial s v 0 0 hAC₀ h₀ h₁,
    n06_finiteMixedField_weak_angular s v 0 0 h₀,
    n06_finiteMixedField_weak_radial s v 1 0 hAC₁ h₁ h₂,
    n06_finiteMixedField_weak_angular s v 1 0 h₁,
    n06_finiteMixedField_weak_radial s v 0 1 hAC₀ h₀ h₁,
    n06_finiteMixedField_weak_angular s v 0 1 h₀⟩

end ContinuousFlexibility.Analysis
