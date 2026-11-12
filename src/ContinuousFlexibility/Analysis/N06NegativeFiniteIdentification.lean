import ContinuousFlexibility.Analysis.N06CompactCanonicalTraces
import ContinuousFlexibility.Analysis.N06NegativeBulkLimits
import ContinuousFlexibility.Analysis.N06CurrentTestTensorGreen
import ContinuousFlexibility.Analysis.N06CanonicalTestSeparation

/-!
# Finite negative height identifies the actual principal forcing

The finite H2 Green identity on the original half-period rectangle has
zero true boundary terms for compact canonical tests. Hence a finite
height representing the original weak solution has exactly the finite
principal source. The proof uses the original weak equation and L2 test
separation, and does not assume a finite raw source or discard its scalar
columns.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
  {U G : CanonicalL2 S K m}

/-- Every finite subset of the actual H2 modes obeys the compact weak
principal equation. Its endpoint Wronskians vanish by test support. -/
theorem N06NegativeGraphApproximation.finite_principal_weak
    (P : N06NegativeGraphApproximation U G) (D : ReferenceData) (s : Finset ℕ)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    (∫ p, r11bFiniteSynthesis s P.modes referenceAngularBasis p * n06NegativePrincipalTest φ p
      ∂canonicalMeasure S K m) =
      ∫ p, (n06FiniteMixedField s P.modes 2 0 p -
        p.1 * n06FiniteMixedField s P.modes 0 2 p) * φ p ∂canonicalMeasure S K m := by
  let Dm : ReferenceData := { D with a := K.left m, b := K.right m }
  have hg := n06_finite_negative_principal_green_half (D := Dm) P.left_lt_right.le
    s P.modes (fun i _ => P.contDiff i) (fun i _ => P.deriv_ac i)
    (fun i _ => P.mode_memLp i) (fun i _ => P.deriv_memLp i)
    (fun i _ => P.second_memLp i) hφ.1 hφ.2.1
  change
    (∫ p, (n06FiniteMixedField s P.modes 2 0 p -
        p.1 * n06FiniteMixedField s P.modes 0 2 p) * φ p ∂canonicalMeasure S K m) -
      (∫ p, r11bFiniteSynthesis s P.modes referenceAngularBasis p * n06NegativePrincipalTest φ p
        ∂canonicalMeasure S K m) = _ at hg
  have hzero (θ : ℝ) :
      (φ (K.right m, θ) *
          radialPartial (r11bFiniteSynthesis s P.modes referenceAngularBasis) (K.right m, θ) -
        r11bFiniteSynthesis s P.modes referenceAngularBasis (K.right m, θ) *
          radialPartial φ (K.right m, θ)) -
      (φ (K.left m, θ) *
          radialPartial (r11bFiniteSynthesis s P.modes referenceAngularBasis) (K.left m, θ) -
        r11bFiniteSynthesis s P.modes referenceAngularBasis (K.left m, θ) *
          radialPartial φ (K.left m, θ)) = 0 := by
    have hends (y : ℝ) (hy : y ∉ Ioo (K.left m) (K.right m)) :=
      hφ.n06_value_radial_zero_of_not_mem hy θ
    have hl := hends (K.left m) (by simp only [mem_Ioo, lt_self_iff_false, false_and, not_false_eq_true])
    have hr := hends (K.right m) (by simp only [mem_Ioo, lt_self_iff_false, and_false, not_false_eq_true])
    simp only [hl.1, hl.2, hr.1, hr.2, zero_mul, mul_zero, sub_self]
  have hboundary :
      (∫ θ in (0 : ℝ)..Real.pi,
        (φ (K.right m, θ) *
            radialPartial (r11bFiniteSynthesis s P.modes referenceAngularBasis) (K.right m, θ) -
          r11bFiniteSynthesis s P.modes referenceAngularBasis (K.right m, θ) *
            radialPartial φ (K.right m, θ)) -
        (φ (K.left m, θ) *
            radialPartial (r11bFiniteSynthesis s P.modes referenceAngularBasis) (K.left m, θ) -
          r11bFiniteSynthesis s P.modes referenceAngularBasis (K.left m, θ) *
            radialPartial φ (K.left m, θ))) = 0 := by
    simp_rw [hzero]
    exact intervalIntegral.integral_zero
  change _ = (∫ θ in (0 : ℝ)..Real.pi,
    (φ (K.right m, θ) *
        radialPartial (r11bFiniteSynthesis s P.modes referenceAngularBasis) (K.right m, θ) -
      r11bFiniteSynthesis s P.modes referenceAngularBasis (K.right m, θ) *
        radialPartial φ (K.right m, θ)) -
    (φ (K.left m, θ) *
        radialPartial (r11bFiniteSynthesis s P.modes referenceAngularBasis) (K.left m, θ) -
      r11bFiniteSynthesis s P.modes referenceAngularBasis (K.left m, θ) *
        radialPartial φ (K.left m, θ))) at hg
  rw [hboundary] at hg
  exact (sub_eq_zero.mp hg).symm

/-- Finite H2 principal fields are genuine elements of the same original
canonical L2 space. The modal ODE identifies them with finite forcing sums. -/
theorem N06NegativeGraphApproximation.finite_principal_memLp
    (P : N06NegativeGraphApproximation U G) (s : Finset ℕ) :
    MemLp (fun p : PolarPoint => n06FiniteMixedField s P.modes 2 0 p -
      p.1 * n06FiniteMixedField s P.modes 0 2 p) 2 (canonicalMeasure S K m) := by
  have hf : MemLp (r11bFiniteSynthesis s (n06HalfCosineCoefficient G) referenceAngularBasis)
      2 (canonicalMeasure S K m) := by
    unfold r11bFiniteSynthesis
    exact memLp_finsetSum s (fun i _ => n06_canonical_tensor_memLp
      (n06_canonical_halfCosineCoefficient_memLp G i) (contDiff_referenceAngularBasis i).continuous)
  exact (memLp_congr_ae (n06_negative_finite_principal_eq_forcingCut G P.modes P.ode s)).mpr hf

/-- The true original principal weak equation identifies the entire L2
forcing once the finite height is known. No assumption on source angular
support is introduced. -/
theorem N06NegativeGraphApproximation.forcing_eq_finitePrincipal_of_height
    (P : N06NegativeGraphApproximation U G) (D : ReferenceData) (s : Finset ℕ)
    (hvalue : (U : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      r11bFiniteSynthesis s P.modes referenceAngularBasis)
    (hweak : ∀ φ, CanonicalTest S K m φ →
      (∫ p, U p * n06NegativePrincipalTest φ p ∂canonicalMeasure S K m) =
        ∫ p, G p * φ p ∂canonicalMeasure S K m) :
    (G : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => n06FiniteMixedField s P.modes 2 0 p -
        p.1 * n06FiniteMixedField s P.modes 0 2 p := by
  let f : PolarPoint → ℝ := fun p => n06FiniteMixedField s P.modes 2 0 p -
    p.1 * n06FiniteMixedField s P.modes 0 2 p
  have hf : MemLp f 2 (canonicalMeasure S K m) := P.finite_principal_memLp s
  let H : CanonicalL2 S K m := hf.toLp f
  have hH : (H : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] f := hf.coeFn_toLp
  have he : G = H := by
    apply n06_canonicalL2_test_ext
    intro φ hφ
    calc
      (∫ p, G p * φ p ∂canonicalMeasure S K m) =
          ∫ p, U p * n06NegativePrincipalTest φ p ∂canonicalMeasure S K m :=
        (hweak φ hφ).symm
      _ = ∫ p, r11bFiniteSynthesis s P.modes referenceAngularBasis p *
          n06NegativePrincipalTest φ p ∂canonicalMeasure S K m := by
        apply integral_congr_ae
        filter_upwards [hvalue] with p hp
        rw [hp]
      _ = ∫ p, f p * φ p ∂canonicalMeasure S K m := P.finite_principal_weak D s hφ
      _ = ∫ p, H p * φ p ∂canonicalMeasure S K m := by
        apply integral_congr_ae
        filter_upwards [hH] with p hp
        rw [hp]
  have hGH : (G : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] (H : PolarPoint → ℝ) :=
    Eventually.of_forall (fun p => congrArg (fun v : CanonicalL2 S K m => v p) he)
  exact hGH.trans hH

end ContinuousFlexibility.Analysis
