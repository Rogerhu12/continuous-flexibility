import ContinuousFlexibility.Scalar.WeightedAngularPrimitive
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Mixed weighted jets of angular primitives

Radial derivatives commute with the actual angular integral.  A positive
number of angular derivatives removes that integral.  The same identities
hold after the material pullback and multiplication by its radial weights.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

private theorem iteratedDeriv_intervalIntegral_parameter_of_le
    {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {a b : ℝ} (hab : a ≤ b)
    (n : ℕ) (r : ℝ) :
    iteratedDeriv n (fun s => ∫ t in a..b, f (s, t)) r =
      ∫ t in a..b, iteratedDeriv n (fun s => f (s, t)) r := by
  simp only [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  simpa only [iteratedDeriv_eq_iteratedFDeriv] using
    iteratedFDeriv_compactIntegral_parameter_apply (μ := volume)
      (O := univ) (K := Icc a b) isOpen_univ isCompact_Icc
      (fun _ _ _ _ => hf.contDiffAt) n (p := r) (mem_univ r) (fun _ => 1)

/-- Differentiation in the radial parameter commutes with either orientation
of the fixed angular interval. -/
theorem iteratedDeriv_intervalIntegral_parameter
    {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) (a b r : ℝ) :
    iteratedDeriv n (fun s => ∫ t in a..b, f (s, t)) r =
      ∫ t in a..b, iteratedDeriv n (fun s => f (s, t)) r := by
  rcases le_total a b with hab | hba
  · exact iteratedDeriv_intervalIntegral_parameter_of_le hf hab n r
  · have hreverse : (fun s => ∫ t in a..b, f (s, t)) =
        fun s => -(∫ t in b..a, f (s, t)) := by
      funext s
      exact intervalIntegral.integral_symm _ _
    rw [hreverse, iteratedDeriv_neg,
      iteratedDeriv_intervalIntegral_parameter_of_le hf hba,
      intervalIntegral.integral_symm]

theorem mixedDerivative_scalarAngularPrimitive_zero {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (a : ℕ) :
    mixedDerivative a 0 (scalarAngularPrimitive f) =
      scalarAngularPrimitive (mixedDerivative a 0 f) := by
  funext p
  simp only [mixedDerivative, iteratedDeriv_zero, scalarAngularPrimitive]
  exact iteratedDeriv_intervalIntegral_parameter hf a 0 p.2 p.1

theorem mixedDerivative_scalarAngularPrimitive_succ {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (a b : ℕ) :
    mixedDerivative a (b + 1) (scalarAngularPrimitive f) = mixedDerivative a b f := by
  have hd (r : ℝ) : deriv (fun t => scalarAngularPrimitive f (r, t)) =
      fun t => f (r, t) := by
    funext t
    exact (hasDerivAt_scalarAngularPrimitive_angular hf.continuous r t).deriv
  funext p
  simp only [mixedDerivative, iteratedDeriv_succ', hd]

theorem weightedPhysicalJet_scalarAngularPrimitive_zero
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hf : ContDiff ℝ ∞ f) (a c : ℕ) :
    weightedPhysicalJet T γ a 0 c (scalarAngularPrimitive f) =
      scalarAngularPrimitive (weightedPhysicalJet T γ a 0 c f) := by
  have hg : ContDiff ℝ ∞ (materialPullback T γ f) :=
    contDiff_materialPullback hT hf.contDiffOn
  funext p
  simp only [weightedPhysicalJet, materialPullback_scalarAngularPrimitive,
    mixedDerivative_scalarAngularPrimitive_zero hg, scalarAngularPrimitive,
    intervalIntegral.integral_const_mul]

theorem weightedPhysicalJet_scalarAngularPrimitive_succ
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hf : ContDiff ℝ ∞ f) (a b c : ℕ) :
    weightedPhysicalJet T γ a (b + 1) c (scalarAngularPrimitive f) =
      weightedPhysicalJet T γ a b c f := by
  have hg : ContDiff ℝ ∞ (materialPullback T γ f) :=
    contDiff_materialPullback hT hf.contDiffOn
  funext p
  simp only [weightedPhysicalJet, materialPullback_scalarAngularPrimitive,
    mixedDerivative_scalarAngularPrimitive_succ hg]

end ContinuousFlexibility.Statements
