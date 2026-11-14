module

public import ContinuousFlexibility.Analysis.OneHighCylinderCompositionL2
public import ContinuousFlexibility.Analysis.OneHighCylinderVectorProducts
public import ContinuousFlexibility.Analysis.OneHighCircleVectorProducts

/-!
# Finite-energy derivatives of multivariable cylinder compositions

The actual vector derivative products supply every lower output derivative
through a single finite high order. Both membership and the norm estimate
are conclusions, so no output integrability is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal BigOperators ContDiff

variable {P : ℝ} [Fact (0 < P)] {m : ℕ}

/-- The vector input has finite energy whenever all its actual components
do, with the corresponding finite-sum norm bound. -/
theorem cylinder_vector_l2_le_components
    (u : CylinderSmoothJet P (Fin m → ℝ))
    (hu2 : ∀ i, MemLp ((u.component i).jet 0 0) 2 (cylinderPhysicalMeasure P)) :
    MemLp (u.jet 0 0) 2 (cylinderPhysicalMeasure P) ∧
      (eLpNorm (u.jet 0 0) 2 (cylinderPhysicalMeasure P)).toReal ≤
        ∑ i, (eLpNorm ((u.component i).jet 0 0) 2
          (cylinderPhysicalMeasure P)).toReal := by
  classical
  have hpoint (p : ℝ × AddCircle P) :
      ‖u.jet 0 0 p‖ ≤ ∑ i, (1 : ℝ) * ‖(u.component i).jet 0 0 p‖ := by
    simpa only [one_mul, CylinderSmoothJet.component_jet] using
      norm_pi_le_sum_norm (u.jet 0 0 p)
  have h := oneHigh_l2_finite_domination
    (μ := cylinderPhysicalMeasure P) (g := u.jet 0 0)
    (u.continuous 0 0).aestronglyMeasurable
    (fun i => (u.component i).jet 0 0) hu2
    (fun _ => (1 : ℝ)) (fun _ => zero_le_one) (Eventually.of_forall hpoint)
  exact ⟨h.1, by simpa only [one_mul] using h.2⟩

/-- Either positive pure derivative is controlled by the same finite input
Sobolev order. The outer derivatives are genuine multilinear derivatives. -/
theorem cylinder_vector_composition_pure_l2_le
    (u : CylinderSmoothJet P (Fin m → ℝ))
    (hu2 : ∀ i, MemLp ((u.component i).jet 0 0) 2 (cylinderPhysicalMeasure P))
    {s : ℕ} (hs : ∀ i, (u.component i).MemRealSobolev s (hu2 i))
    (hF1 : ∀ i, MemLp
      (cylinderFourier (cylinderComplexify ((u.component i).jet 0 0))
        (continuous_cylinderComplexify ((u.component i).continuous 0 0))
        (cylinderComplexify_memLp ((u.component i).continuous 0 0) (hu2 i)))
      1 cylinderFrequencyMeasure)
    (Φ : (Fin m → ℝ) → ℝ)
    (hΦ : ∀ p, ContDiffAt ℝ ∞ Φ (u.jet 0 0 p))
    {k : ℕ} (hk : 0 < k) (hks : k ≤ s) (radial : Bool)
    {R : ℝ} (hR0 : 0 ≤ R) {B : ℕ → ℝ} (hB0 : ∀ n, 0 ≤ B n)
    (hB : ∀ p n, 1 ≤ n → n ≤ k →
      ‖iteratedFDeriv ℝ n Φ (u.jet 0 0 p)‖ ≤ B n)
    (hR : ∀ i, cylinderRealFourierL1Norm
      ((u.component i).jet 0 0) ((u.component i).continuous 0 0) (hu2 i) ≤ R) :
    MemLp (cylinderPureDerivative (cylinderComposition u Φ) radial k)
        2 (cylinderPhysicalMeasure P) ∧
      (eLpNorm (cylinderPureDerivative (cylinderComposition u Φ) radial k)
        2 (cylinderPhysicalMeasure P)).toReal ≤
      circleVectorCompositionCoefficient m k R B *
        ∑ i, cylinderRealSobolevNorm s ((u.component i).jet 0 0)
          ((u.component i).continuous 0 0) (hu2 i) := by
  classical
  let H := ∑ i, cylinderRealSobolevNorm s ((u.component i).jet 0 0)
    ((u.component i).continuous 0 0) (hu2 i)
  let A (c : OrderedFinpartition k) :=
    (m : ℝ) ^ c.length * (c.length : ℝ) * R ^ (c.length - 1) * H
  have hp (c : OrderedFinpartition k) :
      MemLp (fun p => ∏ j,
        ‖u.jet (if radial then c.partSize j else 0)
          (if radial then 0 else c.partSize j) p‖) 2 (cylinderPhysicalMeasure P) ∧
      (eLpNorm (fun p => ∏ j,
        ‖u.jet (if radial then c.partSize j else 0)
          (if radial then 0 else c.partSize j) p‖) 2 (cylinderPhysicalMeasure P)).toReal ≤ A c := by
    let a : Fin c.length → ℕ := fun j => if radial then c.partSize j else 0
    let b : Fin c.length → ℕ := fun j => if radial then 0 else c.partSize j
    have hab : ∑ j, (a j + b j) ≤ s := by
      cases radial <;> simpa [a, b] using (oneHighPartition_sum_orders c).le.trans hks
    exact cylinder_vector_derivative_product_le u hu2 hs hF1
      (c.length_pos hk) a b hab hR0 hR
  have hD := cylinder_composition_pure_l2_of_product_bounds u Φ hΦ hk radial hB0 hB A hp
  refine ⟨hD.1, hD.2.trans_eq ?_⟩
  simp only [circleVectorCompositionCoefficient, Finset.sum_mul, A]
  apply Finset.sum_congr rfl
  intro c _
  ring

end ContinuousFlexibility.Analysis
