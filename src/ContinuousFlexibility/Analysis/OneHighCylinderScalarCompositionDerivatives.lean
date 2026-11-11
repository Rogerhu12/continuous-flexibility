import ContinuousFlexibility.Analysis.OneHighCylinderCompositionL2
import ContinuousFlexibility.Analysis.OneHighCylinderRealProducts
import ContinuousFlexibility.Analysis.OneHighCircleRepeatedProducts

/-!
# Finite-energy derivatives of scalar cylinder compositions

Every positive derivative through the fixed high order is controlled by
the same input H^s norm. This also supplies all lower derivative membership
needed by the actual Fourier endpoint comparison.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal BigOperators ContDiff

variable {P : ℝ} [Fact (0 < P)]

theorem cylinder_scalar_composition_pure_l2_le
    (u : CylinderSmoothJet P ℝ)
    (hu2 : MemLp (u.jet 0 0) 2 (cylinderPhysicalMeasure P))
    {s : ℕ} (hs : u.MemRealSobolev s hu2)
    (hF1 : MemLp
      (cylinderFourier (cylinderComplexify (u.jet 0 0))
        (continuous_cylinderComplexify (u.continuous 0 0))
        (cylinderComplexify_memLp (u.continuous 0 0) hu2))
      1 cylinderFrequencyMeasure)
    (Φ : ℝ → ℝ) (hΦ : ∀ p, ContDiffAt ℝ ∞ Φ (u.jet 0 0 p))
    {k : ℕ} (hk : 0 < k) (hks : k ≤ s) (radial : Bool)
    {R : ℝ} {B : ℕ → ℝ} (hB0 : ∀ n, 0 ≤ B n)
    (hB : ∀ p n, 1 ≤ n → n ≤ k → ‖iteratedDeriv n Φ (u.jet 0 0 p)‖ ≤ B n)
    (hR : cylinderRealFourierL1Norm (u.jet 0 0) (u.continuous 0 0) hu2 ≤ R) :
    MemLp (cylinderPureDerivative (cylinderComposition u Φ) radial k)
        2 (cylinderPhysicalMeasure P) ∧
      (eLpNorm (cylinderPureDerivative (cylinderComposition u Φ) radial k)
        2 (cylinderPhysicalMeasure P)).toReal ≤
      circleScalarCompositionCoefficient k R B *
        cylinderRealSobolevNorm s (u.jet 0 0) (u.continuous 0 0) hu2 := by
  classical
  let H := cylinderRealSobolevNorm s (u.jet 0 0) (u.continuous 0 0) hu2
  let A (c : OrderedFinpartition k) := (c.length : ℝ) * R ^ (c.length - 1) * H
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
    have h := cylinder_real_repeated_derivative_product_le u hu2 hs hF1
      (c.length_pos hk) a b hab hR
    let Q : ℝ × AddCircle P → ℝ := fun p => ∏ j, u.jet (a j) (b j) p
    have he : (fun p => ∏ j,
        ‖u.jet (if radial then c.partSize j else 0)
          (if radial then 0 else c.partSize j) p‖) = fun p => ‖Q p‖ := by
      funext p
      simp only [Q, a, b, norm_prod]
    constructor
    · rw [he]
      exact h.1.norm
    · rw [he, eLpNorm_norm Q h.1.aestronglyMeasurable]
      exact h.2
  have hBf (p : ℝ × AddCircle P) (n : ℕ) (hn : 1 ≤ n) (hnk : n ≤ k) :
      ‖iteratedFDeriv ℝ n Φ (u.jet 0 0 p)‖ ≤ B n := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hB p n hn hnk
  have hD := cylinder_composition_pure_l2_of_product_bounds u Φ hΦ hk radial hB0 hBf A hp
  refine ⟨hD.1, hD.2.trans_eq ?_⟩
  simp only [circleScalarCompositionCoefficient, Finset.sum_mul, A]
  apply Finset.sum_congr rfl
  intro c _
  ring

end ContinuousFlexibility.Analysis
