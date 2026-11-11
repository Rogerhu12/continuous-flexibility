import ContinuousFlexibility.Analysis.OneHighCylinderRealProducts
import ContinuousFlexibility.Analysis.OneHighCircleComponents
import ContinuousFlexibility.Analysis.OneHighL2Domination

/-!
# Products of actual vector derivative norms on the full cylinder

Expansion over finitely many component choices reduces the norm products
to the same scalar one-high estimate. Membership is proved from the finite
majorant, so no product-integrability hypothesis is added.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal BigOperators

variable {P : ℝ} [Fact (0 < P)] {m : ℕ}

theorem cylinder_vector_derivative_product_le
    (u : CylinderSmoothJet P (Fin m → ℝ))
    (hu2 : ∀ i, MemLp ((u.component i).jet 0 0) 2 (cylinderPhysicalMeasure P))
    {s : ℕ} (hs : ∀ i, (u.component i).MemRealSobolev s (hu2 i))
    (hF1 : ∀ i, MemLp
      (cylinderFourier (cylinderComplexify ((u.component i).jet 0 0))
        (continuous_cylinderComplexify ((u.component i).continuous 0 0))
        (cylinderComplexify_memLp ((u.component i).continuous 0 0) (hu2 i)))
      1 cylinderFrequencyMeasure)
    {k : ℕ} (hk : 0 < k) (a b : Fin k → ℕ)
    (hab : ∑ j, (a j + b j) ≤ s) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ i, cylinderRealFourierL1Norm
      ((u.component i).jet 0 0) ((u.component i).continuous 0 0) (hu2 i) ≤ R) :
    MemLp (fun p => ∏ j, ‖u.jet (a j) (b j) p‖) 2 (cylinderPhysicalMeasure P) ∧
      (eLpNorm (fun p => ∏ j, ‖u.jet (a j) (b j) p‖) 2
        (cylinderPhysicalMeasure P)).toReal ≤
      (m : ℝ) ^ k * (k : ℝ) * R ^ (k - 1) *
        ∑ i, cylinderRealSobolevNorm s ((u.component i).jet 0 0)
          ((u.component i).continuous 0 0) (hu2 i) := by
  classical
  let Q (sel : Fin k → Fin m) (p : ℝ × AddCircle P) : ℝ :=
    ∏ j, u.jet (a j) (b j) p (sel j)
  let H := ∑ i, cylinderRealSobolevNorm s ((u.component i).jet 0 0)
    ((u.component i).continuous 0 0) (hu2 i)
  have hQ (sel : Fin k → Fin m) :
      MemLp (Q sel) 2 (cylinderPhysicalMeasure P) ∧
        (eLpNorm (Q sel) 2 (cylinderPhysicalMeasure P)).toReal ≤
          (k : ℝ) * R ^ (k - 1) * H := by
    exact cylinder_real_selected_derivative_product_le
      (fun i => u.component i) hu2 hs hF1 hk sel a b hab hR0 hR
  have hc : Continuous (fun p : ℝ × AddCircle P => ∏ j, ‖u.jet (a j) (b j) p‖) :=
    continuous_finsetProd _ fun j _ => (u.continuous (a j) (b j)).norm
  have hpoint (p : ℝ × AddCircle P) :
      ‖∏ j, ‖u.jet (a j) (b j) p‖‖ ≤ ∑ sel : Fin k → Fin m, 1 * ‖Q sel p‖ := by
    rw [Real.norm_of_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)]
    simp only [one_mul, Q, norm_prod]
    calc
      _ ≤ ∏ j, ∑ i : Fin m, ‖u.jet (a j) (b j) p i‖ :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun j _ => norm_pi_le_sum_norm (u.jet (a j) (b j) p))
      _ = _ := Fintype.prod_sum (fun (j : Fin k) (i : Fin m) => ‖u.jet (a j) (b j) p i‖)
  have hD := oneHigh_l2_finite_domination hc.aestronglyMeasurable Q
    (fun sel => (hQ sel).1) (fun _ => (1 : ℝ)) (fun _ => zero_le_one)
    (Eventually.of_forall hpoint)
  refine ⟨hD.1, hD.2.trans ?_⟩
  calc
    _ ≤ ∑ _sel : Fin k → Fin m, (k : ℝ) * R ^ (k - 1) * H := by
      apply Finset.sum_le_sum
      intro sel _
      simpa only [one_mul] using (hQ sel).2
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
      ring

end ContinuousFlexibility.Analysis
