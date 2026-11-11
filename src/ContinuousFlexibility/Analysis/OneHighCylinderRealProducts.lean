import ContinuousFlexibility.Analysis.OneHighCylinderRealSobolev
import ContinuousFlexibility.Analysis.OneHighCylinderDerivativeProducts

/-!
# The actual derivative-product estimate for real cylinder functions

Canonical complexification transfers the full finite-Sobolev estimate to real
functions. Repeated inputs and selected components retain explicit constants
depending only on the prescribed Fourier L¹ bound.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal BigOperators

variable {P : ℝ} [Fact (0 < P)]

theorem cylinder_real_derivative_product_oneHigh (k s : ℕ)
    (u : Fin (k + 1) → CylinderSmoothJet P ℝ)
    (hu2 : ∀ i, MemLp ((u i).jet 0 0) 2 (cylinderPhysicalMeasure P))
    (hs : ∀ i, (u i).MemRealSobolev s (hu2 i))
    (hF1 : ∀ i, MemLp
      (cylinderFourier (cylinderComplexify ((u i).jet 0 0))
        (continuous_cylinderComplexify ((u i).continuous 0 0))
        (cylinderComplexify_memLp ((u i).continuous 0 0) (hu2 i)))
      1 cylinderFrequencyMeasure)
    (a b : Fin (k + 1) → ℕ) (hab : ∑ i, (a i + b i) ≤ s) :
    MemLp (fun p => ∏ i, (u i).jet (a i) (b i) p) 2 (cylinderPhysicalMeasure P) ∧
      (eLpNorm (fun p => ∏ i, (u i).jet (a i) (b i) p) 2
        (cylinderPhysicalMeasure P)).toReal ≤
      ∑ j, cylinderRealSobolevNorm s ((u j).jet 0 0) ((u j).continuous 0 0) (hu2 j) *
        ∏ i ∈ Finset.univ.erase j,
          cylinderRealFourierL1Norm ((u i).jet 0 0) ((u i).continuous 0 0) (hu2 i) := by
  classical
  have h := cylinder_derivative_product_oneHigh k s (fun i => (u i).complexify)
    (fun i => cylinderComplexify_memLp ((u i).continuous 0 0) (hu2 i))
    hs hF1 a b hab
  have hr : Continuous (fun p : ℝ × AddCircle P => ∏ i, (u i).jet (a i) (b i) p) :=
    continuous_finsetProd _ fun i _ => (u i).continuous (a i) (b i)
  have hc : Continuous (fun p : ℝ × AddCircle P =>
      ∏ i, (u i).complexify.jet (a i) (b i) p) :=
    continuous_finsetProd _ fun i _ => (u i).complexify.continuous (a i) (b i)
  have hn (p : ℝ × AddCircle P) :
      ‖∏ i, (u i).complexify.jet (a i) (b i) p‖ =
        ‖∏ i, (u i).jet (a i) (b i) p‖ := by
    simp [norm_prod]
  have hm : MemLp (fun p => ∏ i, (u i).jet (a i) (b i) p)
      2 (cylinderPhysicalMeasure P) :=
    h.1.of_le hr.aestronglyMeasurable (Eventually.of_forall fun p => (hn p).symm.le)
  have he : eLpNorm (fun p => ∏ i, (u i).complexify.jet (a i) (b i) p)
      2 (cylinderPhysicalMeasure P) =
      eLpNorm (fun p => ∏ i, (u i).jet (a i) (b i) p) 2 (cylinderPhysicalMeasure P) :=
    eLpNorm_congr_norm_ae hc.aestronglyMeasurable hr.aestronglyMeasurable
      (Eventually.of_forall hn)
  refine ⟨hm, ?_⟩
  have hb := h.2
  rw [he] at hb
  refine hb.trans_eq ?_
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg₂ (fun x y : ℝ => x * y) rfl
    (Finset.prod_congr rfl fun i _ => rfl)

/-- Repeating the same physical input in any positive number of factors. -/
theorem cylinder_real_repeated_derivative_product_le
    (u : CylinderSmoothJet P ℝ)
    (hu2 : MemLp (u.jet 0 0) 2 (cylinderPhysicalMeasure P))
    {s : ℕ} (hs : u.MemRealSobolev s hu2)
    (hF1 : MemLp
      (cylinderFourier (cylinderComplexify (u.jet 0 0))
        (continuous_cylinderComplexify (u.continuous 0 0))
        (cylinderComplexify_memLp (u.continuous 0 0) hu2))
      1 cylinderFrequencyMeasure)
    {m : ℕ} (hm : 0 < m) (a b : Fin m → ℕ)
    (hab : ∑ i, (a i + b i) ≤ s) {R : ℝ}
    (hR : cylinderRealFourierL1Norm (u.jet 0 0) (u.continuous 0 0) hu2 ≤ R) :
    MemLp (fun p => ∏ i, u.jet (a i) (b i) p) 2 (cylinderPhysicalMeasure P) ∧
      (eLpNorm (fun p => ∏ i, u.jet (a i) (b i) p) 2
        (cylinderPhysicalMeasure P)).toReal ≤
      (m : ℝ) * R ^ (m - 1) *
        cylinderRealSobolevNorm s (u.jet 0 0) (u.continuous 0 0) hu2 := by
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have h := cylinder_real_derivative_product_oneHigh k s (fun _ => u)
    (fun _ => hu2) (fun _ => hs) (fun _ => hF1) a b hab
  refine ⟨h.1, h.2.trans ?_⟩
  have hp (j : Fin (k + 1)) :
      (∏ _i ∈ Finset.univ.erase j,
        cylinderRealFourierL1Norm (u.jet 0 0) (u.continuous 0 0) hu2) ≤ R ^ k := by
    calc
      _ ≤ ∏ _i ∈ Finset.univ.erase j, R :=
        Finset.prod_le_prod₀ (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ => hR)
      _ = _ := by simp
  calc
    _ ≤ ∑ _j : Fin (k + 1),
        cylinderRealSobolevNorm s (u.jet 0 0) (u.continuous 0 0) hu2 * R ^ k :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hp j) ENNReal.toReal_nonneg
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.succ_eq_add_one, Nat.add_sub_cancel]
      ring

/-- An arbitrary component selection in a genuine derivative product. -/
theorem cylinder_real_selected_derivative_product_le {m : ℕ}
    (u : Fin m → CylinderSmoothJet P ℝ)
    (hu2 : ∀ i, MemLp ((u i).jet 0 0) 2 (cylinderPhysicalMeasure P))
    {s : ℕ} (hs : ∀ i, (u i).MemRealSobolev s (hu2 i))
    (hF1 : ∀ i, MemLp
      (cylinderFourier (cylinderComplexify ((u i).jet 0 0))
        (continuous_cylinderComplexify ((u i).continuous 0 0))
        (cylinderComplexify_memLp ((u i).continuous 0 0) (hu2 i)))
      1 cylinderFrequencyMeasure)
    {k : ℕ} (hk : 0 < k) (sel : Fin k → Fin m)
    (a b : Fin k → ℕ) (hab : ∑ i, (a i + b i) ≤ s)
    {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ i, cylinderRealFourierL1Norm
      ((u i).jet 0 0) ((u i).continuous 0 0) (hu2 i) ≤ R) :
    MemLp (fun p => ∏ j, (u (sel j)).jet (a j) (b j) p) 2 (cylinderPhysicalMeasure P) ∧
      (eLpNorm (fun p => ∏ j, (u (sel j)).jet (a j) (b j) p) 2
        (cylinderPhysicalMeasure P)).toReal ≤
      (k : ℝ) * R ^ (k - 1) *
        ∑ i, cylinderRealSobolevNorm s ((u i).jet 0 0) ((u i).continuous 0 0) (hu2 i) := by
  classical
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  let H := ∑ i, cylinderRealSobolevNorm s ((u i).jet 0 0) ((u i).continuous 0 0) (hu2 i)
  have h := cylinder_real_derivative_product_oneHigh l s (fun j => u (sel j))
    (fun j => hu2 (sel j)) (fun j => hs (sel j)) (fun j => hF1 (sel j)) a b hab
  refine ⟨h.1, h.2.trans ?_⟩
  have hp (j : Fin (l + 1)) :
      (∏ i ∈ Finset.univ.erase j,
        cylinderRealFourierL1Norm ((u (sel i)).jet 0 0)
          ((u (sel i)).continuous 0 0) (hu2 (sel i))) ≤ R ^ l := by
    calc
      _ ≤ ∏ _i ∈ Finset.univ.erase j, R :=
        Finset.prod_le_prod₀ (fun _ _ => ENNReal.toReal_nonneg) (fun i _ => hR (sel i))
      _ = _ := by simp
  have hhigh (j : Fin (l + 1)) :
      cylinderRealSobolevNorm s ((u (sel j)).jet 0 0)
        ((u (sel j)).continuous 0 0) (hu2 (sel j)) ≤ H :=
    Finset.single_le_sum
      (f := fun i => cylinderRealSobolevNorm s ((u i).jet 0 0) ((u i).continuous 0 0) (hu2 i))
      (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ (sel j))
  calc
    _ ≤ ∑ _j : Fin (l + 1), H * R ^ l := by
      apply Finset.sum_le_sum
      intro j _
      exact (mul_le_mul_of_nonneg_left (hp j) ENNReal.toReal_nonneg).trans
        (mul_le_mul_of_nonneg_right (hhigh j) (pow_nonneg hR0 l))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.succ_eq_add_one, Nat.add_sub_cancel]
      ring

end ContinuousFlexibility.Analysis
