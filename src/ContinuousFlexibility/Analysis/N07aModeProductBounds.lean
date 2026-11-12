import ContinuousFlexibility.Analysis.N07aCanonicalModeLinear
import ContinuousFlexibility.Analysis.N07aCylinderWeightedNorms

/-!
# Weighted L² bounds for the actual mode products

Pointwise bounds on the genuine circle multiplication entries pass to
the actual interval L² classes. The resulting weights are precisely
those controlled by the positive weak mode energy.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements ContinuousFlexibility.Radial

theorem n07a_interval_norm_le_weight (v u : N07aIntervalL2) (p : ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1),
      |v x| ≤ M * cylinderWeight x ^ p * |u x|) :
    ‖v‖ ≤ M * ‖n07aCylinderPower p u‖ := by
  have hb : ‖v‖ ≤ ‖M • n07aCylinderPower p u‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [h, n07aCylinderPower_ae p u,
      Lp.coeFn_smul M (n07aCylinderPower p u), ae_restrict_mem measurableSet_Ioo]
      with x hx hp hs hxi
    simp only [Real.norm_eq_abs, hs, Pi.smul_apply, smul_eq_mul, hp,
      abs_mul, abs_of_nonneg hM,
      abs_of_nonneg (pow_nonneg (cylinderWeight_nonneg (Ioo_subset_Icc_self hxi)) p)]
    simpa only [mul_assoc] using hx
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hM] using hb

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07aCanonicalProduct_cosine_norm_le (hm : K.left m < K.right m)
    (χ : N07aCanonicalOpenCoefficient S K m) (u : CanonicalL2 S K m)
    (hu : n07aAngularReflection m u = u) (j l p : ℕ)
    (hb : n07aAngularBand m hm j u = u) {κ M : ℝ} (hM : 0 ≤ M)
    (hrow : ∀ x ∈ Ioo (0 : ℝ) 1,
      |κ * n07aCosineMatrixEntry
        (fun θ => χ.value (n07aIntervalUnitMap (K.left m) (K.right m) x, θ)) l j| ≤
          M * cylinderWeight x ^ p) :
    ‖κ • n07aCanonicalUnitMode hm (χ.mul u) l‖ ≤
      M * ‖n07aCylinderPower p (n07aCanonicalUnitMode hm u j)‖ := by
  apply n07a_interval_norm_le_weight _ _ p hM
  filter_upwards [n07aCanonicalProduct_cosine_unitMode hm χ u hu j l hb,
    Lp.coeFn_smul κ (n07aCanonicalUnitMode hm (χ.mul u) l),
    ae_restrict_mem measurableSet_Ioo] with x hx hs hxi
  rw [hs, Pi.smul_apply, smul_eq_mul, hx]
  calc
    _ = |κ * n07aCosineMatrixEntry
        (fun θ => χ.value (n07aIntervalUnitMap (K.left m) (K.right m) x, θ)) l j| *
          |n07aCanonicalUnitMode hm u j x| := by rw [← abs_mul]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hrow x hxi) (abs_nonneg _)

theorem n07aCanonicalProduct_sine_norm_le (hm : K.left m < K.right m)
    (χ : N07aCanonicalOpenCoefficient S K m) (u d : CanonicalL2 S K m)
    (hu : n07aAngularReflection m u = u) (j l p : ℕ)
    (hb : n07aAngularBand m hm j u = u)
    (hd : N07aWeakCanonicalMixedDerivative S K m u d 0 1)
    {κ M : ℝ} (hM : 0 ≤ M)
    (hrow : ∀ x ∈ Ioo (0 : ℝ) 1,
      |κ * n07aSineMatrixEntry
        (fun θ => χ.value (n07aIntervalUnitMap (K.left m) (K.right m) x, θ)) l j| ≤
          M * cylinderWeight x ^ p) :
    ‖κ • n07aCanonicalUnitMode hm (χ.mul d) l‖ ≤
      (2 * (j : ℝ)) * M * ‖n07aCylinderPower p (n07aCanonicalUnitMode hm u j)‖ := by
  apply n07a_interval_norm_le_weight _ _ p (mul_nonneg (by positivity) hM)
  filter_upwards [n07aCanonicalProduct_sine_unitMode hm χ u d hu j l hb hd,
    Lp.coeFn_smul κ (n07aCanonicalUnitMode hm (χ.mul d) l),
    ae_restrict_mem measurableSet_Ioo] with x hx hs hxi
  rw [hs, Pi.smul_apply, smul_eq_mul, hx]
  calc
    _ = (2 * (j : ℝ)) * |κ * n07aSineMatrixEntry
        (fun θ => χ.value (n07aIntervalUnitMap (K.left m) (K.right m) x, θ)) l j| *
          |n07aCanonicalUnitMode hm u j x| := by
      simp only [abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg j : 0 ≤ (j : ℝ)),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hrow x hxi) (by positivity : 0 ≤ 2 * (j : ℝ)))
        (abs_nonneg (n07aCanonicalUnitMode hm u j x))
      simpa only [mul_assoc] using h

theorem n07aCylinderPower_norm_antitone {p q : ℕ} (hpq : p ≤ q)
    (u : N07aIntervalL2) : ‖n07aCylinderPower q u‖ ≤ ‖n07aCylinderPower p u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [n07aCylinderPower_norm_sq, n07aCylinderPower_norm_sq]
  exact n07aCylinderSquare_antitone (by omega) u

theorem n07aCylinderEnergy_root_norms (j : ℝ) (u d dd : N07aIntervalL2) :
    ‖n07aCylinderPower 3 dd‖ ≤ Real.sqrt (n07aCylinderEnergy j u d dd) ∧
    ‖n07aCylinderPower 2 d‖ ≤ Real.sqrt (n07aCylinderEnergy j u d dd) ∧
    j * ‖n07aCylinderPower 3 d‖ ≤ Real.sqrt (n07aCylinderEnergy j u d dd) ∧
    j * ‖n07aCylinderPower 2 u‖ ≤ Real.sqrt (n07aCylinderEnergy j u d dd) ∧
    j ^ 2 * ‖n07aCylinderPower 3 u‖ ≤ Real.sqrt (n07aCylinderEnergy j u d dd) := by
  obtain ⟨h₀, h₁, h₂, h₃, h₄⟩ := n07aCylinderEnergy_weighted_norms j u d dd
  exact ⟨Real.le_sqrt_of_sq_le h₀, Real.le_sqrt_of_sq_le h₁,
    Real.le_sqrt_of_sq_le (by simpa only [mul_pow] using h₂),
    Real.le_sqrt_of_sq_le (by simpa only [mul_pow] using h₃),
    Real.le_sqrt_of_sq_le (by simpa only [mul_pow, ← pow_mul] using h₄)⟩

end ContinuousFlexibility.Analysis
