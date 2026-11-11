import ContinuousFlexibility.Analysis.N04bNearIdentityLift
import ContinuousFlexibility.Analysis.N04bFourierCorrector

/-!
# A quantitative first-order translation-number estimate

An explicit Fourier conjugacy removes the nonconstant first variation.
The remaining actual conjugacy defect is bounded uniformly by
|q| η + q² L (|c|+|a|+|b|+η). Comparison with translations gives the same
bound for the physical translation number. No regularity of the
translation-number functional is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

def n04bFourierRemainderBound (T a b c q η : ℝ) : ℝ :=
  |q| * η + q ^ 2 * n04bFourierLipschitz T a b *
    (|c| + |a| + |b| + η)

/-- The actual near-identity conjugacy defect, before any use of
translation numbers. The remainder assumption is uniform in angle. -/
theorem n04bFourier_conjugacy_defect
    {T : ℝ} (hT : Real.sin T ≠ 0) (a b c q η : ℝ) (F : ℝ → ℝ)
    (hrem : ∀ θ : ℝ,
      |F θ - θ - T - q * (c + n04bSecondHarmonic a b θ)| ≤ |q| * η)
    (θ : ℝ) :
    |(F θ + q * n04bFourierCorrector T a b (F θ)) -
        (θ + q * n04bFourierCorrector T a b θ) - T - q * c| ≤
      n04bFourierRemainderBound T a b c q η := by
  let M : ℝ := |c| + |a| + |b|
  let L : ℝ := n04bFourierLipschitz T a b
  have hL : 0 ≤ L := n04bFourierLipschitz_nonneg T a b
  have hc : |c + n04bSecondHarmonic a b θ| ≤ M := by
    calc
      _ ≤ |c| + |n04bSecondHarmonic a b θ| := abs_add_le _ _
      _ ≤ |c| + (|a| + |b|) := add_le_add_left (n04bSecondHarmonic_abs_le a b θ) _
      _ = M := by dsimp only [M]; ring
  have hd : |F θ - (θ + T)| ≤ |q| * (M + η) := by
    calc
      _ = |(F θ - θ - T - q * (c + n04bSecondHarmonic a b θ)) +
          q * (c + n04bSecondHarmonic a b θ)| := by congr 1; ring
      _ ≤ |F θ - θ - T - q * (c + n04bSecondHarmonic a b θ)| +
          |q| * |c + n04bSecondHarmonic a b θ| := by
        simpa only [abs_mul] using
          abs_add_le (F θ - θ - T - q * (c + n04bSecondHarmonic a b θ))
            (q * (c + n04bSecondHarmonic a b θ))
      _ ≤ |q| * η + |q| * M :=
        add_le_add (hrem θ) (mul_le_mul_of_nonneg_left hc (abs_nonneg q))
      _ = _ := by ring
  have hco := n04bFourierCorrector_difference hT a b θ
  have he :
      (F θ + q * n04bFourierCorrector T a b (F θ)) -
          (θ + q * n04bFourierCorrector T a b θ) - T - q * c =
        (F θ - θ - T - q * (c + n04bSecondHarmonic a b θ)) +
          q * (n04bFourierCorrector T a b (F θ) -
            n04bFourierCorrector T a b (θ + T)) := by
    linear_combination q * hco
  rw [he]
  calc
    _ ≤ |F θ - θ - T - q * (c + n04bSecondHarmonic a b θ)| +
        |q| * |n04bFourierCorrector T a b (F θ) -
          n04bFourierCorrector T a b (θ + T)| := by
      simpa only [abs_mul] using
        abs_add_le (F θ - θ - T - q * (c + n04bSecondHarmonic a b θ))
          (q * (n04bFourierCorrector T a b (F θ) -
            n04bFourierCorrector T a b (θ + T)))
    _ ≤ |q| * η + |q| * (L * |F θ - (θ + T)|) :=
      add_le_add (hrem θ) (mul_le_mul_of_nonneg_left
        (n04bFourierCorrector_lipschitz T a b (F θ) (θ + T)) (abs_nonneg q))
    _ ≤ |q| * η + |q| * (L * (|q| * (M + η))) :=
      add_le_add_left
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd hL) (abs_nonneg q)) _
    _ = |q| * η + |q| ^ 2 * L * (M + η) := by ring
    _ = n04bFourierRemainderBound T a b c q η := by
      rw [sq_abs]
      rfl

/-- Physical translation-number comparison for an actual period-one lift
whose physical realization has the stated uniform remainder. -/
theorem n04b_physicalTranslationNumber_fourier_bound
    (f : CircleDeg1Lift) {T : ℝ} (hT : Real.sin T ≠ 0) (a b c q η : ℝ)
    (hsmall : |q| * n04bFourierLipschitz T a b < 1)
    (hrem : ∀ θ : ℝ,
      |n04bPhysicalLift f θ - θ - T -
        q * (c + n04bSecondHarmonic a b θ)| ≤ |q| * η) :
    |n04bPhysicalTranslationNumber f - T - q * c| ≤
      n04bFourierRemainderBound T a b c q η := by
  let H : CircleDeg1Liftˣ :=
    n04bNearIdentityUnit q (n04bFourierLipschitz T a b)
      (n04bUnitFourierCorrector T a b)
      (n04bUnitFourierCorrector_periodic T a b)
      (n04bUnitFourierCorrector_lipschitz T a b) hsmall
      (n04bUnitFourierCorrector_continuous T a b)
  have hH (x : ℝ) : H x = x + q * n04bUnitFourierCorrector T a b x :=
    n04bNearIdentityUnit_apply _ _ _ _ _ _ _ x
  have hdef : ∀ x : ℝ, |H (f x) - H x - (T + q * c) / Real.pi| ≤
      n04bFourierRemainderBound T a b c q η / Real.pi := by
    intro x
    have hp := n04bFourier_conjugacy_defect hT a b c q η
      (n04bPhysicalLift f) hrem (Real.pi * x)
    simp only [n04bPhysicalLift_pi] at hp
    have he : H (f x) - H x - (T + q * c) / Real.pi =
        ((Real.pi * f x + q * n04bFourierCorrector T a b (Real.pi * f x)) -
          (Real.pi * x + q * n04bFourierCorrector T a b (Real.pi * x)) -
          T - q * c) / Real.pi := by
      rw [hH (f x), hH x]
      dsimp only [n04bUnitFourierCorrector]
      field_simp [Real.pi_ne_zero]
      <;> ring
    rw [he, abs_div, abs_of_pos Real.pi_pos]
    exact div_le_div_of_nonneg_right hp Real.pi_pos.le
  have hn := n04b_translationNumber_bound_of_conjugacy_defect f H
    ((T + q * c) / Real.pi) (n04bFourierRemainderBound T a b c q η / Real.pi) hdef
  have he : n04bPhysicalTranslationNumber f - T - q * c =
      Real.pi * (f.translationNumber - (T + q * c) / Real.pi) := by
    dsimp only [n04bPhysicalTranslationNumber]
    field_simp [Real.pi_ne_zero]
    <;> ring
  rw [he, abs_mul, abs_of_pos Real.pi_pos]
  calc
    _ ≤ Real.pi * (n04bFourierRemainderBound T a b c q η / Real.pi) :=
      mul_le_mul_of_nonneg_left hn Real.pi_pos.le
    _ = _ := by field_simp [Real.pi_ne_zero]

end ContinuousFlexibility.Analysis
