module

public import ContinuousFlexibility.Analysis.N04bLiftTranslationBounds
public import ContinuousFlexibility.Analysis.N04bRotationBounds
public import ContinuousFlexibility.Analysis.N04bFourierCorrector

/-!
# A quantitative first-order translation-number estimate

An explicit bounded Fourier corrector removes the nonconstant first
variation. Its displacement defect is bounded uniformly by
|q| η + q² L (|c|+|a|+|b|+η). Orbit telescoping gives the same bound for
the actual physical translation number. The corrector need not be an
invertible coordinate change, so no smallness condition on q is needed.
-/

@[expose] public section

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
  have hc (x : ℝ) : |c + n04bSecondHarmonic a b x| ≤ M := by
    calc
      _ ≤ |c| + |n04bSecondHarmonic a b x| := abs_add_le _ _
      _ ≤ |c| + (|a| + |b|) := add_le_add le_rfl (n04bSecondHarmonic_abs_le a b x)
      _ = M := by dsimp only [M]; ring
  have he :
      (F θ + q * n04bFourierCorrector T a b (F θ)) -
          (θ + q * n04bFourierCorrector T a b θ) - T - q * c =
        (F θ + q * n04bFourierCorrector T a b (F θ)) -
          (θ + q * n04bFourierCorrector T a b θ) - (T + q * c) := by ring
  rw [he]
  exact n04b_bounded_corrector_displacement F (n04bFourierCorrector T a b)
    (n04bSecondHarmonic a b) T c q η M (n04bFourierLipschitz T a b)
    (n04bFourierLipschitz_nonneg T a b) hc
    (n04bFourierCorrector_lipschitz T a b)
    (n04bFourierCorrector_difference hT a b) hrem θ

/-- Physical translation-number comparison for an actual period-one lift
whose physical realization has the stated uniform remainder. -/
theorem n04b_physicalTranslationNumber_fourier_bound
    (f : CircleDeg1Lift) {T : ℝ} (hT : Real.sin T ≠ 0) (a b c q η : ℝ)
    (hrem : ∀ θ : ℝ,
      |n04bPhysicalLift f θ - θ - T -
        q * (c + n04bSecondHarmonic a b θ)| ≤ |q| * η) :
    |n04bPhysicalTranslationNumber f - T - q * c| ≤
      n04bFourierRemainderBound T a b c q η := by
  let H : ℝ → ℝ := fun x => x + q * n04bUnitFourierCorrector T a b x
  let B : ℝ := (|n04bFourierCosCoeff T a b| + |n04bFourierSinCoeff T a b|) / Real.pi
  have hH (x : ℝ) : H x = x + q * n04bUnitFourierCorrector T a b x := rfl
  have hB (x : ℝ) : |H x - x| ≤ |q| * B := by
    rw [hH, add_sub_cancel_left, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg q)
    dsimp only [n04bUnitFourierCorrector, B]
    rw [abs_div, abs_of_pos Real.pi_pos]
    exact div_le_div_of_nonneg_right
      (n04bFourierCorrector_abs_le T a b (Real.pi * x)) Real.pi_pos.le
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
  have hn := n04b_translationNumber_bound_of_bounded_corrector f H (|q| * B)
    ((T + q * c) / Real.pi) (n04bFourierRemainderBound T a b c q η / Real.pi) hB hdef
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
