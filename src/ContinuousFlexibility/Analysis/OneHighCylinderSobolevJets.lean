import ContinuousFlexibility.Analysis.OneHighCylinderSobolevJetsBasic
import ContinuousFlexibility.Analysis.OneHighCylinderFourierReverseDerivative
import ContinuousFlexibility.Analysis.OneHighCylinderDerivativeMultiplier

/-!
# Finite Sobolev regularity of actual mixed jets

Starting with only the base function in physical L2 and its actual Hs
frequency membership, induction proves L2 membership of every actual mixed
derivative of total order at most s. The exact physical multiplier and the
derivative L2 bound are proved at the same time.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal

variable {P : ℝ} [Fact (0 < P)]

private theorem CylinderSmoothJet.exists_memLp_fourier_derivative
    (u : CylinderSmoothJet P)
    (hu2 : MemLp (u.jet 0 0) 2 (cylinderPhysicalMeasure P))
    {s : ℕ} (hs : u.MemSobolev s hu2) :
    ∀ i j : ℕ, i + j ≤ s →
      ∃ hij2 : MemLp (u.jet i j) 2 (cylinderPhysicalMeasure P),
        cylinderFourier (u.jet i j) (u.continuous i j) hij2 =ᵐ[cylinderFrequencyMeasure]
          fun ζ => cylinderDerivativeMultiplier P i j ζ *
            cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2 ζ := by
  let F := cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2
  have hF : Measurable F := measurable_cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2
  intro i
  induction i with
  | zero =>
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨hu2, Eventually.of_forall (fun ζ => ?_)⟩
      simp only [cylinderDerivativeMultiplier_zero_zero, one_mul]
    | succ j ih =>
      intro hij
      obtain ⟨hj2, hje⟩ := ih (by omega)
      have hnext : MemLp (fun ζ => cylinderDerivativeMultiplier P 0 (j + 1) ζ * F ζ)
          2 cylinderFrequencyMeasure :=
        cylinderDerivativeMultiplier_mul_memLp hF hij hs
      have hMeq : (fun ζ : ℝ × ℤ =>
          (Complex.I * (circlePhysicalFrequency P ζ.2 : ℂ)) *
            cylinderFourier (u.jet 0 j) (u.continuous 0 j) hj2 ζ) =ᵐ[cylinderFrequencyMeasure]
          fun ζ => cylinderDerivativeMultiplier P 0 (j + 1) ζ * F ζ := by
        filter_upwards [hje] with ζ hζ
        rw [hζ, cylinderDerivativeMultiplier_angular_succ]
        simp only [circlePhysicalFrequency, mul_assoc]
      have hM2 := (memLp_congr_ae hMeq).mpr hnext
      have hnew : MemLp (u.jet 0 (j + 1)) 2 (cylinderPhysicalMeasure P) :=
        cylinder_memLp_angularDerivative_of_frequency (u.jet 0 j) (u.jet 0 (j + 1))
          (u.continuous 0 j) (u.continuous 0 (j + 1)) hj2 (u.angular 0 j) hM2
      refine ⟨hnew, ?_⟩
      exact (cylinderFourier_angularDerivative_ae (u.jet 0 j) (u.jet 0 (j + 1))
        (u.continuous 0 j) (u.continuous 0 (j + 1)) hj2 hnew (u.angular 0 j)).trans hMeq
  | succ i ih =>
    intro j hij
    obtain ⟨hij2, hije⟩ := ih j (by omega)
    have hnext : MemLp (fun ζ => cylinderDerivativeMultiplier P (i + 1) j ζ * F ζ)
        2 cylinderFrequencyMeasure :=
      cylinderDerivativeMultiplier_mul_memLp hF hij hs
    have hMeq : (fun ζ : ℝ × ℤ =>
        (2 * Real.pi * Complex.I) * (ζ.1 : ℂ) *
          cylinderFourier (u.jet i j) (u.continuous i j) hij2 ζ) =ᵐ[cylinderFrequencyMeasure]
        fun ζ => cylinderDerivativeMultiplier P (i + 1) j ζ * F ζ := by
      filter_upwards [hije] with ζ hζ
      rw [hζ, cylinderDerivativeMultiplier_radial_succ]
      simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
      ring
    have hM2 := (memLp_congr_ae hMeq).mpr hnext
    have hnew : MemLp (u.jet (i + 1) j) 2 (cylinderPhysicalMeasure P) :=
      cylinder_memLp_radialDerivative_of_frequency (u.jet i j) (u.jet (i + 1) j)
        (u.continuous i j) (u.continuous (i + 1) j) hij2
        (fun θ r => u.radial i j r θ) hM2
    refine ⟨hnew, ?_⟩
    exact (cylinderFourier_radialDerivative_ae (u.jet i j) (u.jet (i + 1) j)
      (u.continuous i j) (u.continuous (i + 1) j) hij2 hnew
      (fun θ r => u.radial i j r θ)).trans hMeq

/-- Actual derivative membership follows from finite-order Sobolev membership. -/
theorem CylinderSmoothJet.memLp_derivative (u : CylinderSmoothJet P)
    (hu2 : MemLp (u.jet 0 0) 2 (cylinderPhysicalMeasure P))
    {s i j : ℕ} (hs : u.MemSobolev s hu2) (hij : i + j ≤ s) :
    MemLp (u.jet i j) 2 (cylinderPhysicalMeasure P) :=
  (u.exists_memLp_fourier_derivative hu2 hs i j hij).choose

/-- The actual derivative transform has the physical mixed multiplier. -/
theorem CylinderSmoothJet.fourier_derivative_ae (u : CylinderSmoothJet P)
    (hu2 : MemLp (u.jet 0 0) 2 (cylinderPhysicalMeasure P))
    {s i j : ℕ} (hs : u.MemSobolev s hu2) (hij : i + j ≤ s) :
    cylinderFourier (u.jet i j) (u.continuous i j)
      (u.memLp_derivative hu2 hs hij) =ᵐ[cylinderFrequencyMeasure]
      fun ζ => cylinderDerivativeMultiplier P i j ζ *
        cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2 ζ :=
  (u.exists_memLp_fourier_derivative hu2 hs i j hij).choose_spec

theorem CylinderSmoothJet.derivative_eLpNorm_two_le (u : CylinderSmoothJet P)
    (hu2 : MemLp (u.jet 0 0) 2 (cylinderPhysicalMeasure P))
    {s i j : ℕ} (hs : u.MemSobolev s hu2) (hij : i + j ≤ s) :
    eLpNorm (u.jet i j) 2 (cylinderPhysicalMeasure P) ≤
      eLpNorm (frequencyWeighted
        (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ)
        (cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2)) 2 cylinderFrequencyMeasure := by
  have hij2 := u.memLp_derivative hu2 hs hij
  calc
    _ = eLpNorm (cylinderFourier (u.jet i j) (u.continuous i j) hij2)
        2 cylinderFrequencyMeasure :=
      (cylinderFourier_eLpNorm_two (u.jet i j) (u.continuous i j) hij2).symm
    _ = eLpNorm (fun ζ => cylinderDerivativeMultiplier P i j ζ *
        cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2 ζ) 2 cylinderFrequencyMeasure :=
      eLpNorm_congr_ae (u.fourier_derivative_ae hu2 hs hij)
    _ ≤ _ := by
      apply eLpNorm_mono_ae
        ((measurable_cylinderDerivativeMultiplier P i j).mul
          (measurable_cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2)).aestronglyMeasurable
      exact Eventually.of_forall fun ζ => by
        simp only [Pi.mul_apply]
        rw [norm_mul, cylinder_norm_frequencyWeighted_nat]
        exact mul_le_mul_of_nonneg_right
          (norm_cylinderDerivativeMultiplier_le_weight P i j s hij ζ) (norm_nonneg _)

theorem CylinderSmoothJet.derivative_l2_le_sobolev (u : CylinderSmoothJet P)
    (hu2 : MemLp (u.jet 0 0) 2 (cylinderPhysicalMeasure P))
    {s i j : ℕ} (hs : u.MemSobolev s hu2) (hij : i + j ≤ s) :
    (eLpNorm (u.jet i j) 2 (cylinderPhysicalMeasure P)).toReal ≤
      cylinderSobolevNorm s (u.jet 0 0) (u.continuous 0 0) hu2 := by
  have htop : eLpNorm (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ)
      (cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2))
      2 cylinderFrequencyMeasure ≠ ⊤ := by
    exact (show MemLp (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) (s : ℝ)
      (cylinderFourier (u.jet 0 0) (u.continuous 0 0) hu2))
      2 cylinderFrequencyMeasure from hs).ne
  exact ENNReal.toReal_mono htop (u.derivative_eLpNorm_two_le hu2 hs hij)

end ContinuousFlexibility.Analysis
