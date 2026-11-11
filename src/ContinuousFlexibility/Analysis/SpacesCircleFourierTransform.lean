import ContinuousFlexibility.Analysis.SpacesCircleFourierProjection

/-!
# The normalized angular Fourier isometry

The factor `sqrt π` converts the normalized Fourier coefficient convention
to the unnormalized angular `L²` norm used throughout the physical spaces.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ENNReal ComplexConjugate ContDiff

private instance circleFourierTransform_period_pos : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

private instance circleFourierTransform_finite : IsFiniteMeasure angleMeasure :=
  ⟨by
    rw [angleMeasure, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
    exact ENNReal.ofReal_lt_top⟩

private theorem integrable_circleFourierWave_mul {f : ℝ → ℝ}
    (hf : MemLp f 2 angleMeasure) (n : ℤ) :
    Integrable (fun θ => circleFourierWave n θ * (f θ : ℂ)) angleMeasure := by
  have hfC : MemLp (fun θ => (f θ : ℂ)) 2 angleMeasure := hf.ofReal
  have hi := (hfC.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).bdd_smul 1
    (circleFourierWave_contDiff n).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ => (circleFourierWave_norm n θ).le)
  change Integrable (fun θ => circleFourierWave n θ • (f θ : ℂ)) angleMeasure at hi
  simpa only [smul_eq_mul] using hi

theorem circleFourierCoeff_add {f g : ℝ → ℝ}
    (hf : MemLp f 2 angleMeasure) (hg : MemLp g 2 angleMeasure) (n : ℤ) :
    circleFourierCoeff (f + g) n = circleFourierCoeff f n + circleFourierCoeff g n := by
  rw [circleFourierCoeff_integral (f + g) n, circleFourierCoeff_integral f n,
    circleFourierCoeff_integral g n, ← mul_add,
    ← integral_add (integrable_circleFourierWave_mul hf (-n))
      (integrable_circleFourierWave_mul hg (-n))]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ => by
    simp only [Pi.add_apply, Complex.ofReal_add, mul_add]

theorem circleFourierCoeff_smul (f : ℝ → ℝ) (c : ℝ) (n : ℤ) :
    circleFourierCoeff (c • f) n = c • circleFourierCoeff f n := by
  have heq : (fun θ => ((c • f) θ : ℂ)) = (c : ℂ) • (fun θ => (f θ : ℂ)) := by
    funext θ
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  unfold circleFourierCoeff
  rw [heq, fourierCoeffOn.const_smul]
  simp only [smul_eq_mul, Complex.real_smul]

/-- The square-summable Fourier coefficients of an angular `L²` class. -/
def circleFourierCoefficients (f : AngleL2) : lp (fun _ : ℤ => ℂ) 2 :=
  ⟨circleFourierCoeff f, memℓp_gen (by
    have hpow (x : ℝ) : x ^ (2 : ℝ≥0∞).toReal = x ^ (2 : ℕ) := by norm_cast
    simpa only [hpow] using (circleFourierCoeff_hasSum_sq f).summable)⟩

theorem circleFourierCoefficients_apply (f : AngleL2) (n : ℤ) :
    circleFourierCoefficients f n = circleFourierCoeff f n := rfl

theorem circleFourierCoefficients_add (f g : AngleL2) :
    circleFourierCoefficients (f + g) = circleFourierCoefficients f + circleFourierCoefficients g := by
  apply lp.ext
  funext n
  change circleFourierCoeff (f + g : AngleL2) n = circleFourierCoeff f n + circleFourierCoeff g n
  exact (congrFun (circleFourierCoeff_congr_ae (Lp.coeFn_add f g)) n).trans
    (circleFourierCoeff_add (Lp.memLp f) (Lp.memLp g) n)

theorem circleFourierCoefficients_smul (c : ℝ) (f : AngleL2) :
    circleFourierCoefficients (c • f) = c • circleFourierCoefficients f := by
  apply lp.ext
  funext n
  change circleFourierCoeff (c • f : AngleL2) n = c • circleFourierCoeff f n
  exact (congrFun (circleFourierCoeff_congr_ae (Lp.coeFn_smul c f)) n).trans
    (circleFourierCoeff_smul f c n)

theorem circleFourierCoefficients_norm_sq (f : AngleL2) :
    ‖circleFourierCoefficients f‖ ^ 2 = Real.pi⁻¹ * ‖f‖ ^ 2 := by
  have hpow (x : ℝ) : x ^ (2 : ℝ≥0∞).toReal = x ^ (2 : ℕ) := by norm_cast
  have h : HasSum (fun n => ‖circleFourierCoeff f n‖ ^ 2) (‖circleFourierCoefficients f‖ ^ 2) := by
    simpa only [hpow, circleFourierCoefficients_apply] using
      lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (circleFourierCoefficients f)
  exact h.unique (circleFourierCoeff_hasSum_sq f)

private theorem circleFourierTransform_norm (f : AngleL2) :
    ‖Real.sqrt Real.pi • circleFourierCoefficients f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg f)).mp
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt Real.pi_pos.le, circleFourierCoefficients_norm_sq]
  rw [← mul_assoc, mul_inv_cancel₀ Real.pi_ne_zero, one_mul]

/-- The Fourier transform is a real linear isometry into the complex sequence
Hilbert space; realness is retained by conjugate symmetry. -/
def circleFourierTransform : AngleL2 →ₗᵢ[ℝ] lp (fun _ : ℤ => ℂ) 2 where
  toFun f := Real.sqrt Real.pi • circleFourierCoefficients f
  map_add' := by
    intro f g
    rw [circleFourierCoefficients_add, smul_add]
  map_smul' := by
    intro c f
    rw [circleFourierCoefficients_smul, smul_comm]
    rfl
  norm_map' := circleFourierTransform_norm

theorem circleFourierTransform_apply (f : AngleL2) (n : ℤ) :
    circleFourierTransform f n = Real.sqrt Real.pi • circleFourierCoeff f n := rfl

theorem circleFourierCoeff_injective {f g : AngleL2}
    (h : circleFourierCoeff f = circleFourierCoeff g) : f = g := by
  apply circleFourierTransform.injective
  apply lp.ext
  funext n
  exact congrArg (Real.sqrt Real.pi • ·) (congrFun h n)

end ContinuousFlexibility.Statements
