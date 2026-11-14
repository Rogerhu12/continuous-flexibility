module

public import ContinuousFlexibility.Radial.ZeroModeWeightedHeight
public import ContinuousFlexibility.Radial.ReferenceZeroModeBorderCorrection

/-!
# The actual weighted zero-mode solution

For every source in the frozen radial weighted space with the required
mean-zero condition, the existing two integral primitives give the
solution. The output uses the actual smooth left border, and the estimate
includes its actual coefficient. All constants are common to the entire
exponent interval [0,1].
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real Filter MeasureTheory
open scoped ENNReal ContDiff
open ContinuousFlexibility.Statements

theorem zeroMode_weighted_solution
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D) :
    ∃ Mstar K : ℝ, 0 < Mstar ∧ 0 < K ∧
      ∀ M₀ M₁ γ : ℝ, Mstar ≤ M₀ → 0 ≤ M₁ → γ ∈ Icc (0 : ℝ) 1 →
      ∀ f : ℝ → ℝ,
      MemLp f 2 (referenceRadialWeightedMeasure D γ M₀) →
      IntervalIntegrable f volume D.a D.b → (∫ t in D.a..D.b, f t) = 0 →
      IntervalIntegrable (fun s => zeroModeFlux D.a f s / D.w s) volume D.a D.b ∧
      MemLp (fun r => zeroModeHeight D.a D.b D.w f r -
        zeroModeHeight D.a D.b D.w f D.a * D.chiLeft r) 2
        (referenceRadialWeightedMeasure D γ (-M₁)) ∧
      (zeroModeHeight D.a D.b D.w f D.a) ^ 2 +
        (∫ r, (zeroModeHeight D.a D.b D.w f r -
          zeroModeHeight D.a D.b D.w f D.a * D.chiLeft r) ^ 2
          ∂referenceRadialWeightedMeasure D γ (-M₁)) ≤
        K * ∫ t, f t ^ 2 ∂referenceRadialWeightedMeasure D γ M₀ ∧
      ContDiffOn ℝ 1 (zeroModeHeight D.a D.b D.w f) (radialCore D) ∧
      zeroModeHeight D.a D.b D.w f D.b = 0 ∧
      ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → tsupport ψ ⊆ radialCore D →
        (∫ r in D.a..D.b, zeroModeHeight D.a D.b D.w f r * radialJacobi 0 D.w ψ r) =
          ∫ r in D.a..D.b, f r * ψ r := by
  obtain ⟨C, hC⟩ := hD
  obtain ⟨Mstar, Kh, hMstar, hKh, hheight⟩ := zeroMode_weighted_endpoint_height hC
  obtain ⟨B, hB, hcorrection⟩ := referenceZeroModeBorderCorrection_uniform_bound ⟨C, hC⟩ hborder
  refine ⟨Mstar, (3 + 2 * B) * Kh, hMstar, by positivity, ?_⟩
  intro M₀ M₁ γ hM₀ hM₁ hγ f hf hfi hmean
  obtain ⟨hqi, hHmem, hHenergy⟩ := hheight M₀ M₁ γ hM₀ hM₁ hγ f hf hfi hmean
  obtain ⟨hβmem, hβenergy⟩ := hcorrection γ hγ M₁ hM₁
  let U : ℝ → ℝ := zeroModeHeight D.a D.b D.w f
  let aL : ℝ := U D.a
  let H : ℝ → ℝ := fun r => U r - aL * (if r ≤ (D.a + D.b) / 2 then 1 else 0)
  let β : ℝ → ℝ := referenceZeroModeBorderCorrection D
  let R : ℝ → ℝ := fun r => U r - aL * D.chiLeft r
  let μ : Measure ℝ := referenceRadialWeightedMeasure D γ (-M₁)
  have hR (r : ℝ) : H r + aL * β r = R r := by
    dsimp only [H, β, R, referenceZeroModeBorderCorrection]
    ring
  have hRmem : MemLp R 2 μ := by
    have hs : MemLp (fun r => H r + aL * β r) 2 μ :=
      hHmem.add (hβmem.const_mul aL)
    exact hs.ae_eq (ae_of_all _ hR)
  have hmajor : (∫ r, (R r) ^ 2 ∂μ) ≤
      2 * (∫ r, (H r) ^ 2 ∂μ) + (2 * aL ^ 2) * (∫ r, (β r) ^ 2 ∂μ) := by
    calc
      _ ≤ ∫ r, 2 * (H r) ^ 2 + (2 * aL ^ 2) * (β r) ^ 2 ∂μ := by
        apply integral_mono_ae hRmem.integrable_sq
          ((hHmem.integrable_sq.const_mul 2).add
            (hβmem.integrable_sq.const_mul (2 * aL ^ 2)))
        exact ae_of_all _ (fun r => by
          change (R r) ^ 2 ≤ 2 * (H r) ^ 2 + (2 * aL ^ 2) * (β r) ^ 2
          rw [← hR r]
          nlinarith only [sq_nonneg (H r - aL * β r)])
      _ = _ := by
        rw [integral_add (hHmem.integrable_sq.const_mul 2)
          (hβmem.integrable_sq.const_mul (2 * aL ^ 2)),
          integral_const_mul, integral_const_mul]
  have hH0 : 0 ≤ ∫ r, (H r) ^ 2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have hβscaled :
      (2 * aL ^ 2) * (∫ r, (β r) ^ 2 ∂μ) ≤ (2 * aL ^ 2) * B :=
    mul_le_mul_of_nonneg_left hβenergy (mul_nonneg (by norm_num) (sq_nonneg aL))
  have hsumscaled :
      (3 + 2 * B) * (aL ^ 2 + ∫ r, (H r) ^ 2 ∂μ) ≤
        (3 + 2 * B) *
          (Kh * ∫ t, f t ^ 2 ∂referenceRadialWeightedMeasure D γ M₀) :=
    mul_le_mul_of_nonneg_left hHenergy (by positivity)
  have hbound : aL ^ 2 + (∫ r, (R r) ^ 2 ∂μ) ≤
      ((3 + 2 * B) * Kh) *
        ∫ t, f t ^ 2 ∂referenceRadialWeightedMeasure D γ M₀ := by
    have hrest : 0 ≤ (1 + 2 * B) * (∫ r, (H r) ^ 2 ∂μ) :=
      mul_nonneg (by positivity) hH0
    nlinarith only [hmajor, hβscaled, hsumscaled, hrest, sq_nonneg aL]
  refine ⟨hqi, hRmem, hbound, ?_, ?_, ?_⟩
  · exact zeroModeHeight_contDiffOn_one_of_integrable hC.1.2.2.1.1.continuous.continuousOn
      (fun r hr => (hC.1.2.2.2.2.1 r hr).ne') hfi hqi
  · simp only [zeroModeHeight, intervalIntegral.integral_same, neg_zero]
  · intro ψ hψ hψs
    exact zeroModeHeight_weak_radialJacobi hC.1.2.1 hC.1.2.2.1.1
      (fun r hr => (hC.1.2.2.2.2.1 r hr).ne') hfi hqi hψ hψs

end ContinuousFlexibility.Radial
