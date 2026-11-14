module

public import ContinuousFlexibility.Radial.ReferenceCosineReconstruction

/-!
# Pairing genuine cosine synthesis with arbitrary L² tests

The test need not be even or periodic. Its actual angular coefficients
arise from Fubini applied to the product of two L² functions. Applying
the continuous inner product functional to the convergent synthesis
then gives the full paired series.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

theorem referencePhysicalCosineTensor_pairing
    (g : Lp ℝ 2 μ) {ψ : α × ℝ → ℝ}
    (hψ : MemLp ψ 2 (μ.prod referenceAngularMeasure)) (n : ℕ) :
    ⟪referencePhysicalCosineTensor g n, hψ.toLp ψ⟫_ℝ =
      ∫ r, g r * referenceCosineCoefficient ψ n r ∂μ := by
  have ha :
      (fun x : α × ℝ =>
        ⟪referencePhysicalCosineTensor g n x, hψ.toLp ψ x⟫_ℝ) =ᵐ[μ.prod referenceAngularMeasure]
      fun x => g x.1 * (ψ x * referenceCircleCosine n (x.2 : AddCircle Real.pi)) := by
    filter_upwards [referencePhysicalCosineTensor_ae g n, hψ.coeFn_toLp] with x ht hx
    change referencePhysicalCosineTensor g n x =
      g x.1 * referenceCircleCosine n (x.2 : AddCircle Real.pi) at ht
    change hψ.toLp ψ x = ψ x at hx
    rw [Real.inner_apply, ht, hx]
    ring
  have hi : Integrable (fun x : α × ℝ =>
      g x.1 * (ψ x * referenceCircleCosine n (x.2 : AddCircle Real.pi)))
      (μ.prod referenceAngularMeasure) :=
    (L2.integrable_inner (𝕜 := ℝ)
      (referencePhysicalCosineTensor g n) (hψ.toLp ψ)).congr ha
  calc
    _ = ∫ x : α × ℝ, g x.1 * (ψ x * referenceCircleCosine n (x.2 : AddCircle Real.pi))
        ∂μ.prod referenceAngularMeasure := by
      rw [L2.inner_def]
      exact integral_congr_ae ha
    _ = ∫ r, ∫ θ, g r * (ψ (r, θ) * referenceCircleCosine n (θ : AddCircle Real.pi))
        ∂referenceAngularMeasure ∂μ := integral_prod _ hi
    _ = _ := by
      simp only [integral_const_mul, referenceCosineCoefficient, referenceCosineCoeff]

theorem referenceCosineRepresentative_pairing_hasSum
    (a : lp (fun _ : ℕ => Lp ℝ 2 μ) 2) {ψ : α × ℝ → ℝ}
    (hψ : MemLp ψ 2 (μ.prod referenceAngularMeasure)) :
    HasSum (fun n : ℕ => ∫ r, a n r * referenceCosineCoefficient ψ n r ∂μ)
      (∫ x, referenceCosineRepresentative a x * ψ x ∂μ.prod referenceAngularMeasure) := by
  have hs := (referencePhysicalCosineL2Synthesis_hasSum a).mapL (innerSL ℝ (hψ.toLp ψ))
  change HasSum (fun n => ⟪hψ.toLp ψ, referencePhysicalCosineTensor (a n) n⟫_ℝ)
    ⟪hψ.toLp ψ, referencePhysicalCosineL2Synthesis a⟫_ℝ at hs
  have hterm (n : ℕ) :
      ⟪hψ.toLp ψ, referencePhysicalCosineTensor (a n) n⟫_ℝ =
        ∫ r, a n r * referenceCosineCoefficient ψ n r ∂μ := by
    rw [real_inner_comm, referencePhysicalCosineTensor_pairing (a n) hψ n]
  have hpair :
      ⟪hψ.toLp ψ, referencePhysicalCosineL2Synthesis a⟫_ℝ =
        ∫ x, referenceCosineRepresentative a x * ψ x ∂μ.prod referenceAngularMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hψ.coeFn_toLp, referenceCosineRepresentative_ae a] with x hx hr
    change hψ.toLp ψ x = ψ x at hx
    change referenceCosineRepresentative a x = referencePhysicalCosineL2Synthesis a x at hr
    rw [Real.inner_apply, hx, ← hr]
    ring
  simpa only [hterm, hpair] using hs

/-- The same identity for the actual Fourier analysis of a physical field. -/
theorem referenceCosineAnalysis_pairing_hasSum {f ψ : α × ℝ → ℝ}
    (hf : MemLp f 2 (μ.prod referenceAngularMeasure))
    (hfp : ∀ r, Function.Periodic (fun θ => f (r, θ)) Real.pi)
    (hfe : ∀ r θ, f (r, -θ) = f (r, θ))
    (hψ : MemLp ψ 2 (μ.prod referenceAngularMeasure)) :
    HasSum (fun n : ℕ => ∫ r,
      referenceCosineCoefficient f n r * referenceCosineCoefficient ψ n r ∂μ)
      (∫ x, f x * ψ x ∂μ.prod referenceAngularMeasure) := by
  have hs := referenceCosineRepresentative_pairing_hasSum
    (referenceCosineAnalysis hf hfp hfe) hψ
  have hterms :
      (fun n : ℕ => ∫ r, referenceCosineAnalysis hf hfp hfe n r *
        referenceCosineCoefficient ψ n r ∂μ) =
      (fun n : ℕ => ∫ r, referenceCosineCoefficient f n r *
        referenceCosineCoefficient ψ n r ∂μ) := by
    funext n
    apply integral_congr_ae
    filter_upwards [referenceCosineAnalysisCoeff_ae hf hfp hfe n] with r hr
    change referenceCosineAnalysis hf hfp hfe n r = referenceCosineCoefficient f n r at hr
    rw [hr]
  have hpair :
      (∫ x, referenceCosineRepresentative (referenceCosineAnalysis hf hfp hfe) x * ψ x
        ∂μ.prod referenceAngularMeasure) =
      ∫ x, f x * ψ x ∂μ.prod referenceAngularMeasure := by
    apply integral_congr_ae
    filter_upwards [referenceCosineRepresentative_analysis_ae hf hfp hfe] with x hx
    rw [hx]
  rw [hterms, hpair] at hs
  exact hs

end ContinuousFlexibility.Statements
