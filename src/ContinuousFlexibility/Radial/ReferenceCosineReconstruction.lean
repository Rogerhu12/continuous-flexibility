module

public import ContinuousFlexibility.Radial.ReferenceCosineAnalysis
public import ContinuousFlexibility.Radial.ReferenceCosineRepresentative

/-!
# Reconstruction in the actual physical L² space

The tensor/source inner product is computed by Fubini as the actual
radial coefficient pairing. Applying it to the convergent synthesized
series and using Parseval proves that analysis followed by synthesis
equals the original L² vector. Thus reconstruction is a conclusion.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

def referencePhysicalCosineTensor (g : Lp ℝ 2 μ) (n : ℕ) :
    Lp ℝ 2 (μ.prod referenceAngularMeasure) :=
  referenceCirclePullback (referenceL2Tensor g (referenceCircleCosineLp n))

theorem referencePhysicalCosineTensor_ae (g : Lp ℝ 2 μ) (n : ℕ) :
    referencePhysicalCosineTensor g n =ᵐ[μ.prod referenceAngularMeasure]
      fun x : α × ℝ => g x.1 * referenceCircleCosine n (x.2 : AddCircle Real.pi) := by
  have ht := (referenceCircleProduct_measurePreserving (μ := μ)).quasiMeasurePreserving.ae
    (referenceL2Tensor_ae g (referenceCircleCosineLp n))
  have hc := referenceCircle_measurePreserving.quasiMeasurePreserving.ae
    (referenceCircleCosineLp_ae n)
  have hcp := (Measure.quasiMeasurePreserving_snd (μ := μ)
    (ν := referenceAngularMeasure)).ae hc
  filter_upwards [referenceCirclePullback_ae
    (referenceL2Tensor g (referenceCircleCosineLp n)), ht, hcp] with x hp ht hc
  change referenceCirclePullback (referenceL2Tensor g (referenceCircleCosineLp n)) x =
    referenceL2Tensor g (referenceCircleCosineLp n) (x.1, (x.2 : AddCircle Real.pi)) at hp
  change referenceL2Tensor g (referenceCircleCosineLp n) (x.1, (x.2 : AddCircle Real.pi)) =
    g x.1 * referenceCircleCosineLp n (x.2 : AddCircle Real.pi) at ht
  change referenceCircleCosineLp n (x.2 : AddCircle Real.pi) =
    referenceCircleCosine n (x.2 : AddCircle Real.pi) at hc
  change referenceCirclePullback (referenceL2Tensor g (referenceCircleCosineLp n)) x = _
  rw [hp, ht, hc]

/-- The synthesis as a linear isometry into the true physical product space. -/
def referencePhysicalCosineL2Synthesis :
    lp (fun _ : ℕ => Lp ℝ 2 μ) 2 →ₗᵢ[ℝ] Lp ℝ 2 (μ.prod referenceAngularMeasure) :=
  (referenceCirclePullback (μ := μ)).comp referenceCosineL2Synthesis

theorem referencePhysicalCosineL2Synthesis_hasSum
    (a : lp (fun _ : ℕ => Lp ℝ 2 μ) 2) :
    HasSum (fun n => referencePhysicalCosineTensor (a n) n)
      (referencePhysicalCosineL2Synthesis a) :=
  (referenceCosineL2Synthesis_hasSum a).mapL
    (referenceCirclePullback (μ := μ)).toContinuousLinearMap

theorem referencePhysicalCosineL2Synthesis_norm_sq
    (a : lp (fun _ : ℕ => Lp ℝ 2 μ) 2) :
    ‖referencePhysicalCosineL2Synthesis a‖ ^ 2 = ∑' n, ‖a n‖ ^ 2 := by
  change ‖referenceCirclePullback (referenceCosineL2Synthesis a)‖ ^ 2 = _
  rw [referenceCirclePullback_norm, referenceCosineL2Synthesis_norm_sq]

/-- The genuine product-test integral is the radial coefficient pairing. -/
theorem referencePhysicalCosineTensor_inner {f : α × ℝ → ℝ}
    (hf : MemLp f 2 (μ.prod referenceAngularMeasure))
    (hp : ∀ r, Function.Periodic (fun θ => f (r, θ)) Real.pi)
    (he : ∀ r θ, f (r, -θ) = f (r, θ))
    (g : Lp ℝ 2 μ) (n : ℕ) :
    ⟪referencePhysicalCosineTensor g n, hf.toLp f⟫_ℝ =
      ⟪g, referenceCosineAnalysisCoeff hf hp he n⟫_ℝ := by
  have ha :
      (fun x : α × ℝ =>
        ⟪referencePhysicalCosineTensor g n x, hf.toLp f x⟫_ℝ) =ᵐ[μ.prod referenceAngularMeasure]
      fun x => g x.1 * (f x * referenceCircleCosine n (x.2 : AddCircle Real.pi)) := by
    filter_upwards [referencePhysicalCosineTensor_ae g n, hf.coeFn_toLp] with x ht hx
    simp only [Real.inner_apply, ht, hx]
    ring
  have hi : Integrable
      (fun x : α × ℝ => g x.1 * (f x * referenceCircleCosine n (x.2 : AddCircle Real.pi)))
      (μ.prod referenceAngularMeasure) :=
    (L2.integrable_inner (𝕜 := ℝ)
      (referencePhysicalCosineTensor g n) (hf.toLp f)).congr ha
  calc
    _ = ∫ x : α × ℝ,
        g x.1 * (f x * referenceCircleCosine n (x.2 : AddCircle Real.pi))
        ∂μ.prod referenceAngularMeasure := by
      rw [L2.inner_def]
      exact integral_congr_ae ha
    _ = ∫ r, ∫ θ,
        g r * (f (r, θ) * referenceCircleCosine n (θ : AddCircle Real.pi))
        ∂referenceAngularMeasure ∂μ := integral_prod _ hi
    _ = ∫ r, g r * referenceCosineCoefficient f n r ∂μ := by
      simp only [integral_const_mul, referenceCosineCoefficient, referenceCosineCoeff]
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [referenceCosineAnalysisCoeff_ae hf hp he n] with r hr
      simp only [Real.inner_apply, hr]

theorem referencePhysicalCosineL2Synthesis_analysis_inner {f : α × ℝ → ℝ}
    (hf : MemLp f 2 (μ.prod referenceAngularMeasure))
    (hp : ∀ r, Function.Periodic (fun θ => f (r, θ)) Real.pi)
    (he : ∀ r θ, f (r, -θ) = f (r, θ)) :
    ⟪hf.toLp f, referencePhysicalCosineL2Synthesis (referenceCosineAnalysis hf hp he)⟫_ℝ =
      ‖hf.toLp f‖ ^ 2 := by
  have hs := (referencePhysicalCosineL2Synthesis_hasSum
    (referenceCosineAnalysis hf hp he)).mapL (innerSL ℝ (hf.toLp f))
  have hterm (n : ℕ) :
      ⟪hf.toLp f,
        referencePhysicalCosineTensor (referenceCosineAnalysis hf hp he n) n⟫_ℝ =
        ‖referenceCosineAnalysisCoeff hf hp he n‖ ^ 2 := by
    change ⟪hf.toLp f,
      referencePhysicalCosineTensor (referenceCosineAnalysisCoeff hf hp he n) n⟫_ℝ = _
    rw [real_inner_comm, referencePhysicalCosineTensor_inner hf hp he,
      real_inner_self_eq_norm_sq]
  have hs' : HasSum (fun n : ℕ => ‖referenceCosineAnalysisCoeff hf hp he n‖ ^ 2)
      ⟪hf.toLp f,
        referencePhysicalCosineL2Synthesis (referenceCosineAnalysis hf hp he)⟫_ℝ := by
    simpa only [innerSL_apply_apply, hterm] using hs
  exact hs'.unique (referenceCosineAnalysisCoeff_hasSum_norm_sq hf hp he)

/-- Actual L² reconstruction, proved from the coefficient pairings and energy identity. -/
theorem referencePhysicalCosineL2Synthesis_analysis {f : α × ℝ → ℝ}
    (hf : MemLp f 2 (μ.prod referenceAngularMeasure))
    (hp : ∀ r, Function.Periodic (fun θ => f (r, θ)) Real.pi)
    (he : ∀ r θ, f (r, -θ) = f (r, θ)) :
    referencePhysicalCosineL2Synthesis (referenceCosineAnalysis hf hp he) = hf.toLp f := by
  have hn :
      ‖referencePhysicalCosineL2Synthesis (referenceCosineAnalysis hf hp he)‖ ^ 2 =
      ‖hf.toLp f‖ ^ 2 := by
    rw [referencePhysicalCosineL2Synthesis_norm_sq, referenceCosineAnalysis_tsum_norm_sq]
  have hz : ‖hf.toLp f -
      referencePhysicalCosineL2Synthesis (referenceCosineAnalysis hf hp he)‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, referencePhysicalCosineL2Synthesis_analysis_inner hf hp he, hn]
    ring
  exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))).symm

/-- The pointwise even, periodic physical representative reconstructs the source almost everywhere. -/
theorem referenceCosineRepresentative_analysis_ae {f : α × ℝ → ℝ}
    (hf : MemLp f 2 (μ.prod referenceAngularMeasure))
    (hp : ∀ r, Function.Periodic (fun θ => f (r, θ)) Real.pi)
    (he : ∀ r θ, f (r, -θ) = f (r, θ)) :
    referenceCosineRepresentative (referenceCosineAnalysis hf hp he) =ᵐ[μ.prod referenceAngularMeasure] f := by
  have hr := referenceCosineRepresentative_ae (referenceCosineAnalysis hf hp he)
  have heq := referencePhysicalCosineL2Synthesis_analysis hf hp he
  change referenceCirclePullback
    (referenceCosineL2Synthesis (referenceCosineAnalysis hf hp he)) = hf.toLp f at heq
  rw [heq] at hr
  exact hr.trans hf.coeFn_toLp

end ContinuousFlexibility.Statements
