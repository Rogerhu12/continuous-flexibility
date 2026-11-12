import ContinuousFlexibility.Statements.Radial
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Angular integrals of genuine closed side jets

Continuity and differentiation of angular pairings use only continuity on the
closed side rectangle and the true derivative strictly inside that side.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

private theorem n07a_trace_angularSection_continuousOn
    {l r : ℝ} {G : PolarPoint → ℝ}
    (hG : ContinuousOn G (Icc l r ×ˢ Icc (0 : ℝ) (2 * Real.pi)))
    {x : ℝ} (hx : x ∈ Icc l r) :
    ContinuousOn (fun θ => G (x, θ)) (Icc (0 : ℝ) (2 * Real.pi)) :=
  hG.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ hθ => ⟨hx, hθ⟩)

/-- A normalized angular pairing of a continuous closed side jet remains
continuous all the way to both radial endpoints. -/
theorem n07a_closedAngularIntegral_continuousOn
    {l r : ℝ} {W : PolarPoint → ℝ}
    (hW : ContinuousOn W (Icc l r ×ˢ Icc (0 : ℝ) (2 * Real.pi)))
    {β : ℝ → ℝ} (hβ : Continuous β) :
    ContinuousOn (fun x => radialAngularMean (fun θ => W (x, θ) * β θ))
      (Icc l r) := by
  let G : PolarPoint → ℝ := fun p => W p * β p.2
  have hG : ContinuousOn G (Icc l r ×ˢ Icc (0 : ℝ) (2 * Real.pi)) :=
    hW.mul (hβ.comp continuous_snd).continuousOn
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hG
  have hT : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  intro x hx
  have hi : ContinuousWithinAt
      (fun y => ∫ θ in (0 : ℝ)..2 * Real.pi, G (y, θ)) (Icc l r) x := by
    apply intervalIntegral.continuousWithinAt_of_dominated_interval
      (bound := fun _ : ℝ => B)
    · filter_upwards [self_mem_nhdsWithin] with y hy
      rw [uIoc_of_le hT]
      exact ((n07a_trace_angularSection_continuousOn hG hy).mono
        Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact Eventually.of_forall fun θ hθ => hB (y, θ)
        ⟨hy, by simpa only [uIcc_of_le hT] using uIoc_subset_uIcc hθ⟩
    · exact intervalIntegrable_const
    · exact Eventually.of_forall fun θ hθ =>
        (hG.comp (continuous_id.prodMk continuous_const).continuousOn
          (fun y hy => ⟨hy,
            by simpa only [uIcc_of_le hT] using uIoc_subset_uIcc hθ⟩)) x hx
  exact continuousWithinAt_const.mul hi

/-- On the open radial side, the integral of the genuine closed radial
jet is the derivative of the integral of the closed value jet. -/
theorem n07a_closedAngularIntegral_hasDerivAt
    {l r : ℝ} {W Wr : PolarPoint → ℝ}
    (hW : ContinuousOn W (Icc l r ×ˢ Icc (0 : ℝ) (2 * Real.pi)))
    (hWr : ContinuousOn Wr (Icc l r ×ˢ Icc (0 : ℝ) (2 * Real.pi)))
    (hderiv : ∀ x ∈ Ioo l r, ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
      HasDerivAt (fun y => W (y, θ)) (Wr (x, θ)) x)
    {β : ℝ → ℝ} (hβ : Continuous β)
    {x : ℝ} (hx : x ∈ Ioo l r) :
    HasDerivAt (fun y => radialAngularMean (fun θ => W (y, θ) * β θ))
      (radialAngularMean (fun θ => Wr (x, θ) * β θ)) x := by
  let G : PolarPoint → ℝ := fun p => W p * β p.2
  let Gr : PolarPoint → ℝ := fun p => Wr p * β p.2
  have hG : ContinuousOn G (Icc l r ×ˢ Icc (0 : ℝ) (2 * Real.pi)) :=
    hW.mul (hβ.comp continuous_snd).continuousOn
  have hGr : ContinuousOn Gr (Icc l r ×ˢ Icc (0 : ℝ) (2 * Real.pi)) :=
    hWr.mul (hβ.comp continuous_snd).continuousOn
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hGr
  have hT : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hmeas : ∀ᶠ y in 𝓝 x,
      AEStronglyMeasurable (fun θ => G (y, θ))
        (volume.restrict (uIoc (0 : ℝ) (2 * Real.pi))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    rw [uIoc_of_le hT]
    exact ((n07a_trace_angularSection_continuousOn hG
      (Ioo_subset_Icc_self hy)).mono Ioc_subset_Icc_self).aestronglyMeasurable
        measurableSet_Ioc
  have hmeasr : AEStronglyMeasurable (fun θ => Gr (x, θ))
      (volume.restrict (uIoc (0 : ℝ) (2 * Real.pi))) := by
    rw [uIoc_of_le hT]
    exact ((n07a_trace_angularSection_continuousOn hGr
      (Ioo_subset_Icc_self hx)).mono Ioc_subset_Icc_self).aestronglyMeasurable
        measurableSet_Ioc
  have hi : IntervalIntegrable (fun θ => G (x, θ)) volume 0 (2 * Real.pi) :=
    (n07a_trace_angularSection_continuousOn hG
      (Ioo_subset_Icc_self hx)).intervalIntegrable_of_Icc hT
  have hbound : ∀ᵐ θ ∂volume, θ ∈ uIoc (0 : ℝ) (2 * Real.pi) →
      ∀ y ∈ Ioo l r, ‖Gr (y, θ)‖ ≤ B :=
    Eventually.of_forall fun θ hθ y hy => hB (y, θ)
      ⟨Ioo_subset_Icc_self hy,
        by simpa only [uIcc_of_le hT] using uIoc_subset_uIcc hθ⟩
  have hd : ∀ᵐ θ ∂volume, θ ∈ uIoc (0 : ℝ) (2 * Real.pi) →
      ∀ y ∈ Ioo l r, HasDerivAt (fun z => G (z, θ)) (Gr (y, θ)) y :=
    Eventually.of_forall fun θ hθ y hy =>
      (hderiv y hy θ
        (by simpa only [uIcc_of_le hT] using uIoc_subset_uIcc hθ)).mul_const (β θ)
  have hInt := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y θ => G (y, θ)) (F' := fun y θ => Gr (y, θ))
    (μ := volume) (a := (0 : ℝ)) (b := 2 * Real.pi)
    (bound := fun _ : ℝ => B) (isOpen_Ioo.mem_nhds hx)
    hmeas hi hmeasr hbound intervalIntegrable_const hd
  exact hInt.2.const_mul ((2 * Real.pi)⁻¹)

/-- The closed-side representative's angular pairings are the same scalar
ae class as the original rough field. This step only uses Fubini. -/
theorem n07a_angularIntegral_ae_of_ae
    {l r : ℝ} {u v : PolarPoint → ℝ}
    (huv : u =ᵐ[volume.restrict (Ioo l r ×ˢ Ioc (0 : ℝ) (2 * Real.pi))] v)
    (β : ℝ → ℝ) :
    (fun x => radialAngularMean (fun θ => u (x, θ) * β θ))
      =ᵐ[volume.restrict (Ioo l r)]
    (fun x => radialAngularMean (fun θ => v (x, θ) * β θ)) := by
  have hprod : u =ᵐ[(volume.restrict (Ioo l r)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))] v := by
    simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod] using huv
  filter_upwards [Measure.ae_ae_eq_curry_of_prod hprod] with x hx
  unfold radialAngularMean
  apply congrArg (fun y : ℝ => (2 * Real.pi)⁻¹ * y)
  apply intervalIntegral.integral_congr_ae_restrict
  have hT : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  simpa only [uIoc_of_le hT] using
    hx.mono (fun θ hθ => congrArg (fun y : ℝ => y * β θ) hθ)

end ContinuousFlexibility.Analysis
