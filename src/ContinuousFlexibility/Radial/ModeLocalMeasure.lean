import ContinuousFlexibility.Statements.RadialTargets
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Measure and source pairings for the matched modal graph

The Hilbert measure has exactly the same null sets as Lebesgue measure on
the open radial interval. Source pairings are genuine integrable functions,
including for tests whose ordinary support accumulates at an endpoint.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace
open ContinuousFlexibility.Statements

def matchingDensity (D : ReferenceData) (r : ℝ) : ℝ :=
  12 * D.w r / r ^ 2

theorem matchingProfileGeometry {D : ReferenceData} (hD : IsAccumulatingProfile D) :
    RadialProfileGeometry D := by
  rcases hD with ⟨C, hC⟩
  exact hC.1

theorem matchingDensity_measurable {D : ReferenceData} (hD : IsAccumulatingProfile D) :
    Measurable (matchingDensity D) := by
  have hw : Continuous D.w := (matchingProfileGeometry hD).2.2.1.1.continuous
  unfold matchingDensity
  fun_prop

theorem matchingDensity_pos {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {r : ℝ} (hr : r ∈ radialCore D) : 0 < matchingDensity D r := by
  have hg := matchingProfileGeometry hD
  have hw : 0 < D.w r := hg.2.2.2.2.1 r hr
  have hr0 : 0 < r := lt_trans hg.1 hr.1
  unfold matchingDensity
  positivity

theorem matchingDensity_continuousOn {D : ReferenceData} (hD : IsAccumulatingProfile D) :
    ContinuousOn (matchingDensity D) (Icc D.a D.b) := by
  have hg := matchingProfileGeometry hD
  have hw : Continuous D.w := hg.2.2.1.1.continuous
  apply (continuous_const.mul hw).continuousOn.div (continuous_id.pow 2).continuousOn
  intro r hr
  exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hg.1 hr.1))

theorem radialHilbertMeasure_isFinite {D : ReferenceData} (hD : IsAccumulatingProfile D) :
    IsFiniteMeasure (radialHilbertMeasure D) := by
  have hi : Integrable (matchingDensity D) (volume.restrict (radialCore D)) :=
    (matchingDensity_continuousOn hD).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  exact isFiniteMeasure_withDensity_ofReal hi.2

theorem radialHilbertMeasure_ae_iff {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {p : ℝ → Prop} :
    (∀ᵐ r ∂radialHilbertMeasure D, p r) ↔
      ∀ᵐ r ∂volume.restrict (radialCore D), p r := by
  change (∀ᵐ r ∂(volume.restrict (radialCore D)).withDensity
    (fun r => ENNReal.ofReal (matchingDensity D r)), p r) ↔ _
  rw [ae_withDensity_iff (matchingDensity_measurable hD).ennreal_ofReal]
  constructor
  · intro h
    filter_upwards [h, ae_restrict_mem (show MeasurableSet (radialCore D) from measurableSet_Ioo)]
      with r hr hcore
    exact hr (ne_of_gt (ENNReal.ofReal_pos.mpr (matchingDensity_pos hD hcore)))
  · intro h
    exact h.mono (fun _ hp _ => hp)

theorem matchingInterval_congr_ae {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {f g : ℝ → ℝ} (h : f =ᵐ[radialHilbertMeasure D] g) :
    (∫ r in D.a..D.b, f r) = ∫ r in D.a..D.b, g r := by
  have h' := (radialHilbertMeasure_ae_iff hD).mp h
  have hab : D.a ≤ D.b := (matchingProfileGeometry hD).2.1.le
  simpa only [radialCore, intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo] using
    (integral_congr_ae h')

theorem matchingDensity_integrable_iff {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (f : ℝ → ℝ) :
    Integrable f (radialHilbertMeasure D) ↔
      Integrable (fun r => matchingDensity D r * f r) (volume.restrict (radialCore D)) := by
  change Integrable f ((volume.restrict (radialCore D)).withDensity
    (fun r => ENNReal.ofReal (matchingDensity D r))) ↔ _
  rw [integrable_withDensity_iff_integrable_smul'
    (matchingDensity_measurable hD).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integrable_congr
  filter_upwards [ae_restrict_mem (show MeasurableSet (radialCore D) from measurableSet_Ioo)]
    with r hr
  simp only [ENNReal.toReal_ofReal (matchingDensity_pos hD hr).le, smul_eq_mul]

theorem matchingDensity_integral {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (f : ℝ → ℝ) :
    (∫ r, f r ∂radialHilbertMeasure D) =
      ∫ r in D.a..D.b, matchingDensity D r * f r := by
  change (∫ r, f r ∂(volume.restrict (radialCore D)).withDensity
    (fun r => ENNReal.ofReal (matchingDensity D r))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (matchingDensity_measurable hD).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have hab : D.a ≤ D.b := (matchingProfileGeometry hD).2.1.le
  simp only [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (show MeasurableSet (radialCore D) from measurableSet_Ioo)]
    with r hr
  simp only [ENNReal.toReal_ofReal (matchingDensity_pos hD hr).le, smul_eq_mul]

theorem matchingSource_intervalIntegrable {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (F : RadialModeL2 D) {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hcompact : HasCompactSupport ψ) :
    IntervalIntegrable (fun r => matchingDensity D r * F r * ψ r) volume D.a D.b := by
  letI : IsFiniteMeasure (radialHilbertMeasure D) := radialHilbertMeasure_isFinite hD
  have hψLp : MemLp ψ 2 (radialHilbertMeasure D) :=
    hψ.memLp_of_hasCompactSupport hcompact
  have hi := (matchingDensity_integrable_iff hD (fun r => F r * ψ r)).mp
    ((Lp.memLp F).integrable_mul hψLp)
  have hi' : Integrable (fun r => matchingDensity D r * F r * ψ r)
      (volume.restrict (radialCore D)) := by
    simpa only [mul_assoc] using hi
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (matchingProfileGeometry hD).2.1.le).mpr hi'

theorem matchingSource_integral_eq_inner {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (F : RadialModeL2 D) {ψ : ℝ → ℝ} (hψ : MemLp ψ 2 (radialHilbertMeasure D)) :
    (∫ r in D.a..D.b, matchingDensity D r * F r * ψ r) =
      ⟪F, hψ.toLp ψ⟫_ℝ := by
  rw [L2.inner_def]
  have he : (∫ r, ⟪F r, (hψ.toLp ψ : ℝ → ℝ) r⟫_ℝ ∂radialHilbertMeasure D) =
      ∫ r, F r * ψ r ∂radialHilbertMeasure D := by
    apply integral_congr_ae
    filter_upwards [hψ.coeFn_toLp] with r hr
    simp only [hr, RCLike.inner_apply, conj_trivial]
    ring
  rw [he, matchingDensity_integral hD]
  congr 1
  funext r
  ring

end ContinuousFlexibility.Radial
