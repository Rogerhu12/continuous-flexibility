import ContinuousFlexibility.Radial.OuterEntranceVariation
import ContinuousFlexibility.Radial.OuterWholeKernelRepresentation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Weighted variation of parameters for every L² source

The density is included in the forcing. Integrability at the regular
entrance follows from the actual weighted L² norm and compact continuity,
while the natural solution supplies the full tail integral.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Analysis

theorem selected_integrable_withDensity {μ : Measure ℝ} {ρ g : ℝ → ℝ}
    (hρ : Measurable ρ) (hρ₀ : ∀ᵐ x ∂μ, 0 ≤ ρ x) :
    Integrable g (μ.withDensity (fun x => ENNReal.ofReal (ρ x))) ↔
      Integrable (fun x => ρ x * g x) μ := by
  rw [integrable_withDensity_iff_integrable_smul' hρ.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integrable_congr
  filter_upwards [hρ₀] with x hx
  simp only [ENNReal.toReal_ofReal hx, smul_eq_mul]

theorem selected_integral_withDensity {μ : Measure ℝ} {ρ : ℝ → ℝ}
    (hρ : Measurable ρ) (hρ₀ : ∀ᵐ x ∂μ, 0 ≤ ρ x) (g : ℝ → ℝ) :
    (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (ρ x))) =
      ∫ x, ρ x * g x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul hρ.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [hρ₀] with x hx
  simp only [ENNReal.toReal_ofReal hx, smul_eq_mul]

theorem selected_initial_density {a b x : ℝ} {ρ : ℝ → ℝ} (hx : x ∈ Ico a b) :
    ((volume.restrict (Ioo a b)).withDensity (fun y => ENNReal.ofReal (ρ y))).restrict
      (Ioc a x) =
    (volume.restrict (Ioc a x)).withDensity (fun y => ENNReal.ofReal (ρ y)) := by
  have hi : Ioc a x ∩ Ioo a b = Ioc a x :=
    inter_eq_left.mpr (fun y hy => ⟨hy.1, hy.2.trans_lt hx.2⟩)
  rw [restrict_withDensity measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc, hi]

theorem selected_initial_product_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b x : ℝ} {U : ℝ → ℝ} (hU : ContinuousOn U (Ico a b))
    (f : Lp ℝ 2 μ) (hx : x ∈ Ico a b) :
    Integrable (fun y => U y * f y) (μ.restrict (Ioc a x)) := by
  letI : IsFiniteMeasure (compactIntervalMeasure μ a x) :=
    isFiniteMeasure_compactIntervalMeasure μ hx.1
  have hc := integrable_outer_core_product μ hx.1 U
    (hU.mono (fun y hy => ⟨hy.1, hy.2.trans_lt hx.2⟩)) f
  exact (show IntegrableOn (fun y => U y * f y) (Icc a x) μ from hc).mono_set
    Ioc_subset_Icc_self

theorem selected_weighted_forcing_locallyIntegrable
    {a b : ℝ} {ρ : ℝ → ℝ} (hρ : Measurable ρ)
    (hρ₀ : ∀ x ∈ Ioo a b, 0 ≤ ρ x)
    [IsFiniteMeasure ((volume.restrict (Ioo a b)).withDensity
      (fun x => ENNReal.ofReal (ρ x)))]
    (f : Lp ℝ 2 ((volume.restrict (Ioo a b)).withDensity
      (fun x => ENNReal.ofReal (ρ x)))) :
    LocallyIntegrableOn (fun x => -(ρ x * f x)) (Ioo a b) := by
  have hnonneg : ∀ᵐ x ∂volume.restrict (Ioo a b), 0 ≤ ρ x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hρ₀ x hx
  have hf := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp f)
  have hg : IntegrableOn (fun x => ρ x * f x) (Ioo a b) :=
    (selected_integrable_withDensity hρ hnonneg).mp hf
  exact hg.neg.locallyIntegrableOn

theorem selected_weighted_initial_primitive
    {a b x : ℝ} {ρ U : ℝ → ℝ} (hρ : Measurable ρ)
    (hρ₀ : ∀ y ∈ Ioo a b, 0 ≤ ρ y)
    [IsFiniteMeasure ((volume.restrict (Ioo a b)).withDensity
      (fun y => ENNReal.ofReal (ρ y)))]
    (hU : ContinuousOn U (Ico a b))
    (f : Lp ℝ 2 ((volume.restrict (Ioo a b)).withDensity
      (fun y => ENNReal.ofReal (ρ y))))
    (hx : x ∈ Ico a b) :
    IntervalIntegrable (fun y => U y * (-(ρ y * f y))) volume a x ∧
      (∫ y in a..x, U y * (-(ρ y * f y))) =
        -(∫ y in Ioc a x, U y * f y ∂(volume.restrict (Ioo a b)).withDensity
          (fun y => ENNReal.ofReal (ρ y))) := by
  let μ := (volume.restrict (Ioo a b)).withDensity (fun y => ENNReal.ofReal (ρ y))
  have hnonneg : ∀ᵐ y ∂volume.restrict (Ioc a x), 0 ≤ ρ y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact hρ₀ y ⟨hy.1, hy.2.trans_lt hx.2⟩
  have hi := selected_initial_product_integrable μ hU f hx
  rw [show μ.restrict (Ioc a x) =
    (volume.restrict (Ioc a x)).withDensity (fun y => ENNReal.ofReal (ρ y)) from
      selected_initial_density hx] at hi
  have hρi := (selected_integrable_withDensity hρ hnonneg).mp hi
  constructor
  · apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1).mpr
    exact hρi.neg.congr (Eventually.of_forall (fun y => by dsimp only; ring))
  · rw [intervalIntegral.integral_of_le hx.1, selected_initial_density hx,
      selected_integral_withDensity hρ hnonneg, ← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall (fun y => by dsimp only; ring)

/-- Splitting the actual weighted kernel at x gives the same entrance-based
variation formula, including its correct density and its tail constant. -/
theorem selected_weighted_kernel_variation
    {a b lam x : ℝ} {ρ U V : ℝ → ℝ} (hρ : Measurable ρ)
    (hρ₀ : ∀ y ∈ Ioo a b, 0 ≤ ρ y)
    [IsFiniteMeasure ((volume.restrict (Ioo a b)).withDensity
      (fun y => ENNReal.ofReal (ρ y)))]
    (hU : ContinuousOn U (Ico a b)) (hV : ContinuousOn V (Ico a b))
    (f : Lp ℝ 2 ((volume.restrict (Ioo a b)).withDensity
      (fun y => ENNReal.ofReal (ρ y))))
    (hVf : Integrable (fun y => V y * f y)
      ((volume.restrict (Ioo a b)).withDensity (fun y => ENNReal.ofReal (ρ y))))
    (hrow : Integrable (fun y => outerGreenKernel lam U V x y * f y)
      ((volume.restrict (Ioo a b)).withDensity (fun y => ENNReal.ofReal (ρ y))))
    (hx : x ∈ Ico a b) :
    (∫ y, outerGreenKernel lam U V x y * f y
      ∂(volume.restrict (Ioo a b)).withDensity (fun y => ENNReal.ofReal (ρ y))) =
    outerSolution lam 0
      (-(∫ y, V y * f y
        ∂(volume.restrict (Ioo a b)).withDensity (fun y => ENNReal.ofReal (ρ y))))
      a U V (fun y => -(ρ y * f y)) x := by
  let μ := (volume.restrict (Ioo a b)).withDensity (fun y => ENNReal.ofReal (ρ y))
  have hfull : ∀ᵐ y ∂μ, y ∈ Ioo a b :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioo)
  have hleft :
      (∫ y in Ioc a x, outerGreenKernel lam U V x y * f y ∂μ) =
      lam⁻¹ * V x * ∫ y in Ioc a x, U y * f y ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    rw [outerGreenKernel_symm lam U V x y, outerGreenKernel_of_le hy.2]
    ring
  have hright :
      (∫ y in (Ioc a x)ᶜ, outerGreenKernel lam U V x y * f y ∂μ) =
      lam⁻¹ * U x * ∫ y in (Ioc a x)ᶜ, V y * f y ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hfull.filter_mono ae_restrict_le,
      ae_restrict_mem measurableSet_Ioc.compl] with y hy hn
    have hxy : x < y := lt_of_not_ge (fun h => hn ⟨hy.1, h⟩)
    rw [outerGreenKernel_of_le hxy.le]
    ring
  have hsplit := integral_add_compl measurableSet_Ioc hrow
  have htail := setIntegral_compl measurableSet_Ioc hVf
  have hUi := (selected_weighted_initial_primitive hρ hρ₀ hU f hx).2
  have hVi := (selected_weighted_initial_primitive hρ hρ₀ hV f hx).2
  rw [← hsplit, hleft, hright, htail]
  unfold outerSolution
  rw [hUi, hVi]
  ring

end ContinuousFlexibility.Radial
