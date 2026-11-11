import ContinuousFlexibility.Radial.SelectedOuterVariation
import ContinuousFlexibility.Radial.OuterGreenAssembly
import ContinuousFlexibility.Radial.OuterFirstOrderRegularity

/-!
# The constructed weighted Green map solves the actual equation

For arbitrary weighted L² data the kernel formula has a C¹ representative
up to the regular entrance. Its continuous physical flux has the required
weak derivative and the exact normalized Robin trace.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Analysis

section

variable {a c b J lam : ℝ} {w ρ P ZP Q ZQ : ℝ → ℝ}

local notation "μ" => Measure.withDensity (Measure.restrict volume (Ioo a b))
  (fun x => ENNReal.ofReal (ρ x))

theorem OuterFundamentalStatePair.weighted_solution
    (H : OuterFundamentalStatePair (fun x => lam / w x)
      (fun x => J * deriv w x / (lam * x)) P ZP Q ZQ a c b)
    (hac : a ≤ c) (hcb : c < b) (hlam : lam ≠ 0)
    (hw : ContDiff ℝ ∞ w)
    (hwn : ∀ x ∈ Ico a b, w x ≠ 0) (hr : ∀ x ∈ Ico a b, x ≠ 0)
    (hρ : Measurable ρ) (hρ₀ : ∀ x ∈ Ioo a b, 0 ≤ ρ x)
    (hPc : P c = 1) (hPLp : MemLp P 2 (Measure.restrict μ (Icc a c)ᶜ))
    [IsFiniteMeasure μ]
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hR : ∀ f : Lp ℝ 2 μ, (R f : ℝ → ℝ) =ᵐ[μ]
      fun x => ∫ y, outerGreenKernel lam H.U H.V x y * f y ∂μ)
    (hrow : ∀ (f : Lp ℝ 2 μ) (x : ℝ), x ∈ Ico a b →
      Integrable (fun y => outerGreenKernel lam H.U H.V x y * f y) μ) :
    ∀ f : Lp ℝ 2 μ, ∃ u p : ℝ → ℝ,
      (R f : ℝ → ℝ) =ᵐ[μ] u ∧
      ContDiffOn ℝ 1 u (Ico a b) ∧ ContinuousOn p (Ico a b) ∧
      (∀ x ∈ Ioo a b, p x = w x * deriv u x) ∧
      (∀ x ∈ Ico a b, p x = w x * derivWithin u (Ico a b) x) ∧
      HasIntervalWeakDerivative a b p (fun x => J * deriv w x / x * u x - ρ x * f x) ∧
      outerStatePair H.entrance (u a, p a / lam) = 0 := by
  intro f
  have hab : a < b := hac.trans_lt hcb
  have ha : a ∈ Ico a b := ⟨le_rfl, hab⟩
  have hdw : ContDiff ℝ ∞ (deriv w) := (contDiff_infty_iff_deriv.mp hw).2
  have hα : ContDiffOn ℝ ∞ (fun x => lam / w x) (Ico a b) :=
    contDiffOn_const.div hw.contDiffOn hwn
  have hβ : ContDiffOn ℝ ∞ (fun x => J * deriv w x / (lam * x)) (Ico a b) :=
    (contDiffOn_const.mul hdw.contDiffOn).div (contDiffOn_const.mul contDiffOn_id)
      (fun x hx => mul_ne_zero hlam (hr x hx))
  have hUinf := (H.U_system.contDiffOn (uniqueDiffOn_Ico a b) hα hβ).1
  have hVinf := (H.V_system.contDiffOn (uniqueDiffOn_Ico a b) hα hβ).1
  have hU1 : ContDiffOn ℝ 1 H.U (Ioo a b) :=
    (hUinf.of_le (by simp)).mono Ioo_subset_Ico_self
  have hV1 : ContDiffOn ℝ 1 H.V (Ioo a b) :=
    (hVinf.of_le (by simp)).mono Ioo_subset_Ico_self
  have hU2 : ContDiffOn ℝ 2 H.U (Ioo a b) :=
    (hUinf.of_le (by simp)).mono Ioo_subset_Ico_self
  have hV2 : ContDiffOn ℝ 2 H.V (Ioo a b) :=
    (hVinf.of_le (by simp)).mono Ioo_subset_Ico_self
  have hUc := H.U_system.continuousOn.1
  have hVc := H.V_system.continuousOn.1
  have hDU := (H.U_system.continuousOn_deriv hα.continuousOn hβ.continuousOn).1
  have hDV := (H.V_system.continuousOn_deriv hα.continuousOn hβ.continuousOn).1
  have hfull : ∀ᵐ x ∂μ, x ∈ Ioo a b :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioo)
  letI : IsFiniteMeasure (compactIntervalMeasure μ a c) :=
    isFiniteMeasure_compactIntervalMeasure μ hac
  have hVf : Integrable (fun x => H.V x * f x) μ := by
    have hc := integrable_outer_core_product μ hac H.V (H.continuousOn_core hcb).2 f
    have hPmul : Integrable (fun x => P x * f x) (Measure.restrict μ (Icc a c)ᶜ) :=
      hPLp.integrable_mul ((Lp.memLp f).restrict (Icc a c)ᶜ)
    have ht : Integrable (fun x => H.V x * f x) (Measure.restrict μ (Icc a c)ᶜ) := by
      apply (hPmul.div_const H.scale).congr
      have htail := outer_ae_deep_interval μ (c := c)
        (hfull.mono (fun x hx => Ioo_subset_Ico_self hx))
      filter_upwards [htail] with x hx
      rw [H.V_tail x hx]
      ring
    have h := hc.add_measure ht
    rwa [Measure.restrict_add_restrict_compl measurableSet_Icc] at h
  let g : ℝ → ℝ := fun x => -(ρ x * f x)
  let C : ℝ := -(∫ x, H.V x * f x ∂μ)
  let u : ℝ → ℝ := outerSolution lam 0 C a H.U H.V g
  let p : ℝ → ℝ := outerSolutionFlux lam 0 C a w H.U H.V g
  let du : ℝ → ℝ := fun x => -(1 / lam) *
    (deriv H.V x * (0 + ∫ t in a..x, H.U t * g t) +
      deriv H.U x * (C - ∫ t in a..x, H.V t * g t))
  have hg : LocallyIntegrableOn g (Ioo a b) :=
    selected_weighted_forcing_locallyIntegrable hρ hρ₀ f
  have hUi : ∀ x ∈ Ioo a b, IntervalIntegrable (fun t => H.U t * g t) volume a x :=
    fun x hx => (selected_weighted_initial_primitive hρ hρ₀ hUc f
      (Ioo_subset_Ico_self hx)).1
  have hVi : ∀ x ∈ Ioo a b, IntervalIntegrable (fun t => H.V t * g t) volume a x :=
    fun x hx => (selected_weighted_initial_primitive hρ hρ₀ hVc f
      (Ioo_subset_Ico_self hx)).1
  have hA : ContinuousOn (fun x => 0 + ∫ t in a..x, H.U t * g t) (Ico a b) :=
    continuousOn_const.add (continuousOn_initialPrimitive hUi)
  have hB : ContinuousOn (fun x => C - ∫ t in a..x, H.V t * g t) (Ico a b) :=
    continuousOn_const.sub (continuousOn_initialPrimitive hVi)
  have huc : ContinuousOn u (Ico a b) :=
    continuousOn_const.mul ((hVc.mul hA).add (hUc.mul hB))
  have hduc : ContinuousOn du (Ico a b) :=
    continuousOn_const.mul ((hDV.mul hA).add (hDU.mul hB))
  have hud : ∀ x ∈ Ioo a b, HasDerivAt u (du x) x :=
    hasDerivAt_outerSolution_from_left hU1 hV1 hg hUi hVi
  have hwithin : ∀ x ∈ Ico a b, HasDerivWithinAt u (du x) (Ico a b) x :=
    tail_hasDerivWithinAt_Ico_of_continuous hab huc hduc hud
  have hu : ContDiffOn ℝ 1 u (Ico a b) := by
    apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ico a b)).mpr
    refine ⟨fun x hx => (hwithin x hx).differentiableWithinAt, ?_⟩
    exact hduc.congr (fun x hx =>
      (hwithin x hx).derivWithin (uniqueDiffOn_Ico a b x hx))
  have hp : ContinuousOn p (Ico a b) :=
    continuousOn_const.mul (((hw.continuous.continuousOn.mul hDV).mul hA).add
      ((hw.continuous.continuousOn.mul hDU).mul hB))
  have hflux : ∀ x ∈ Ioo a b, p x = w x * deriv u x :=
    outerSolutionFlux_eq_from_left hU1 hV1 hg hUi hVi
  have hfluxWithin : ∀ x ∈ Ico a b, p x = w x * derivWithin u (Ico a b) x := by
    intro x hx
    rw [(hwithin x hx).derivWithin (uniqueDiffOn_Ico a b x hx)]
    dsimp only [p, outerSolutionFlux, du]
    ring
  have hUeq : ∀ x ∈ Ioo a b, radialJacobi J w H.U x = 0 :=
    outerFirstOrderSystem_radialJacobi isOpen_Ioo hlam
      (fun x hx => H.U_system x (Ioo_subset_Ico_self hx))
      (fun x hx => hwn x (Ioo_subset_Ico_self hx))
      (fun x hx => hr x (Ioo_subset_Ico_self hx))
  have hVeq : ∀ x ∈ Ioo a b, radialJacobi J w H.V x = 0 :=
    outerFirstOrderSystem_radialJacobi isOpen_Ioo hlam
      (fun x hx => H.V_system x (Ioo_subset_Ico_self hx))
      (fun x hx => hwn x (Ioo_subset_Ico_self hx))
      (fun x hx => hr x (Ioo_subset_Ico_self hx))
  have hW : ∀ x ∈ Ioo a b, radialWronskian w H.U H.V x = -lam :=
    fun x hx => H.radialWronskian hwn x (Ioo_subset_Ico_self hx)
  have hweak : HasIntervalWeakDerivative a b p
      (fun x => J * deriv w x / x * u x - ρ x * f x) := by
    simpa only [u, p, g, sub_eq_add_neg] using
      (outerSolutionFlux_weakDerivative_from_left (cA := 0) (cB := C)
        hab (hw.of_le (by simp)).contDiffOn hU2 hV2 hUeq hVeq hW hlam hg hUi hVi)
  have hRobin : outerStatePair H.entrance (u a, p a / lam) = 0 := by
    have he := (outerSolution_entrance_traces (cB := C) hab H.unit hU1 hV1
      hUc hVc hDU hDV hg hUi hVi
      ((H.flux_states hlam hwn a ha).1.trans H.U_initial)).1
    change outerStatePair H.entrance (u a,
      w a * derivWithin u (Ico a b) a / lam) = 0 at he
    rwa [← hfluxWithin a ha] at he
  refine ⟨u, p, ?_, hu, hp, hflux, hfluxWithin, hweak, hRobin⟩
  filter_upwards [hR f, hfull] with x hx hxi
  exact hx.trans (selected_weighted_kernel_variation hρ hρ₀ hUc hVc f hVf
    (hrow f x (Ioo_subset_Ico_self hxi)) (Ioo_subset_Ico_self hxi))

end

end ContinuousFlexibility.Radial
