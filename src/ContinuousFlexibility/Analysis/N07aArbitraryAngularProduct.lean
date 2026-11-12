import ContinuousFlexibility.Radial.ReferenceGraphCoefficients
import ContinuousFlexibility.Radial.ReferenceColumnSmooth
import ContinuousFlexibility.Radial.WeakDivergenceRegularity
import ContinuousFlexibility.Radial.R11bLocalL2
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Arbitrary angular product tests for the reference graph

Every smooth periodic angular test projects the reference weak equation to a
scalar weak-divergence equation. Its forcing retains the angular second-test
derivative, so no eigenfunction identity or source differentiability is needed.
Local integrability follows from the graph's actual weighted L² membership.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

def n07aTraceAngularMoment (β : ℝ → ℝ) (u : PolarPoint → ℝ) (r : ℝ) : ℝ :=
  radialAngularMean (fun θ => u (r, θ) * β θ)

theorem n07a_trace_product_lift_test {D : ReferenceData} {φ β : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ radialCore D)
    (hβ : ContDiff ℝ ∞ β) (hβp : Function.Periodic β (2 * Real.pi)) :
    RadialTest D (fun x : PolarPoint => φ x.1 * β x.2) := by
  refine ⟨(hφ.comp contDiff_fst).mul (hβ.comp contDiff_snd),
    ?_, tsupport φ, hφc, hφs, ?_⟩
  · intro x
    simp only [Prod.fst_add, Prod.snd_add, add_zero, hβp x.2]
  · intro r hr θ
    have hz : φ r = 0 := image_eq_zero_of_notMem_tsupport hr
    change φ r * β θ = 0
    rw [hz, zero_mul]

theorem n07a_trace_radialPDE_product {w φ β : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hφ : ContDiff ℝ ∞ φ)
    (hβ : ContDiff ℝ ∞ β) (r θ : ℝ) :
    radialPDE w (fun s α => φ s * β α) r θ =
      deriv (fun t => w t * deriv φ t) r * β θ +
        deriv w r / r * φ r * deriv (deriv β) θ := by
  have hφ' : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hβ' : ContDiff ℝ ∞ (deriv β) := (contDiff_infty_iff_deriv.mp hβ).2
  have hflux : Differentiable ℝ (fun t => w t * deriv φ t) :=
    (hw.mul hφ').differentiable (by simp)
  have hr : (fun t => w t * deriv (fun z => φ z * β θ) t) =
      (fun t => (w t * deriv φ t) * β θ) := by
    funext t
    rw [((hφ.differentiable (by simp) t).hasDerivAt.mul_const (β θ)).deriv]
    ring
  have hθ₁ : deriv (fun α => φ r * β α) = fun α => φ r * deriv β α := by
    funext α
    exact ((hβ.differentiable (by simp) α).hasDerivAt.const_mul (φ r)).deriv
  have hθ₂ : deriv (deriv (fun α => φ r * β α)) θ =
      φ r * deriv (deriv β) θ := by
    rw [hθ₁]
    exact ((hβ'.differentiable (by simp) θ).hasDerivAt.const_mul (φ r)).deriv
  change deriv (fun t => w t * deriv (fun z => φ z * β θ) t) r +
      deriv w r / r * deriv (deriv (fun α => φ r * β α)) θ = _
  rw [hr, ((hflux r).hasDerivAt.mul_const (β θ)).deriv, hθ₂]
  ring

theorem n07a_trace_mean_mul (u : PolarPoint → ℝ) (β : ℝ → ℝ)
    (a : ℝ → ℝ) (r : ℝ) :
    radialAngularMean (fun θ => u (r, θ) * (a r * β θ)) =
      n07aTraceAngularMoment β u r * a r := by
  have he : (fun θ => u (r, θ) * (a r * β θ)) =
      (fun θ => a r * (u (r, θ) * β θ)) := by
    funext θ
    ring
  rw [he, radialAngularMean_const_mul]
  exact mul_comm _ _

private theorem n07a_trace_mean_two_terms {f β δ : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 (2 * Real.pi))
    (hβ : Continuous β) (hδ : Continuous δ) (A B : ℝ) :
    radialAngularMean (fun θ => f θ * (A * β θ + B * δ θ)) =
      A * radialAngularMean (fun θ => f θ * β θ) +
        B * radialAngularMean (fun θ => f θ * δ θ) := by
  have h₁ := (hf.mul_continuousOn hβ.continuousOn).const_mul A
  have h₂ := (hf.mul_continuousOn hδ.continuousOn).const_mul B
  have he : (fun θ => f θ * (A * β θ + B * δ θ)) =
      (fun θ => A * (f θ * β θ) + B * (f θ * δ θ)) := by
    funext θ
    ring
  unfold radialAngularMean
  rw [he, intervalIntegral.integral_add h₁ h₂,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

theorem n07a_trace_mean_radialPDE_product {w φ β : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hφ : ContDiff ℝ ∞ φ) (hβ : ContDiff ℝ ∞ β)
    (u : PolarPoint → ℝ) (r : ℝ)
    (hu : IntervalIntegrable (fun θ => u (r, θ)) volume 0 (2 * Real.pi)) :
    radialAngularMean (fun θ =>
      u (r, θ) * radialPDE w (fun s α => φ s * β α) r θ) =
      n07aTraceAngularMoment β u r * deriv (fun t => w t * deriv φ t) r +
        (deriv w r / r * n07aTraceAngularMoment (deriv (deriv β)) u r) * φ r := by
  have hβ' := (contDiff_infty_iff_deriv.mp hβ).2
  have hβ'' := (contDiff_infty_iff_deriv.mp hβ').2
  simp_rw [n07a_trace_radialPDE_product hw hφ hβ]
  rw [n07a_trace_mean_two_terms hu hβ.continuous hβ''.continuous]
  unfold n07aTraceAngularMoment
  ring

theorem n07a_trace_column_product (D : ReferenceData) (β φ : ℝ → ℝ) (r : ℝ) :
    radialAngularMean (fun θ =>
      referenceColumn D r * cosineMode 2 θ * (φ r * β θ)) =
      (referenceColumn D r *
        radialAngularMean (fun θ => cosineMode 2 θ * β θ)) * φ r := by
  have he : (fun θ => referenceColumn D r * cosineMode 2 θ * (φ r * β θ)) =
      (fun θ => (referenceColumn D r * φ r) * (cosineMode 2 θ * β θ)) := by
    funext θ
    ring
  rw [he, radialAngularMean_const_mul]
  ring

private theorem n07a_trace_angular_sections {l r : ℝ} {u : PolarPoint → ℝ}
    (hu : IntegrableOn u (Ioc l r ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) volume) :
    ∀ᵐ x ∂volume.restrict (Ioc l r),
      IntervalIntegrable (fun θ => u (x, θ)) volume 0 (2 * Real.pi) := by
  have hp : Integrable u ((volume.restrict (Ioc l r)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod] using hu.integrable
  filter_upwards [hp.prod_right_ae] with x hx
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi)).mpr hx

theorem n07a_trace_angularMoment_integrable {l r : ℝ} (hlr : l ≤ r)
    {u : PolarPoint → ℝ}
    (hu : IntegrableOn u (Ioc l r ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) volume)
    {β : ℝ → ℝ} (hβ : Continuous β) :
    IntervalIntegrable (n07aTraceAngularMoment β u) volume l r := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hβ.continuousOn (s := Icc (0 : ℝ) (2 * Real.pi)))
  have hβm : AEStronglyMeasurable (fun p : PolarPoint => β p.2)
      (volume.restrict (Ioc l r ×ˢ Ioc (0 : ℝ) (2 * Real.pi))) :=
    (hβ.comp continuous_snd).aestronglyMeasurable
  have hβb : ∀ᵐ p ∂volume.restrict (Ioc l r ×ˢ Ioc (0 : ℝ) (2 * Real.pi)),
      ‖β p.2‖ ≤ B := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
    exact hB p.2 (Ioc_subset_Icc_self hp.2)
  have hi := hu.mul_bdd hβm hβb
  have hp : Integrable (fun p : PolarPoint => u p * β p.2)
      ((volume.restrict (Ioc l r)).prod
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod] using hi
  have hmoment : n07aTraceAngularMoment β u =
      fun x => (2 * Real.pi)⁻¹ *
        ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), u (x, θ) * β θ := by
    funext x
    simp only [n07aTraceAngularMoment, radialAngularMean,
      intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  rw [hmoment, intervalIntegrable_iff_integrableOn_Ioc_of_le hlr]
  have hmomentInt := hp.integral_prod_left.const_mul ((2 * Real.pi)⁻¹)
  exact ⟨hmomentInt.aestronglyMeasurable, hmomentInt.hasFiniteIntegral⟩

private theorem n07a_trace_interval_localize {D : ReferenceData} {l r : ℝ}
    (hsub : Icc l r ⊆ radialCore D) {f : ℝ → ℝ}
    (hs : Function.support f ⊆ Ioo l r) :
    (∫ x in D.a..D.b, f x) = ∫ x in l..r, f x := by
  have hbig : Function.support f ⊆ Ioc D.a D.b := by
    intro x hx
    have hm := hsub (Ioo_subset_Icc_self (hs hx))
    exact ⟨hm.1, hm.2.le⟩
  rw [intervalIntegral.integral_eq_integral_of_support_subset hbig,
    intervalIntegral.integral_eq_integral_of_support_subset
      (hs.trans Ioo_subset_Ioc_self)]

def n07aTraceAngularRhs (D : ReferenceData) (U : RadialUnknown)
    (F : RadialSource) (β : ℝ → ℝ) (r : ℝ) : ℝ :=
  n07aTraceAngularMoment β F.1 r -
    deriv D.w r / r * n07aTraceAngularMoment (deriv (deriv β)) U.1 r -
    U.2 * referenceColumn D r *
      radialAngularMean (fun θ => cosineMode 2 θ * β θ)

/-- The actual reference graph, tested against an arbitrary angular
function, is a scalar weak-divergence equation. No angular derivative of
either the unknown or the source is assumed. -/
theorem n07a_referenceGraph_product_divergence
    {D : ReferenceData} {γ M₀ M₁ : ℝ}
    (hgeom : RadialProfileGeometry D) (hborder : RadialTrueBorder D)
    {U : RadialUnknown} {F : RadialSource}
    (hgraph : ReferenceGraph D γ M₀ M₁ U F)
    {l r : ℝ} (hlr : l < r) (hsub : Icc l r ⊆ radialCore D)
    (hUi : IntegrableOn U.1
      (Ioc l r ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) volume)
    (hFi : IntegrableOn F.1
      (Ioc l r ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) volume)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβp : Function.Periodic β (2 * Real.pi)) :
    IntervalIntegrable (n07aTraceAngularMoment β U.1) volume l r ∧
    IntervalIntegrable (n07aTraceAngularRhs D U F β) volume l r ∧
    ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo l r →
      (∫ x in l..r, n07aTraceAngularMoment β U.1 x *
        deriv (fun y => D.w y * deriv φ y) x) =
        ∫ x in l..r, n07aTraceAngularRhs D U F β x * φ x := by
  let q : ℝ → ℝ := fun x => deriv D.w x / x
  let κ : ℝ := radialAngularMean (fun θ => cosineMode 2 θ * β θ)
  have hw : ContDiff ℝ ∞ D.w := hgeom.2.2.1.1
  have hq : Continuous q :=
    (reference_contDiff_flat_deriv_div hgeom.1 hgeom.2.2.1).continuous
  have hcol : Continuous (referenceColumn D) :=
    (referenceColumn_contDiff hgeom hborder).continuous
  have hβ' := (contDiff_infty_iff_deriv.mp hβ).2
  have hβ'' := (contDiff_infty_iff_deriv.mp hβ').2
  have hUM := n07a_trace_angularMoment_integrable hlr.le hUi hβ.continuous
  have hUM₂ := n07a_trace_angularMoment_integrable hlr.le hUi hβ''.continuous
  have hFM := n07a_trace_angularMoment_integrable hlr.le hFi hβ.continuous
  have hqU : IntervalIntegrable
      (fun x => q x * n07aTraceAngularMoment (deriv (deriv β)) U.1 x)
      volume l r := hUM₂.continuousOn_mul hq.continuousOn
  have hCcont : Continuous (fun x : ℝ => U.2 * referenceColumn D x * κ) :=
    (continuous_const.mul hcol).mul continuous_const
  have hCi : IntervalIntegrable
      (fun x => U.2 * referenceColumn D x * κ) volume l r :=
    hCcont.intervalIntegrable l r
  have hg : IntervalIntegrable (n07aTraceAngularRhs D U F β) volume l r := by
    change IntervalIntegrable
      (fun x => n07aTraceAngularMoment β F.1 x -
        q x * n07aTraceAngularMoment (deriv (deriv β)) U.1 x -
        U.2 * referenceColumn D x * κ) volume l r
    exact (hFM.sub hqU).sub hCi
  refine ⟨hUM, hg, ?_⟩
  intro φ hφ hφc hφs
  let dφ : ℝ → ℝ := fun x => deriv (fun y => D.w y * deriv φ y) x
  have hφ' := (contDiff_infty_iff_deriv.mp hφ).2
  have hdφ : ContDiff ℝ ∞ dφ :=
    (contDiff_infty_iff_deriv.mp (hw.mul hφ')).2
  have hdφs : tsupport dφ ⊆ tsupport φ :=
    tsupport_deriv_subset.trans (tsupport_mul_subset_right.trans tsupport_deriv_subset)
  let R : ℝ → ℝ := fun x => radialAngularMean (fun θ =>
    U.1 (x, θ) * radialPDE D.w (fun s α => φ s * β α) x θ)
  have hRs : Function.support R ⊆ Ioo l r := by
    intro x hx
    by_contra hxi
    have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hxi (hφs h))
    have hdx : dφ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hxi (hφs (hdφs h)))
    apply hx
    dsimp only [R]
    simp_rw [n07a_trace_radialPDE_product hw hφ hβ]
    change radialAngularMean (fun θ => U.1 (x, θ) *
      (dφ x * β θ + deriv D.w x / x * φ x * deriv (deriv β) θ)) = 0
    simp only [hφx, hdx, zero_mul, mul_zero, zero_add,
      radialAngularMean, intervalIntegral.integral_zero]
  have hCs : Function.support
      (fun x => (referenceColumn D x * κ) * φ x) ⊆ Ioo l r :=
    (Function.support_mul_subset_right _ _).trans ((subset_tsupport φ).trans hφs)
  have hFs : Function.support
      (fun x => n07aTraceAngularMoment β F.1 x * φ x) ⊆ Ioo l r :=
    (Function.support_mul_subset_right _ _).trans ((subset_tsupport φ).trans hφs)
  have htest := n07a_trace_product_lift_test hφ hφc
    (hφs.trans (Ioo_subset_Icc_self.trans hsub)) hβ hβp
  have hraw := hgraph.2.2.2 _ htest
  unfold radialWeakPairing at hraw
  simp_rw [n07a_trace_column_product, n07a_trace_mean_mul] at hraw
  change (∫ x in D.a..D.b, R x) +
      U.2 * (∫ x in D.a..D.b, (referenceColumn D x * κ) * φ x) =
      ∫ x in D.a..D.b, n07aTraceAngularMoment β F.1 x * φ x at hraw
  rw [n07a_trace_interval_localize hsub hRs,
    n07a_trace_interval_localize hsub hCs,
    n07a_trace_interval_localize hsub hFs] at hraw
  have hRae : R =ᵐ[volume.restrict (Ioc l r)]
      (fun x => n07aTraceAngularMoment β U.1 x * dφ x +
        (q x * n07aTraceAngularMoment (deriv (deriv β)) U.1 x) * φ x) := by
    filter_upwards [n07a_trace_angular_sections hUi] with x hx
    exact n07a_trace_mean_radialPDE_product hw hφ hβ U.1 x hx
  have hRint : (∫ x in l..r, R x) =
      ∫ x in l..r, n07aTraceAngularMoment β U.1 x * dφ x +
        (q x * n07aTraceAngularMoment (deriv (deriv β)) U.1 x) * φ x := by
    apply intervalIntegral.integral_congr_ae_restrict
    simpa only [uIoc_of_le hlr.le] using hRae
  have hUMd := hUM.mul_continuousOn hdφ.continuous.continuousOn
  have hqUφ := hqU.mul_continuousOn hφ.continuous.continuousOn
  have hFMφ := hFM.mul_continuousOn hφ.continuous.continuousOn
  have hCiφ := hCi.mul_continuousOn hφ.continuous.continuousOn
  rw [hRint, intervalIntegral.integral_add hUMd hqUφ] at hraw
  have hcolumn : U.2 * (∫ x in l..r, (referenceColumn D x * κ) * φ x) =
      ∫ x in l..r, (U.2 * referenceColumn D x * κ) * φ x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hcolumn] at hraw
  have hrhs : (fun x => n07aTraceAngularRhs D U F β x * φ x) =
      (fun x => (n07aTraceAngularMoment β F.1 x * φ x -
        (q x * n07aTraceAngularMoment (deriv (deriv β)) U.1 x) * φ x) -
        (U.2 * referenceColumn D x * κ) * φ x) := by
    funext x
    dsimp only [n07aTraceAngularRhs, q, κ]
    ring
  change (∫ x in l..r, n07aTraceAngularMoment β U.1 x * dφ x) = _
  rw [hrhs, intervalIntegral.integral_sub (hFMφ.sub hqUφ) hCiφ,
    intervalIntegral.integral_sub hFMφ hqUφ]
  linarith only [hraw]

/-- A single C1 scalar representative across the reference cut, for every
smooth periodic angular test. The reference source needs no derivatives. -/
theorem n07a_referenceGraph_product_C1
    {D : ReferenceData} {γ M₀ M₁ : ℝ}
    (hgeom : RadialProfileGeometry D) (hborder : RadialTrueBorder D)
    {U : RadialUnknown} {F : RadialSource}
    (hgraph : ReferenceGraph D γ M₀ M₁ U F)
    {l r : ℝ} (hlr : l < r) (hsub : Icc l r ⊆ radialCore D)
    (hUi : IntegrableOn U.1
      (Ioc l r ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) volume)
    (hFi : IntegrableOn F.1
      (Ioc l r ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) volume)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβp : Function.Periodic β (2 * Real.pi)) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 1 v ∧
      n07aTraceAngularMoment β U.1 =ᵐ[volume.restrict (Ioo l r)] v := by
  have hdata := n07a_referenceGraph_product_divergence
    hgeom hborder hgraph hlr hsub hUi hFi hβ hβp
  obtain ⟨v, C, hv, hue, _hflux, _hAC, _hfluxAE⟩ :=
    exists_contDiff_representative_of_weak_divergence hlr hdata.1 hdata.2.1
      hgeom.2.2.1.1 (fun x hx => (hgeom.2.2.2.2.1 x (hsub hx)).ne') hdata.2.2
  exact ⟨v, hv, hue⟩

/-- Original graph membership supplies the local integrability used by
the generic projection lemma. No source regularity is added to N07a. -/
theorem n07a_referenceGraph_strip_integrable
    {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (hborder : RadialTrueBorder D) {γ M₀ M₁ : ℝ}
    {U : RadialUnknown} {F : RadialSource}
    (hgraph : ReferenceGraph D γ M₀ M₁ U F)
    {l r : ℝ} (hsub : Icc l r ⊆ radialCore D) :
    IntegrableOn U.1 (Ioc l r ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) volume ∧
    IntegrableOn F.1 (Ioc l r ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) volume := by
  let Q : Set PolarPoint := Ioc l r ×ˢ Ioc (0 : ℝ) (2 * Real.pi)
  letI : IsFiniteMeasure (volume.restrict Q) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)).trans_lt
      (isCompact_Icc.prod isCompact_Icc).measure_lt_top⟩
  have hmeasure : volume.restrict Q ≤
      (radialPhysicalMeasure D).restrict (Icc l r ×ˢ (univ : Set ℝ)) := by
    rw [radialPhysicalMeasure,
      Measure.restrict_restrict (measurableSet_Icc.prod MeasurableSet.univ)]
    apply Measure.restrict_mono ?_ le_rfl
    intro p hp
    exact ⟨⟨Ioc_subset_Icc_self hp.1, mem_univ p.2⟩,
      ⟨hsub (Ioc_subset_Icc_self hp.1), hp.2⟩⟩
  have hULp := MemLp.mono_measure hmeasure
    (r11b_output_memLp_on_compact hD hborder isCompact_Icc hsub hgraph.1)
  have hFLp := MemLp.mono_measure hmeasure
    (r11b_source_memLp_on_compact hD isCompact_Icc hsub hgraph.2.1)
  exact ⟨hULp.integrable (by norm_num), hFLp.integrable (by norm_num)⟩

/-- The final scalar C1 bridge uses only properties already available
for the actual reference graph. In particular its source may be rough. -/
theorem n07a_referenceGraph_arbitraryAngular_C1
    {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (hborder : RadialTrueBorder D) {γ M₀ M₁ : ℝ}
    {U : RadialUnknown} {F : RadialSource}
    (hgraph : ReferenceGraph D γ M₀ M₁ U F)
    {l r : ℝ} (hlr : l < r) (hsub : Icc l r ⊆ radialCore D)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβp : Function.Periodic β (2 * Real.pi)) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 1 v ∧
      n07aTraceAngularMoment β U.1 =ᵐ[volume.restrict (Ioo l r)] v := by
  obtain ⟨hUi, hFi⟩ := n07a_referenceGraph_strip_integrable hD hborder hgraph hsub
  exact n07a_referenceGraph_product_C1 hD.choose_spec.1 hborder hgraph
    hlr hsub hUi hFi hβ hβp

end ContinuousFlexibility.Radial
