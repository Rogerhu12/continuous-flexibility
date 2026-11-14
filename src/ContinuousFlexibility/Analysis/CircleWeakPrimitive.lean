module

public import ContinuousFlexibility.Analysis.CircleJetBonding
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology

namespace ContinuousFlexibility.Statements

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- Periodic extension of a test supported strictly inside one period. -/
def anglePeriodize (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  φ (toIocMod Real.pi_pos 0 x)

theorem anglePeriodize_periodic (φ : ℝ → ℝ) :
    Function.Periodic (anglePeriodize φ) Real.pi := by
  intro x
  simp only [anglePeriodize, toIocMod_add_right]

theorem anglePeriodize_eqOn (φ : ℝ → ℝ) :
    EqOn (anglePeriodize φ) φ (Ioc 0 Real.pi) := by
  intro x hx
  have hmod : toIocMod Real.pi_pos 0 x = x :=
    (toIocMod_eq_self Real.pi_pos).mpr (by simpa only [zero_add] using hx)
  simp only [anglePeriodize, hmod]

theorem contDiff_anglePeriodize {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hs : tsupport φ ⊆ Ioo 0 Real.pi) : ContDiff ℝ ∞ (anglePeriodize φ) := by
  have h0 : (0 : ℝ) ∉ tsupport φ := fun h => (lt_irrefl (0 : ℝ)) (hs h).1
  have hπ : Real.pi ∉ tsupport φ := fun h => (lt_irrefl Real.pi) (hs h).2
  have hs0 : ∀ᶠ x in 𝓝 (0 : ℝ), x ∈ (tsupport φ)ᶜ :=
    (isClosed_tsupport φ).isOpen_compl.mem_nhds h0
  have hsπ : ∀ᶠ x in 𝓝 Real.pi, x ∈ (tsupport φ)ᶜ :=
    (isClosed_tsupport φ).isOpen_compl.mem_nhds hπ
  have hz0 : ∀ᶠ x in 𝓝 (0 : ℝ), φ x = 0 :=
    hs0.mono fun _ h => image_eq_zero_of_notMem_tsupport h
  have hzπ : ∀ᶠ x in 𝓝 Real.pi, φ x = 0 :=
    hsπ.mono fun _ h => image_eq_zero_of_notMem_tsupport h
  have htranslate : Tendsto (fun x : ℝ => x - Real.pi) (𝓝 Real.pi) (𝓝 (0 : ℝ)) := by
    have hcont : Continuous (fun x : ℝ => x - Real.pi) :=
      continuous_id.sub continuous_const
    simpa only [sub_self] using hcont.tendsto Real.pi
  have hseam : anglePeriodize φ =ᶠ[𝓝 Real.pi] (fun _ : ℝ => 0) := by
    have hnear : ∀ᶠ x in 𝓝 Real.pi, x ∈ Ioo (0 : ℝ) (2 * Real.pi) :=
      isOpen_Ioo.mem_nhds ⟨Real.pi_pos, by linarith [Real.pi_pos]⟩
    filter_upwards [hnear, hzπ, htranslate.eventually hz0] with x hx hxπ hx0
    by_cases hle : x ≤ Real.pi
    · exact (anglePeriodize_eqOn φ ⟨hx.1, hle⟩).trans hxπ
    · have hx' : x - Real.pi ∈ Ioc (0 : ℝ) Real.pi :=
        ⟨sub_pos.mpr (lt_of_not_ge hle), by linarith [hx.2]⟩
      calc
        anglePeriodize φ x = anglePeriodize φ (x - Real.pi + Real.pi) := by
          rw [sub_add_cancel]
        _ = anglePeriodize φ (x - Real.pi) := anglePeriodize_periodic φ _
        _ = 0 := (anglePeriodize_eqOn φ hx').trans hx0
  have hbase : ∀ y ∈ Ioc (0 : ℝ) Real.pi, ContDiffAt ℝ ∞ (anglePeriodize φ) y := by
    intro y hy
    rcases hy.2.eq_or_lt with hye | hyl
    · subst y
      exact contDiffAt_const.congr_of_eventuallyEq hseam
    · apply hφ.contDiffAt.congr_of_eventuallyEq
      filter_upwards [isOpen_Ioo.mem_nhds (show y ∈ Ioo (0 : ℝ) Real.pi from ⟨hy.1, hyl⟩)]
        with z hz
      exact anglePeriodize_eqOn φ ⟨hz.1, hz.2.le⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  have hmod : toIocMod Real.pi_pos 0 x ∈ Ioc (0 : ℝ) Real.pi := by
    simpa only [zero_add] using toIocMod_mem_Ioc Real.pi_pos 0 x
  have hx := hbase _ hmod
  let n := toIocDiv Real.pi_pos 0 x
  have hshift : ContDiffAt ℝ ∞ (fun y : ℝ => y - n • Real.pi) x :=
    (contDiff_id.sub contDiff_const).contDiffAt
  have hc : ContDiffAt ℝ ∞ (anglePeriodize φ ∘ fun y : ℝ => y - n • Real.pi) x :=
    ContDiffAt.comp (f := fun y : ℝ => y - n • Real.pi) x hx hshift
  have he : (anglePeriodize φ ∘ fun y : ℝ => y - n • Real.pi) = anglePeriodize φ := by
    funext y
    simp only [Function.comp_apply, anglePeriodize, toIocMod_sub_zsmul]
  rwa [he] at hc

private theorem angleMeasure_eq_restrict_Ioo :
    angleMeasure = volume.restrict (Ioo (0 : ℝ) Real.pi) :=
  restrict_Ioo_eq_restrict_Ioc.symm

/-- Smooth periodic tests separate integrable functions on the actual angular measure. -/
theorem ae_eq_zero_of_integral_periodic_angle {f : ℝ → ℝ} (hf : Integrable f angleMeasure)
    (h : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → Function.Periodic φ Real.pi →
      (∫ x, f x * φ x ∂angleMeasure) = 0) : ∀ᵐ x ∂angleMeasure, f x = 0 := by
  have hlocal : LocallyIntegrableOn f (Ioo (0 : ℝ) Real.pi) volume := by
    apply IntegrableOn.locallyIntegrableOn
    simpa only [IntegrableOn, ← angleMeasure_eq_restrict_Ioo] using hf
  rw [angleMeasure_eq_restrict_Ioo, ae_restrict_iff' measurableSet_Ioo]
  apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocal
  intro φ hφ _ hs
  have he : (∫ x, φ x • f x) = ∫ x, φ x • f x ∂angleMeasure := by
    change _ = ∫ x in Ioc (0 : ℝ) Real.pi, φ x • f x
    rw [← integral_indicator measurableSet_Ioc]
    apply congrArg (fun g : ℝ → ℝ => ∫ x, g x)
    funext x
    by_cases hx : x ∈ Ioc (0 : ℝ) Real.pi
    · rw [indicator_of_mem hx]
    · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hh => hx ⟨(hs hh).1, (hs hh).2.le⟩)
      rw [indicator_of_notMem hx, hz, zero_smul]
  rw [he]
  calc
    (∫ x, φ x • f x ∂angleMeasure) = ∫ x, f x * anglePeriodize φ x ∂angleMeasure := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      change φ x • f x = f x * anglePeriodize φ x
      rw [anglePeriodize_eqOn φ hx, smul_eq_mul, mul_comm]
    _ = 0 := h _ (contDiff_anglePeriodize hφ hs) (anglePeriodize_periodic φ)

private theorem isFiniteMeasure_angle : IsFiniteMeasure angleMeasure :=
  ⟨by
    rw [angleMeasure, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
    exact ENNReal.ofReal_lt_top⟩

theorem integrable_angleL2 (f : AngleL2) : Integrable f angleMeasure := by
  let : IsFiniteMeasure angleMeasure := isFiniteMeasure_angle
  exact (Lp.memLp f).integrable (by norm_num)

theorem angleL2_eq_zero_of_integral_periodic (f : AngleL2)
    (h : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → Function.Periodic φ Real.pi →
      (∫ x, f x * φ x ∂angleMeasure) = 0) : f = 0 := by
  apply Lp.ext
  filter_upwards [ae_eq_zero_of_integral_periodic_angle (integrable_angleL2 f) h,
    Lp.coeFn_zero (E := ℝ) (p := 2) (μ := angleMeasure)] with x hf h0
  exact hf.trans h0.symm

/-- The signed integral of the weak derivative, based at the left endpoint. -/
def angleIntegralPrimitive (d : AngleL2) (x : ℝ) : ℝ :=
  ∫ y in 0..x, d y ∂angleMeasure

theorem continuous_angleIntegralPrimitive (d : AngleL2) :
    Continuous (angleIntegralPrimitive d) := by
  let : NullSingletonClass angleMeasure := by
    unfold angleMeasure
    infer_instance
  exact (integrable_angleL2 d).continuous_primitive 0

theorem angleIntegralPrimitive_eq_integral_volume (d : AngleL2) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) Real.pi) :
    angleIntegralPrimitive d x = ∫ y in 0..x, d y := by
  rw [angleIntegralPrimitive, intervalIntegral.integral_of_le hx.1,
    intervalIntegral.integral_of_le hx.1]
  change (∫ y, d y ∂(volume.restrict (Ioc (0 : ℝ) Real.pi)).restrict (Ioc 0 x)) = _
  rw [Measure.restrict_restrict_of_subset (Ioc_subset_Ioc_right hx.2)]

theorem integral_angleL2_eq_zero_of_hasWeakAngularDerivative {f d : AngleL2}
    (h : HasWeakAngularDerivative f d 1) : (∫ x, d x ∂angleMeasure) = 0 := by
  simpa only [mul_one, iteratedDeriv_one, deriv_const, mul_zero, integral_zero] using
    h (fun _ => 1) contDiff_const (fun _ => rfl)

theorem angleIntegralPrimitive_endpoints {f d : AngleL2}
    (h : HasWeakAngularDerivative f d 1) :
    angleIntegralPrimitive d 0 = 0 ∧ angleIntegralPrimitive d Real.pi = 0 := by
  refine ⟨intervalIntegral.integral_same, ?_⟩
  rw [angleIntegralPrimitive, intervalIntegral.integral_of_le Real.pi_pos.le]
  change (∫ x, d x ∂(volume.restrict (Ioc (0 : ℝ) Real.pi)).restrict (Ioc 0 Real.pi)) = 0
  rw [Measure.restrict_restrict_of_subset Subset.rfl]
  exact integral_angleL2_eq_zero_of_hasWeakAngularDerivative h

/-- Integration by parts for an angular integral primitive and a smooth test.
Fubini on the triangle gives the identity for the genuine L² representative. -/
theorem integral_angleIntegralPrimitive_mul_deriv (d : AngleL2)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    (∫ x, angleIntegralPrimitive d x * deriv φ x ∂angleMeasure) =
      φ Real.pi * (∫ x, d x ∂angleMeasure) - ∫ x, d x * φ x ∂angleMeasure := by
  let W : Set (ℝ × ℝ) := {p | p.2 ≤ p.1}
  let K (x y : ℝ) : ℝ := W.indicator (fun p => deriv φ p.1 * d p.2) (x, y)
  have hW : MeasurableSet W := measurableSet_le measurable_snd measurable_fst
  let : IsFiniteMeasure angleMeasure := isFiniteMeasure_angle
  have hφ' := (contDiff_infty_iff_deriv.mp hφ).2
  have hφ'i : Integrable (deriv φ) angleMeasure :=
    (memLp_angleMeasure_of_continuous hφ'.continuous).integrable (by norm_num)
  have hd := integrable_angleL2 d
  have hK : Integrable (Function.uncurry K) (angleMeasure.prod angleMeasure) :=
    (hφ'i.mul_prod hd).indicator hW
  have hmem : ∀ᵐ x ∂angleMeasure, x ∈ Ioc (0 : ℝ) Real.pi :=
    ae_restrict_mem measurableSet_Ioc
  have hleft (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) Real.pi) :
      (∫ y, K x y ∂angleMeasure) = angleIntegralPrimitive d x * deriv φ x := by
    have hfun : K x = (Iic x).indicator (fun y => deriv φ x * d y) := by
      funext y
      by_cases hy : y ≤ x <;> simp [K, W, hy]
    rw [hfun, integral_indicator measurableSet_Iic, integral_const_mul, angleIntegralPrimitive,
      intervalIntegral.integral_of_le hx.1.le]
    have hr : angleMeasure.restrict (Iic x) = angleMeasure.restrict (Ioc 0 x) := by
      unfold angleMeasure
      rw [Measure.restrict_restrict measurableSet_Iic,
        Measure.restrict_restrict_of_subset (Ioc_subset_Ioc_right hx.2)]
      have hs : Iic x ∩ Ioc (0 : ℝ) Real.pi = Ioc 0 x := by
        ext y
        simp only [mem_inter_iff, mem_Iic, mem_Ioc]
        exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans hx.2⟩⟩
      rw [hs]
    rw [hr, mul_comm]
  have hright (y : ℝ) (hy : y ∈ Ioc (0 : ℝ) Real.pi) :
      (∫ x, K x y ∂angleMeasure) = d y * (φ Real.pi - φ y) := by
    have hfun : (fun x => K x y) = (Ici y).indicator (fun x => d y * deriv φ x) := by
      funext x
      by_cases hx : y ≤ x <;> simp [K, W, hx, mul_comm]
    rw [hfun, integral_indicator measurableSet_Ici, integral_const_mul]
    have hr : angleMeasure.restrict (Ici y) = volume.restrict (Ioc y Real.pi) := by
      unfold angleMeasure
      rw [Measure.restrict_restrict measurableSet_Ici]
      have hs : Ici y ∩ Ioc (0 : ℝ) Real.pi = Icc y Real.pi := by
        ext x
        simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
        exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hy.1.trans_le h.1, h.2⟩⟩
      rw [hs, ← restrict_Ioc_eq_restrict_Icc]
    rw [hr, ← intervalIntegral.integral_of_le hy.2,
      intervalIntegral.integral_deriv_eq_sub (fun x _ => hφ.differentiable (by simp) x)
        (hφ'.continuous.intervalIntegrable _ _)]
  calc
    (∫ x, angleIntegralPrimitive d x * deriv φ x ∂angleMeasure) =
        ∫ x, (∫ y, K x y ∂angleMeasure) ∂angleMeasure :=
      integral_congr_ae (hmem.mono fun x hx => (hleft x hx).symm)
    _ = ∫ y, (∫ x, K x y ∂angleMeasure) ∂angleMeasure := integral_integral_swap hK
    _ = ∫ y, d y * (φ Real.pi - φ y) ∂angleMeasure :=
      integral_congr_ae (hmem.mono hright)
    _ = _ := by
      simp_rw [mul_sub]
      have hprod : Integrable (fun y => d y * φ y) angleMeasure :=
        (Lp.memLp d).integrable_mul (memLp_angleMeasure_of_continuous hφ.continuous)
      rw [integral_sub (hd.mul_const (φ Real.pi)) hprod, integral_mul_const, mul_comm]

/-- Average with respect to the actual angular measure. -/
def angleMean (f : ℝ → ℝ) : ℝ := (∫ x, f x ∂angleMeasure) / Real.pi

private theorem integral_angle_const (c : ℝ) : (∫ _ : ℝ, c ∂angleMeasure) = Real.pi * c := by
  have hm : angleMeasure univ = ENNReal.ofReal Real.pi := by
    rw [angleMeasure, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
  simp only [integral_const, measureReal_def, hm, ENNReal.toReal_ofReal Real.pi_pos.le, smul_eq_mul]

private theorem integral_angle_sub_mean {f : ℝ → ℝ} (hf : Integrable f angleMeasure) :
    (∫ x, f x - angleMean f ∂angleMeasure) = 0 := by
  let : IsFiniteMeasure angleMeasure := isFiniteMeasure_angle
  rw [integral_sub hf (integrable_const _), integral_angle_const, angleMean]
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ Real.pi_ne_zero, sub_self]

/-- Every smooth periodic test minus its angular mean has a smooth periodic
primitive. -/
theorem exists_contDiff_periodic_deriv_sub_angleMean {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψp : Function.Periodic ψ Real.pi) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ Function.Periodic φ Real.pi ∧
      deriv φ = fun x => ψ x - angleMean ψ := by
  let f : ℝ → ℝ := fun x => ψ x - angleMean ψ
  have hf : ContDiff ℝ ∞ f := hψ.sub contDiff_const
  have hp : Function.Periodic f Real.pi := by
    intro x
    change ψ (x + Real.pi) - angleMean ψ = ψ x - angleMean ψ
    rw [hψp x]
  let φ (x : ℝ) : ℝ := ∫ y in 0..x, f y
  have hd (x : ℝ) : HasDerivAt φ (f x) x :=
    intervalIntegral.integral_hasDerivAt_right (hf.continuous.intervalIntegrable _ _)
      hf.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuous.continuousAt
  have hder : deriv φ = f := funext fun x => (hd x).deriv
  have hφ : ContDiff ℝ ∞ φ := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun x => (hd x).differentiableAt, ?_⟩
    rw [hder]
    exact hf
  refine ⟨φ, hφ, ?_, hder⟩
  intro x
  have hmean : (∫ y in (0 : ℝ)..Real.pi, f y) = 0 := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le]
    let : IsFiniteMeasure angleMeasure := isFiniteMeasure_angle
    exact integral_angle_sub_mean
      ((memLp_angleMeasure_of_continuous hψ.continuous).integrable (by norm_num))
  change (∫ y in (0 : ℝ)..x + Real.pi, f y) = ∫ y in (0 : ℝ)..x, f y
  rw [hp.intervalIntegral_add_eq_add 0 x (fun a b => hf.continuous.intervalIntegrable a b),
    zero_add, hmean, add_zero]

private theorem ae_eq_angleMean_of_integral_deriv_zero {k : ℝ → ℝ}
    (hk : MemLp k 2 angleMeasure)
    (h : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → Function.Periodic φ Real.pi →
      (∫ x, k x * deriv φ x ∂angleMeasure) = 0) :
    k =ᵐ[angleMeasure] (fun _ => angleMean k) := by
  let : IsFiniteMeasure angleMeasure := isFiniteMeasure_angle
  have hki := hk.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hz : ∀ᵐ x ∂angleMeasure, k x - angleMean k = 0 := by
    apply ae_eq_zero_of_integral_periodic_angle (hki.sub (integrable_const _))
    intro ψ hψ hp
    obtain ⟨φ, hφ, hφp, hder⟩ := exists_contDiff_periodic_deriv_sub_angleMean hψ hp
    have hψ₂ := memLp_angleMeasure_of_continuous hψ.continuous
    have hψi := hψ₂.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hφk := h φ hφ hφp
    rw [hder] at hφk
    simp only [mul_sub] at hφk
    have hprod : Integrable (fun x => k x * ψ x) angleMeasure := hk.integrable_mul hψ₂
    rw [integral_sub hprod (hki.mul_const (angleMean ψ)), integral_mul_const] at hφk
    have heq := sub_eq_zero.mp hφk
    change (∫ x, (k x - angleMean k) * ψ x ∂angleMeasure) = 0
    simp only [sub_mul]
    rw [integral_sub hprod (hψi.const_mul (angleMean k)), integral_const_mul, heq]
    simp only [angleMean]
    ring
  exact hz.mono fun _ h0 => sub_eq_zero.mp h0

/-- A first weak derivative gives the actual integral representative almost
everywhere. The representative takes the same value at both endpoints. -/
theorem exists_angleIntegralPrimitive_rep_of_hasWeakAngularDerivative {f d : AngleL2}
    (h : HasWeakAngularDerivative f d 1) :
    ∃ c : ℝ, (⇑f =ᵐ[angleMeasure] fun x => c + angleIntegralPrimitive d x) ∧
      c + angleIntegralPrimitive d 0 = c + angleIntegralPrimitive d Real.pi := by
  let k (x : ℝ) := f x - angleIntegralPrimitive d x
  have hp := memLp_angleMeasure_of_continuous (continuous_angleIntegralPrimitive d)
  have hf := Lp.memLp f
  have hk : MemLp k 2 angleMeasure := hf.sub hp
  have hw (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hper : Function.Periodic φ Real.pi) :
      (∫ x, k x * deriv φ x ∂angleMeasure) = 0 := by
    have hwd := h φ hφ hper
    simp only [iteratedDeriv_one, pow_one, neg_one_mul] at hwd
    have hφ' := memLp_angleMeasure_of_continuous ((contDiff_infty_iff_deriv.mp hφ).2.continuous)
    have hi := integral_angleIntegralPrimitive_mul_deriv d hφ
    rw [integral_angleL2_eq_zero_of_hasWeakAngularDerivative h, mul_zero, zero_sub] at hi
    simp only [k, sub_mul]
    have hfirst : Integrable (fun x => f x * deriv φ x) angleMeasure := hf.integrable_mul hφ'
    have hsecond : Integrable (fun x => angleIntegralPrimitive d x * deriv φ x) angleMeasure :=
      hp.integrable_mul hφ'
    rw [integral_sub hfirst hsecond]
    linarith
  refine ⟨angleMean k, ?_, ?_⟩
  · filter_upwards [ae_eq_angleMean_of_integral_deriv_zero hk hw] with x hx
    change f x - angleIntegralPrimitive d x = angleMean k at hx
    linarith
  · obtain ⟨h₀, hπ⟩ := angleIntegralPrimitive_endpoints h
    rw [h₀, hπ]

end

end ContinuousFlexibility.Statements
