module

public import ContinuousFlexibility.Radial.InnerRadialAffineLift
public import ContinuousFlexibility.Radial.ModeWeakRegularity

/-!
# The actual H¹ traces as values of a continuous representative

The physical value and normalized gradient are the existing two Hilbert
coordinates. Smooth integration by parts extends to their actual closed
zero-endpoint domain. The resulting weak primitive gives a continuous
representative, and the canonical reciprocal-density trace pairings are
its two endpoint values. No regularity or trace identity is assumed of
an arbitrary element of the closed domain.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace
open ContinuousFlexibility.Statements

section TestPairing

variable (D : ReferenceData) (hw : Continuous D.w)
  {a b : ℝ} (hab : a < b) (ha : 0 < a)
  (hcore : Ioo a b ⊆ radialCore D)
  (hpos : ∀ r ∈ Icc a b, 0 < D.w r)

include hw hab ha hcore hpos

theorem matchedInnerH1Zero_test (p : ℝ → ℝ) (hp : ContDiff ℝ ∞ p)
    {q : InnerRadialH1Pair D} (hq : q ∈ innerRadialH1Zero D a b) :
    ⟪q.2, innerRadialTraceGradientTest D hw ha hcore hpos p
        hp.continuous.continuousOn⟫_ℝ +
      ⟪q.1, innerRadialTraceValueTest D hw ha hcore hpos p
        (innerDirichlet_deriv_continuousOn (fun _ _ => hp.contDiffAt))⟫_ℝ = 0 := by
  let Tg := innerRadialTraceGradientTest D hw ha hcore hpos p
    hp.continuous.continuousOn
  let Tv := innerRadialTraceValueTest D hw ha hcore hpos p
    (innerDirichlet_deriv_continuousOn (fun _ _ => hp.contDiffAt))
  have hclosed : IsClosed {q : InnerRadialH1Pair D |
      ⟪q.2, Tg⟫_ℝ + ⟪q.1, Tv⟫_ℝ = 0} :=
    isClosed_eq ((continuous_snd.inner continuous_const).add
      (continuous_fst.inner continuous_const)) continuous_const
  apply (closure_minimal (t := {q : InnerRadialH1Pair D |
      ⟪q.2, Tg⟫_ℝ + ⟪q.1, Tv⟫_ℝ = 0}) ?_ hclosed)
    ((mem_innerRadialH1Zero D a b q).mp hq)
  rintro z ⟨u, hu, _, hs, hzu, hzd⟩
  have hua : u a = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl a) (hs h).1)
  have hub : u b = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl b) (hs h).2)
  have h := innerRadialH1_smooth_trace_pairing D hw hab ha hcore hpos
    (fun _ _ => hu.contDiffAt) (fun _ _ => hp.contDiffAt) hzu hzd
  change ⟪z.2, Tg⟫_ℝ + ⟪z.1, Tv⟫_ℝ = 0
  simpa only [Tg, Tv, hua, hub, mul_zero, sub_self] using h

theorem matchedInnerH1Domain_test (p : ℝ → ℝ) (hp : ContDiff ℝ ∞ p)
    {q : InnerRadialH1Pair D}
    (hq : q ∈ innerRadialH1Domain D hw ha hcore hpos) :
    ⟪q.2, innerRadialTraceGradientTest D hw ha hcore hpos p
        hp.continuous.continuousOn⟫_ℝ +
      ⟪q.1, innerRadialTraceValueTest D hw ha hcore hpos p
        (innerDirichlet_deriv_continuousOn (fun _ _ => hp.contDiffAt))⟫_ℝ =
      p b * innerRadialH1Trace D hw ha hcore hpos q 1 -
        p a * innerRadialH1Trace D hw ha hcore hpos q 0 := by
  let z := innerRadialH1Trace D hw ha hcore hpos q
  let Tg := innerRadialTraceGradientTest D hw ha hcore hpos p
    hp.continuous.continuousOn
  let Tv := innerRadialTraceValueTest D hw ha hcore hpos p
    (innerDirichlet_deriv_continuousOn (fun _ _ => hp.contDiffAt))
  have hz := matchedInnerH1Zero_test D hw hab ha hcore hpos p hp
    ((mem_innerRadialH1Domain D hw ha hcore hpos q).mp hq)
  have hunit (i : Fin 2) :
      ⟪(innerRadialAffineUnitPair D hw ha hcore hpos i).2, Tg⟫_ℝ +
        ⟪(innerRadialAffineUnitPair D hw ha hcore hpos i).1, Tv⟫_ℝ =
        p b * innerEndpointValues i 1 - p a * innerEndpointValues i 0 := by
    have h := innerRadialH1_smooth_trace_pairing D hw hab ha hcore hpos
      (fun _ _ => (innerIntervalAffineLift_contDiff a b
        (innerEndpointValues i)).contDiffAt)
      (fun _ _ => hp.contDiffAt)
      (innerRadialAffineUnitPair_value_ae D hw ha hcore hpos i)
      (innerRadialAffineUnitPair_gradient_ae D hw ha hcore hpos i)
    rw [(innerIntervalAffineLift_endpoints hab (innerEndpointValues i)).1,
      (innerIntervalAffineLift_endpoints hab (innerEndpointValues i)).2] at h
    exact h
  have h₀ := hunit 0
  have h₁ := hunit 1
  norm_num [innerEndpointValues] at h₀ h₁
  simp only [innerRadialAffineLift_apply, Prod.fst_sub, Prod.snd_sub,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    inner_sub_left, inner_add_left, real_inner_smul_left] at hz
  change ⟪q.2, Tg⟫_ℝ + ⟪q.1, Tv⟫_ℝ = p b * z 1 - p a * z 0
  linear_combination hz + z 0 * h₀ + z 1 * h₁

theorem matchedInner_traceGradient_pairing (p : ℝ → ℝ)
    (hp : ContinuousOn p (Icc a b)) (q : RadialModeL2 D) :
    ⟪q, innerRadialTraceGradientTest D hw ha hcore hpos p hp⟫_ℝ =
      ∫ r in a..b, (sqrt 12 / r * q r) * p r := by
  rw [innerRadialTraceGradientTest, innerRadialIntervalToLp_inner_right,
    intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  have hr₀ : r ≠ 0 := (ha.trans hr.1).ne'
  have hw₀ : D.w r ≠ 0 := (hpos r (Ioo_subset_Icc_self hr)).ne'
  dsimp only
  field_simp [hr₀, hw₀]
  <;> ring

theorem matchedInner_traceValue_pairing (p : ℝ → ℝ)
    (hp : ContinuousOn (deriv p) (Icc a b)) (q : RadialModeL2 D) :
    ⟪q, innerRadialTraceValueTest D hw ha hcore hpos p hp⟫_ℝ =
      ∫ r in a..b, q r * deriv p r := by
  rw [innerRadialTraceValueTest, innerRadialIntervalToLp_inner_right,
    intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  have hr₀ : r ≠ 0 := (ha.trans hr.1).ne'
  have hw₀ : D.w r ≠ 0 := (hpos r (Ioo_subset_Icc_self hr)).ne'
  dsimp only
  field_simp [hr₀, hw₀]
  <;> ring

/-- Ordinary first-order integration by parts for an arbitrary element
of the actual physical closed domain. -/
theorem matchedInnerH1Domain_integral_test (p : ℝ → ℝ) (hp : ContDiff ℝ ∞ p)
    {q : InnerRadialH1Pair D}
    (hq : q ∈ innerRadialH1Domain D hw ha hcore hpos) :
    (∫ r in a..b, (sqrt 12 / r * q.2 r) * p r) +
      (∫ r in a..b, q.1 r * deriv p r) =
      p b * innerRadialH1Trace D hw ha hcore hpos q 1 -
        p a * innerRadialH1Trace D hw ha hcore hpos q 0 := by
  have h := matchedInnerH1Domain_test D hw hab ha hcore hpos p hp hq
  rw [matchedInner_traceGradient_pairing D hw hab ha hcore hpos,
    matchedInner_traceValue_pairing D hw hab ha hcore hpos] at h
  exact h

end TestPairing

private theorem matchedInner_primitive_parts
    {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) (c : ℝ)
    (p : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) :
    (∫ r in a..b, f r * p r) +
      (∫ r in a..b, (c + ∫ t in a..r, f t) * deriv p r) =
      p b * (c + ∫ t in a..b, f t) - p a * c := by
  have hpd : Continuous (deriv p) :=
    (contDiff_infty_iff_deriv.mp hp).2.continuous
  have hP := hf.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  have hPi : IntervalIntegrable (fun r => ∫ t in a..r, f t) volume a b :=
    hP.continuousOn.intervalIntegrable
  have hdp : (∫ r in a..b, deriv p r) = p b - p a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le
      hp.continuous.continuousOn
      (fun r _ => (hp.differentiable (by simp) r).hasDerivAt)
      (hpd.intervalIntegrable a b)
  have he :
      (∫ r in a..b, (c + ∫ t in a..r, f t) * deriv p r) =
      c * (∫ r in a..b, deriv p r) +
        ∫ r in a..b, (∫ t in a..r, f t) * deriv p r := by
    simp_rw [add_mul]
    rw [intervalIntegral.integral_add ((hpd.intervalIntegrable a b).const_mul c)
      (hPi.mul_continuousOn hpd.continuousOn), intervalIntegral.integral_const_mul]
  rw [he, hdp, intervalPrimitive_integral_mul_deriv hf
    ((hp.of_le (by simp)).contDiffOn)]
  ring

/-- Every actual first-order domain field has one continuous representative
on the closed interval, and its canonical traces are the endpoint values. -/
theorem matchedInnerH1Domain_continuous_representative
    {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (hw : Continuous D.w) {a b : ℝ} (hab : a < b) (ha : 0 < a)
    (hsub : Icc a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    {q : InnerRadialH1Pair D}
    (hq : q ∈ innerRadialH1Domain D hw ha
      (Ioo_subset_Icc_self.trans hsub) hpos) :
    ∃ v : ℝ → ℝ, ContinuousOn v (Icc a b) ∧
      (q.1 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] v ∧
      v a = innerRadialH1Trace D hw ha (Ioo_subset_Icc_self.trans hsub) hpos q 0 ∧
      v b = innerRadialH1Trace D hw ha (Ioo_subset_Icc_self.trans hsub) hpos q 1 := by
  let g (r : ℝ) := sqrt 12 / r * q.2 r
  have hg : IntervalIntegrable g volume a b := by
    have hc : ContinuousOn (fun r : ℝ => sqrt 12 / r) (Icc a b) :=
      continuousOn_const.div continuousOn_id (fun r hr => (ha.trans_le hr.1).ne')
    have hc' : ContinuousOn (fun r : ℝ => sqrt 12 / r) (uIcc a b) := by
      simpa only [uIcc_of_le hab.le] using hc
    simpa only [g, mul_comm] using
      (matchingMode_intervalIntegrable hD q.2 hab.le hsub).mul_continuousOn hc'
  have hweak : ∀ p : ℝ → ℝ, ContDiff ℝ ∞ p → HasCompactSupport p →
      tsupport p ⊆ Ioo a b →
      (∫ r in a..b, q.1 r * deriv p r) = -(∫ r in a..b, g r * p r) := by
    intro p hp _ hs
    have hpa : p a = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl a) (hs h).1)
    have hpb : p b = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl b) (hs h).2)
    have h := matchedInnerH1Domain_integral_test D hw hab ha
      (Ioo_subset_Icc_self.trans hsub) hpos p hp hq
    rw [hpa, hpb, zero_mul, zero_mul, sub_self] at h
    change (∫ r in a..b, g r * p r) + (∫ r in a..b, q.1 r * deriv p r) = 0 at h
    linarith only [h]
  obtain ⟨c, hc⟩ := exists_ae_intervalPrimitive_of_weakDeriv_tsupport hab
    (matchingMode_intervalIntegrable hD q.1 hab.le hsub) hg hweak
  let v (r : ℝ) := c + ∫ t in a..r, g t
  have hP := hg.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  have hv : ContinuousOn v (Icc a b) := by
    have hc' : ContinuousOn (fun _ : ℝ => c) (Icc a b) := continuousOn_const
    exact hc'.add (by simpa only [uIcc_of_le hab.le] using hP.continuousOn)
  have hboundary (p : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) :
      p b * v b - p a * v a =
        p b * innerRadialH1Trace D hw ha (Ioo_subset_Icc_self.trans hsub) hpos q 1 -
          p a * innerRadialH1Trace D hw ha (Ioo_subset_Icc_self.trans hsub) hpos q 0 := by
    have he : (∫ r in a..b, q.1 r * deriv p r) =
        ∫ r in a..b, v r * deriv p r := by
      simp only [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
      apply integral_congr_ae
      filter_upwards [hc] with r hr
      rw [hr]
    have h := matchedInnerH1Domain_integral_test D hw hab ha
      (Ioo_subset_Icc_self.trans hsub) hpos p hp hq
    rw [he] at h
    have hp' := matchedInner_primitive_parts hab hg c p hp
    have hva : v a = c := by simp only [v, intervalIntegral.integral_same, add_zero]
    change (∫ r in a..b, g r * p r) + (∫ r in a..b, v r * deriv p r) =
      p b * v b - p a * c at hp'
    rw [hva]
    exact hp'.symm.trans h
  refine ⟨v, hv, hc, ?_, ?_⟩
  · have h := hboundary (innerIntervalAffineLift a b (innerEndpointValues 0))
      (innerIntervalAffineLift_contDiff a b (innerEndpointValues 0))
    rw [(innerIntervalAffineLift_endpoints hab (innerEndpointValues 0)).1,
      (innerIntervalAffineLift_endpoints hab (innerEndpointValues 0)).2] at h
    simpa [innerEndpointValues] using h
  · have h := hboundary (innerIntervalAffineLift a b (innerEndpointValues 1))
      (innerIntervalAffineLift_contDiff a b (innerEndpointValues 1))
    rw [(innerIntervalAffineLift_endpoints hab (innerEndpointValues 1)).1,
      (innerIntervalAffineLift_endpoints hab (innerEndpointValues 1)).2] at h
    simpa [innerEndpointValues] using h

/-- Any continuous representative has those same actual endpoint values.
In particular this applies to the C¹ representative obtained from the
modal differential equation. -/
theorem matchedInnerH1Domain_trace_of_representative
    {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (hw : Continuous D.w) {a b : ℝ} (hab : a < b) (ha : 0 < a)
    (hsub : Icc a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    {q : InnerRadialH1Pair D}
    (hq : q ∈ innerRadialH1Domain D hw ha
      (Ioo_subset_Icc_self.trans hsub) hpos)
    {v : ℝ → ℝ} (hv : ContinuousOn v (Icc a b))
    (hrep : (q.1 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] v) :
    v a = innerRadialH1Trace D hw ha (Ioo_subset_Icc_self.trans hsub) hpos q 0 ∧
      v b = innerRadialH1Trace D hw ha (Ioo_subset_Icc_self.trans hsub) hpos q 1 := by
  obtain ⟨u, hu, hqu, hua, hub⟩ :=
    matchedInnerH1Domain_continuous_representative hD hw hab ha hsub hpos hq
  have he : u =ᵐ[volume.restrict (Icc a b)] v := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact hqu.symm.trans hrep
  have hp := Measure.eqOn_Icc_of_ae_eq volume hab.ne he hu hv
  exact ⟨(hp ⟨le_rfl, hab.le⟩).symm.trans hua,
    (hp ⟨hab.le, le_rfl⟩).symm.trans hub⟩

end ContinuousFlexibility.Radial
