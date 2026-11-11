import ContinuousFlexibility.Radial.InnerRadialEnergyDomain
import ContinuousFlexibility.Radial.InnerRadialL2Pairing
import ContinuousFlexibility.Radial.InnerIntervalTrace

/-!
# Canonical physical traces and fixed affine lifts

The trace is determined by the value and normalized derivative in the
actual measure μ_D. Reciprocal-density affine test functions convert
the two L² pairings to the ordinary fundamental theorem of calculus.
The zero-endpoint closure has trace zero. Fixed physical affine lifts
then define the full first-order domain without an independent trace
label or an assumed gluing property.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace BigOperators

section PhysicalTrace

variable (D : ReferenceData) (hw : Continuous D.w)
  {a b : ℝ} (hab : a < b) (ha : 0 < a)
  (hcore : Ioo a b ⊆ radialCore D)
  (hpos : ∀ r ∈ Icc a b, 0 < D.w r)

private theorem traceGradientTest_continuousOn (p : ℝ → ℝ)
    (hp : ContinuousOn p (Icc a b)) :
    ContinuousOn (fun r => (Real.sqrt 12 * r / (12 * D.w r)) * p r) (Icc a b) :=
  (((continuousOn_const.mul continuousOn_id).div
    (continuousOn_const.mul hw.continuousOn)
    (fun r hr => mul_ne_zero (by norm_num) (hpos r hr).ne')).mul hp)

private theorem traceValueTest_continuousOn (p : ℝ → ℝ)
    (hp : ContinuousOn (deriv p) (Icc a b)) :
    ContinuousOn (fun r => (r ^ 2 / (12 * D.w r)) * deriv p r) (Icc a b) :=
  (((continuousOn_id.pow 2).div
    (continuousOn_const.mul hw.continuousOn)
    (fun r hr => mul_ne_zero (by norm_num) (hpos r hr).ne')).mul hp)

/-- The test paired with the normalized derivative coordinate. -/
def innerRadialTraceGradientTest (p : ℝ → ℝ)
    (hp : ContinuousOn p (Icc a b)) : RadialModeL2 D :=
  innerRadialIntervalToLp D hw ha hcore
    (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le)
    (fun r => (Real.sqrt 12 * r / (12 * D.w r)) * p r)
    (traceGradientTest_continuousOn D hw hpos p hp)

/-- The test paired with the field coordinate. -/
def innerRadialTraceValueTest (p : ℝ → ℝ)
    (hp : ContinuousOn (deriv p) (Icc a b)) : RadialModeL2 D :=
  innerRadialIntervalToLp D hw ha hcore
    (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le)
    (fun r => (r ^ 2 / (12 * D.w r)) * deriv p r)
    (traceValueTest_continuousOn D hw hpos p hp)

/-- The physical density and normalized derivative cancel exactly in
the trace pairings. No norm-equivalence assumption is used. -/
theorem innerRadialH1_smooth_trace_pairing
    {φ p : ℝ → ℝ}
    (hφ : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ φ x)
    (hp : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ p x)
    {q : InnerRadialH1Pair D}
    (hu : (q.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator φ)
    (hd : (q.2 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (innerGapGradientField φ)) :
    ⟪q.2, innerRadialTraceGradientTest D hw ha hcore hpos p
      (fun x hx => (hp x hx).continuousAt.continuousWithinAt)⟫_ℝ +
    ⟪q.1, innerRadialTraceValueTest D hw ha hcore hpos p
      (innerDirichlet_deriv_continuousOn hp)⟫_ℝ =
      p b * φ b - p a * φ a := by
  have hφc : ContinuousOn φ (Icc a b) :=
    fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  have hφdc := innerDirichlet_deriv_continuousOn hφ
  have hpc : ContinuousOn p (Icc a b) :=
    fun x hx => (hp x hx).continuousAt.continuousWithinAt
  have hpdc := innerDirichlet_deriv_continuousOn hp
  have hgc : ContinuousOn (innerGapGradientField φ) (Icc a b) :=
    (continuousOn_id.div_const (Real.sqrt 12)).mul hφdc
  have huEq : q.1 = innerRadialIntervalToLp D hw ha hcore
      (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) φ hφc :=
    Lp.ext (hu.trans (innerRadialIntervalToLp_ae D hw ha hcore
      (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) φ hφc).symm)
  have hdEq : q.2 = innerRadialIntervalToLp D hw ha hcore
      (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le)
      (innerGapGradientField φ) hgc :=
    Lp.ext (hd.trans (innerRadialIntervalToLp_ae D hw ha hcore
      (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le)
      (innerGapGradientField φ) hgc).symm)
  have hsqrt : Real.sqrt 12 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hpair₁ :
      ⟪q.2, innerRadialTraceGradientTest D hw ha hcore hpos p hpc⟫_ℝ =
        ∫ r in a..b, deriv φ r * p r := by
    rw [hdEq, innerRadialTraceGradientTest,
      innerRadialIntervalToLp_inner D hw hab.le ha hcore]
    apply intervalIntegral.integral_congr
    intro r hr
    have hrcc : r ∈ Icc a b := by simpa only [uIcc_of_le hab.le] using hr
    have hr0 : r ≠ 0 := (ha.trans_le hrcc.1).ne'
    have hw0 : D.w r ≠ 0 := (hpos r hrcc).ne'
    dsimp only [innerGapGradientField]
    field_simp [hr0, hw0, hsqrt] <;> ring
  have hpair₂ :
      ⟪q.1, innerRadialTraceValueTest D hw ha hcore hpos p hpdc⟫_ℝ =
        ∫ r in a..b, φ r * deriv p r := by
    rw [huEq, innerRadialTraceValueTest,
      innerRadialIntervalToLp_inner D hw hab.le ha hcore]
    apply intervalIntegral.integral_congr
    intro r hr
    have hrcc : r ∈ Icc a b := by simpa only [uIcc_of_le hab.le] using hr
    have hr0 : r ≠ 0 := (ha.trans_le hrcc.1).ne'
    have hw0 : D.w r ≠ 0 := (hpos r hrcc).ne'
    field_simp [hr0, hw0] <;> ring
  have hI₁ := (hφdc.mul hpc).intervalIntegrable_of_Icc hab.le
  have hI₂ := (hφc.mul hpdc).intervalIntegrable_of_Icc hab.le
  rw [hpair₁, hpair₂, ← intervalIntegral.integral_add hI₁ hI₂]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le
    (hφc.mul hpc)
    (fun x hx => ((hφ x (Ioo_subset_Icc_self hx)).differentiableAt (by simp)).hasDerivAt.mul
      ((hp x (Ioo_subset_Icc_self hx)).differentiableAt (by simp)).hasDerivAt)
    (hI₁.add hI₂)
  simpa only [Pi.mul_apply, mul_comm] using hFTC

/-- A continuous trace map on the actual physical value/gradient pair. -/
def innerRadialH1Trace : InnerRadialH1Pair D →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun q i := bufferSign i *
    (⟪q.2, innerRadialTraceGradientTest D hw ha hcore hpos
      (innerIntervalAffineLift a b (innerEndpointValues i))
      (innerIntervalAffineLift_contDiff a b (innerEndpointValues i)).continuous.continuousOn⟫_ℝ +
    ⟪q.1, innerRadialTraceValueTest D hw ha hcore hpos
      (innerIntervalAffineLift a b (innerEndpointValues i))
      ((innerIntervalAffineLift_contDiff a b (innerEndpointValues i)).continuous_deriv
        (by simp)).continuousOn⟫_ℝ)
  map_add' q r := by
    funext i
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, inner_add_left]
    ring
  map_smul' c q := by
    funext i
    simp only [Prod.fst_smul, Prod.snd_smul, Pi.smul_apply,
      real_inner_smul_left, smul_eq_mul]
    ring

theorem innerRadialH1Trace_smooth {φ : ℝ → ℝ}
    (hφ : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ φ x)
    {q : InnerRadialH1Pair D}
    (hu : (q.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator φ)
    (hd : (q.2 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (innerGapGradientField φ))
    (i : Fin 2) :
    innerRadialH1Trace D hw ha hcore hpos q i = if i = 0 then φ a else φ b := by
  have hp := innerRadialH1_smooth_trace_pairing D hw hab ha hcore hpos hφ
    (fun _ _ => (innerIntervalAffineLift_contDiff a b (innerEndpointValues i)).contDiffAt) hu hd
  have hends := innerIntervalAffineLift_endpoints hab (innerEndpointValues i)
  rw [hends.1, hends.2] at hp
  change bufferSign i * _ = _
  rw [hp]
  fin_cases i <;> norm_num [bufferSign, innerEndpointValues]

/-- The trace vanishes on the physical zero-endpoint closure. -/
theorem innerRadialH1Trace_zero {q : InnerRadialH1Pair D}
    (hq : q ∈ innerRadialH1Zero D a b) :
    innerRadialH1Trace D hw ha hcore hpos q = 0 := by
  have hqcl := (mem_innerRadialH1Zero D a b q).mp hq
  funext i
  have hcont : Continuous (fun q : InnerRadialH1Pair D =>
      innerRadialH1Trace D hw ha hcore hpos q i) := by
    exact continuous_const.mul
      ((continuous_snd.inner continuous_const).add
        (continuous_fst.inner continuous_const))
  apply (closure_minimal (t := {q | innerRadialH1Trace D hw ha hcore hpos q i = 0})
    ?_ (isClosed_eq hcont continuous_const)) hqcl
  intro r hr
  rcases hr with ⟨φ, hφ, _, hs, hu, hd⟩
  have hφa : φ a = 0 := image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl a) (hs h).1)
  have hφb : φ b = 0 := image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl b) (hs h).2)
  rw [innerRadialH1Trace_smooth D hw hab ha hcore hpos
    (fun _ _ => hφ.contDiffAt) hu hd, hφa, hφb, ite_self]

end PhysicalTrace

end ContinuousFlexibility.Radial
