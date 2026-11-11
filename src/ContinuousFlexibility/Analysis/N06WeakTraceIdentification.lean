import ContinuousFlexibility.Analysis.N06WeakModeRegularity
import ContinuousFlexibility.Radial.InnerIntervalTrace
import ContinuousFlexibility.Radial.InnerRadialSmoothGreen

/-!
# True endpoint values and conormals of weak modal solutions

Absolute continuity is enough to identify the existing L2 trace pairings
with endpoint values. Applied to the actual flux `a * v'`, integration by
parts identifies the fixed affine-lift weak conormal with `a * v'` at the
two endpoints. The final modal theorem obtains the same C1/H2
representative from the original L2 distributional equation.

No smooth forcing, prescribed boundary values, or additional weak-domain
condition is introduced. The finite-interface gluing theorem is not
reproved here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements
open scoped ContDiff Topology InnerProductSpace RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false

/-- The existing interval trace pairing is the endpoint product for an
absolutely continuous representative and an absolutely continuous test. -/
theorem n06_interval_ac_trace_pairing {l r : ℝ} (hlr : l < r)
    {v p : ℝ → ℝ}
    (hv : AbsolutelyContinuousOnInterval v l r)
    (hp : AbsolutelyContinuousOnInterval p l r)
    {U D P Pd : RadialL2}
    (hU : (U : ℝ → ℝ) =ᵐ[volume] (Ioo l r).indicator v)
    (hD : (D : ℝ → ℝ) =ᵐ[volume] (Ioo l r).indicator (deriv v))
    (hP : (P : ℝ → ℝ) =ᵐ[volume] (Ioo l r).indicator p)
    (hPd : (Pd : ℝ → ℝ) =ᵐ[volume] (Ioo l r).indicator (deriv p)) :
    ⟪D, P⟫_ℝ + ⟪U, Pd⟫_ℝ = p r * v r - p l * v l := by
  have hI₁ : IntervalIntegrable (fun x => deriv v x * p x) volume l r :=
    hv.intervalIntegrable_deriv.mul_continuousOn hp.continuousOn
  have hI₂ : IntervalIntegrable (fun x => v x * deriv p x) volume l r :=
    hp.intervalIntegrable_deriv.continuousOn_mul hv.continuousOn
  rw [innerWeakGreen_pairing_indicators hlr.le hD hP,
    innerWeakGreen_pairing_indicators hlr.le hU hPd,
    ← intervalIntegral.integral_add hI₁ hI₂]
  exact (hv.integral_deriv_mul_eq_sub hp).trans (by ring)

/-- The continuous L2 trace map already used by the finite-piece graph
returns the true two endpoint values of an AC representative. -/
theorem n06_innerIntervalTrace_of_ac {l r : ℝ} (hlr : l < r)
    {v : ℝ → ℝ} (hv : AbsolutelyContinuousOnInterval v l r)
    {U D : RadialL2}
    (hU : (U : ℝ → ℝ) =ᵐ[volume] (Ioo l r).indicator v)
    (hD : (D : ℝ → ℝ) =ᵐ[volume] (Ioo l r).indicator (deriv v))
    (i : Fin 2) :
    innerIntervalTrace l r U D i = if i = 0 then v l else v r := by
  have hp : AbsolutelyContinuousOnInterval
      (innerIntervalAffineLift l r (innerEndpointValues i)) l r :=
    ((innerIntervalAffineLift_contDiff l r (innerEndpointValues i)).of_le
      (show (1 : ℕ∞ω) ≤ ∞ by simp)).contDiffOn.absolutelyContinuousOnInterval
  have he := n06_interval_ac_trace_pairing hlr hv hp hU hD
    (innerIntervalBoundaryLiftL2_ae l r (innerEndpointValues i))
    (innerIntervalBoundaryDerivL2_ae l r (innerEndpointValues i))
  have hends := innerIntervalAffineLift_endpoints hlr (innerEndpointValues i)
  rw [hends.1, hends.2] at he
  rw [innerIntervalTrace, he]
  fin_cases i <;> norm_num [bufferSign, innerEndpointValues]

/-- Integration by parts for the actual AC flux of a distributional
equation. Its forcing may be merely integrable. -/
theorem n06_ac_conormal_pairing {l r : ℝ} (hlr : l < r)
    {g V v f p : ℝ → ℝ}
    (hg : AbsolutelyContinuousOnInterval g l r)
    (hp : AbsolutelyContinuousOnInterval p l r)
    (hVv : IntervalIntegrable (fun x => V x * v x) volume l r)
    (hf : IntervalIntegrable f volume l r)
    (hode : ∀ᵐ x ∂volume.restrict (Ioo l r),
      -deriv g x + V x * v x = f x) :
    (∫ x in l..r, g x * deriv p x) +
        (∫ x in l..r, V x * v x * p x) - (∫ x in l..r, f x * p x) =
      p r * g r - p l * g l := by
  have hI₁ : IntervalIntegrable (fun x => V x * v x * p x) volume l r :=
    hVv.mul_continuousOn hp.continuousOn
  have hI₂ : IntervalIntegrable (fun x => f x * p x) volume l r :=
    hf.mul_continuousOn hp.continuousOn
  have hd : (∫ x in l..r, deriv g x * p x) =
      (∫ x in l..r, V x * v x * p x) - (∫ x in l..r, f x * p x) := by
    rw [← intervalIntegral.integral_sub hI₁ hI₂]
    simp only [intervalIntegral.integral_of_le hlr.le, integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [hode] with x hx
    have he : deriv g x = V x * v x - f x := by linarith only [hx]
    rw [he]
    ring
  have hibp := hg.integral_mul_deriv_eq_deriv_mul hp
  rw [hd] at hibp
  calc
    _ = g r * p r - g l * p l := by linarith only [hibp]
    _ = _ := by ring

/-- The literal potential integral in the existing weak residual has its
ordinary interval expression for the same L2 representatives. -/
theorem n06_interval_potential_pairing {l r : ℝ} (hlr : l ≤ r)
    (V : ℝ → ℝ) {v p : ℝ → ℝ} {U P : RadialL2}
    (hU : (U : ℝ → ℝ) =ᵐ[volume] (Ioo l r).indicator v)
    (hP : (P : ℝ → ℝ) =ᵐ[volume] (Ioo l r).indicator p) :
    (∫ x : ℝ, V x * U x * P x) = ∫ x in l..r, V x * v x * p x := by
  calc
    _ = ∫ x : ℝ, (Ioo l r).indicator (fun y => V y * v y * p y) x := by
      apply integral_congr_ae
      filter_upwards [hU, hP] with x hux hpx
      rw [hux, hpx]
      by_cases hx : x ∈ Ioo l r
      · simp only [indicator_of_mem hx]
      · simp only [indicator_of_notMem hx, mul_zero]
    _ = ∫ x in Ioo l r, V x * v x * p x := integral_indicator measurableSet_Ioo
    _ = _ := by rw [intervalIntegral.integral_of_le hlr, integral_Ioc_eq_integral_Ioo]

/-- The actual L2 residual on any represented boundary lift is the
classical endpoint conormal pairing. Here `Q` represents the physical
flux `g`; it need not be a smooth function. -/
theorem n06_innerWeakBoundaryPairing_of_ac {l r : ℝ} (hlr : l < r)
    {V v g f p : ℝ → ℝ}
    (hV : ContinuousOn V (Icc l r)) (hv : ContinuousOn v (Icc l r))
    (hg : AbsolutelyContinuousOnInterval g l r)
    (hp : AbsolutelyContinuousOnInterval p l r)
    (hf : MemLp f 2 (volume.restrict (Ioo l r)))
    (hode : ∀ᵐ x ∂volume.restrict (Ioo l r),
      -deriv g x + V x * v x = f x)
    {U Q F P Pd : RadialL2}
    (hU : (U : ℝ → ℝ) =ᵐ[volume] (Ioo l r).indicator v)
    (hQ : (Q : ℝ → ℝ) =ᵐ[volume] (Ioo l r).indicator g)
    (hF : (F : ℝ → ℝ) =ᵐ[volume] (Ioo l r).indicator f)
    (hP : (P : ℝ → ℝ) =ᵐ[volume] (Ioo l r).indicator p)
    (hPd : (Pd : ℝ → ℝ) =ᵐ[volume] (Ioo l r).indicator (deriv p)) :
    innerWeakBoundaryPairing V U Q F P Pd = p r * g r - p l * g l := by
  have hVv : IntervalIntegrable (fun x => V x * v x) volume l r :=
    (hV.mul hv).intervalIntegrable_of_Icc hlr.le
  have hfi : IntervalIntegrable f volume l r :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hlr.le).mpr
      (interval_memLp_integrable hf)
  rw [innerWeakBoundaryPairing,
    innerWeakGreen_pairing_indicators hlr.le hQ hPd,
    n06_interval_potential_pairing hlr.le V hU hP,
    innerWeakGreen_pairing_indicators hlr.le hF hP]
  exact n06_ac_conormal_pairing hlr hg hp hVv hfi hode

/-- Identification of the existing fixed affine-lift weak flux. The two
outgoing signs are encoded by the endpoint difference in this formula. -/
theorem n06_innerIntervalWeakFluxPairing_of_ac {l r : ℝ} (hlr : l < r)
    {V v g f : ℝ → ℝ}
    (hV : ContinuousOn V (Icc l r)) (hv : ContinuousOn v (Icc l r))
    (hg : AbsolutelyContinuousOnInterval g l r)
    (hf : MemLp f 2 (volume.restrict (Ioo l r)))
    (hode : ∀ᵐ x ∂volume.restrict (Ioo l r),
      -deriv g x + V x * v x = f x)
    {U Q F : RadialL2}
    (hU : (U : ℝ → ℝ) =ᵐ[volume] (Ioo l r).indicator v)
    (hQ : (Q : ℝ → ℝ) =ᵐ[volume] (Ioo l r).indicator g)
    (hF : (F : ℝ → ℝ) =ᵐ[volume] (Ioo l r).indicator f)
    (z : Fin 2 → ℝ) :
    innerIntervalWeakFluxPairing V l r U Q F z = z 1 * g r - z 0 * g l := by
  have hp : AbsolutelyContinuousOnInterval (innerIntervalAffineLift l r z) l r :=
    ((innerIntervalAffineLift_contDiff l r z).of_le
      (show (1 : ℕ∞ω) ≤ ∞ by simp)).contDiffOn.absolutelyContinuousOnInterval
  have he := n06_innerWeakBoundaryPairing_of_ac hlr hV hv hg hp hf hode
    hU hQ hF (innerIntervalBoundaryLiftL2_ae l r z)
    (innerIntervalBoundaryDerivL2_ae l r z)
  have hends := innerIntervalAffineLift_endpoints hlr z
  simpa only [innerIntervalWeakFluxPairing, hends.1, hends.2] using he

/-- For a C1 representative with AC first derivative the actual weak
flux is `a v'` at each endpoint. The original L2 source is unchanged. -/
theorem n06_innerIntervalWeakFluxPairing_of_H2 {l r : ℝ} (hlr : l < r)
    {a V v f : ℝ → ℝ} (ha : ContDiff ℝ 1 a) (hV : Continuous V)
    (hv : ContDiff ℝ 1 v)
    (hvd : AbsolutelyContinuousOnInterval (deriv v) l r)
    (hf : MemLp f 2 (volume.restrict (Ioo l r)))
    (hode : ∀ᵐ x ∂volume.restrict (Ioo l r),
      -deriv (fun y => a y * deriv v y) x + V x * v x = f x)
    {U Q F : RadialL2}
    (hU : (U : ℝ → ℝ) =ᵐ[volume] (Ioo l r).indicator v)
    (hQ : (Q : ℝ → ℝ) =ᵐ[volume]
      (Ioo l r).indicator (fun x => a x * deriv v x))
    (hF : (F : ℝ → ℝ) =ᵐ[volume] (Ioo l r).indicator f)
    (z : Fin 2 → ℝ) :
    innerIntervalWeakFluxPairing V l r U Q F z =
      z 1 * (a r * deriv v r) - z 0 * (a l * deriv v l) :=
  n06_innerIntervalWeakFluxPairing_of_ac hlr hV.continuousOn hv.continuous.continuousOn
    (ha.contDiffOn.absolutelyContinuousOnInterval.fun_mul hvd) hf hode hU hQ hF z

/-- The original physical trace, with density `12 w / r²` and normalized
gradient `r v' / sqrt 12`, also returns the true endpoint value of an AC
representative. The density is cancelled explicitly in the same L2
pairings used by the finite physical weak graph. -/
theorem n06_innerRadialH1Trace_of_ac (D : ReferenceData) (hw : Continuous D.w)
    {l r : ℝ} (hlr : l < r) (hl : 0 < l)
    (hcore : Ioo l r ⊆ radialCore D)
    (hpos : ∀ x ∈ Icc l r, 0 < D.w x)
    {v : ℝ → ℝ} (hv : AbsolutelyContinuousOnInterval v l r)
    {Q : InnerRadialH1Pair D}
    (hQv : (Q.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (Ioo l r).indicator v)
    (hQd : (Q.2 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo l r).indicator (innerGapGradientField v))
    (i : Fin 2) :
    innerRadialH1Trace D hw hl hcore hpos Q i = if i = 0 then v l else v r := by
  let p : ℝ → ℝ := innerIntervalAffineLift l r (innerEndpointValues i)
  have hp : ContDiff ℝ ∞ p := innerIntervalAffineLift_contDiff l r (innerEndpointValues i)
  have hpc : ContinuousOn p (Icc l r) := hp.continuous.continuousOn
  have hpdc : ContinuousOn (deriv p) (Icc l r) :=
    (hp.continuous_deriv (by simp)).continuousOn
  have hpAC : AbsolutelyContinuousOnInterval p l r :=
    (hp.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).contDiffOn.absolutelyContinuousOnInterval
  have hpos' : ∀ x ∈ Ioo l r, 0 ≤ D.w x :=
    fun x hx => (hpos x (Ioo_subset_Icc_self hx)).le
  have hG :
      (innerRadialTraceGradientTest D hw hl hcore hpos p hpc : ℝ → ℝ)
        =ᵐ[radialHilbertMeasure D]
          (Ioo l r).indicator (fun x => (Real.sqrt 12 * x / (12 * D.w x)) * p x) := by
    unfold innerRadialTraceGradientTest
    exact innerRadialIntervalToLp_ae D hw hl hcore _ _ _
  have hP :
      (innerRadialTraceValueTest D hw hl hcore hpos p hpdc : ℝ → ℝ)
        =ᵐ[radialHilbertMeasure D]
          (Ioo l r).indicator (fun x => (x ^ 2 / (12 * D.w x)) * deriv p x) := by
    unfold innerRadialTraceValueTest
    exact innerRadialIntervalToLp_ae D hw hl hcore _ _ _
  have hsqrt : Real.sqrt (12 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hg : ⟪Q.2, innerRadialTraceGradientTest D hw hl hcore hpos p hpc⟫_ℝ =
      ∫ x in l..r, deriv v x * p x := by
    rw [innerRadial_pairing_of_indicator D hw hlr.le hcore hpos' hQd hG]
    apply intervalIntegral.integral_congr
    intro x hx
    have hxcc : x ∈ Icc l r := by simpa only [uIcc_of_le hlr.le] using hx
    have hx0 : x ≠ 0 := (hl.trans_le hxcc.1).ne'
    have hw0 : D.w x ≠ 0 := (hpos x hxcc).ne'
    dsimp only [innerGapGradientField]
    field_simp [hx0, hw0, hsqrt] <;> ring
  have hpv : ⟪Q.1, innerRadialTraceValueTest D hw hl hcore hpos p hpdc⟫_ℝ =
      ∫ x in l..r, v x * deriv p x := by
    rw [innerRadial_pairing_of_indicator D hw hlr.le hcore hpos' hQv hP]
    apply intervalIntegral.integral_congr
    intro x hx
    have hxcc : x ∈ Icc l r := by simpa only [uIcc_of_le hlr.le] using hx
    field_simp [(hl.trans_le hxcc.1).ne', (hpos x hxcc).ne'] <;> ring
  have hI₁ : IntervalIntegrable (fun x => deriv v x * p x) volume l r :=
    hv.intervalIntegrable_deriv.mul_continuousOn hpAC.continuousOn
  have hI₂ : IntervalIntegrable (fun x => v x * deriv p x) volume l r :=
    hpAC.intervalIntegrable_deriv.continuousOn_mul hv.continuousOn
  have hpair :
      ⟪Q.2, innerRadialTraceGradientTest D hw hl hcore hpos p hpc⟫_ℝ +
        ⟪Q.1, innerRadialTraceValueTest D hw hl hcore hpos p hpdc⟫_ℝ =
      p r * v r - p l * v l := by
    rw [hg, hpv, ← intervalIntegral.integral_add hI₁ hI₂]
    exact (hv.integral_deriv_mul_eq_sub hpAC).trans (by ring)
  have hends := innerIntervalAffineLift_endpoints hlr (innerEndpointValues i)
  change p l = (innerEndpointValues i) 0 ∧ p r = (innerEndpointValues i) 1 at hends
  rw [hends.1, hends.2] at hpair
  change bufferSign i * _ = _
  rw [hpair]
  fin_cases i <;> norm_num [bufferSign, innerEndpointValues]

/-- The actual L2 weak modal equation produces one C1/H2 representative
whose unrestricted boundary-test residual has its genuine endpoint flux.
This is the same representative supplied by weak modal regularity. -/
theorem n06_weak_mode_L2_regular_boundary_pairing {l r : ℝ} (hlr : l < r)
    {a c V u F : ℝ → ℝ} (j : ℝ)
    (ha : ContDiff ℝ ∞ a) (han : ∀ x ∈ Icc l r, a x ≠ 0)
    (hc : Continuous c) (hV : Continuous V)
    (hu : MemLp u 2 (volume.restrict (Ioo l r)))
    (hF : MemLp F 2 (volume.restrict (Ioo l r)))
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo l r →
        (∫ x in l..r, u x * (-deriv (fun y => a y * deriv φ y) x +
          (j ^ 2 * c x + V x) * φ x)) = ∫ x in l..r, F x * φ x) :
    ∃ v : ℝ → ℝ,
      u =ᵐ[volume.restrict (Ioo l r)] v ∧ ContDiff ℝ 1 v ∧
      AbsolutelyContinuousOnInterval (deriv v) l r ∧
      MemLp v 2 (volume.restrict (Ioo l r)) ∧
      MemLp (deriv v) 2 (volume.restrict (Ioo l r)) ∧
      MemLp (deriv (deriv v)) 2 (volume.restrict (Ioo l r)) ∧
      (∀ᵐ x ∂volume.restrict (Ioo l r),
        -deriv (fun y => a y * deriv v y) x +
          (j ^ 2 * c x + V x) * v x = F x) ∧
      ∀ p : ℝ → ℝ, ContDiff ℝ 1 p →
        (∫ x in l..r, a x * deriv v x * deriv p x) +
            (∫ x in l..r, (j ^ 2 * c x + V x) * v x * p x) -
            (∫ x in l..r, F x * p x) =
          p r * (a r * deriv v r) - p l * (a l * deriv v l) := by
  obtain ⟨v, huv, hv, hvd, hv₀, hv₁, hv₂, hode, _⟩ :=
    n06_weak_mode_L2_regular hlr j ha han hc hV hu hF hweak
  have hode' : ∀ᵐ x ∂volume.restrict (Ioo l r),
      -deriv (fun y => a y * deriv v y) x +
        (j ^ 2 * c x + V x) * v x = F x := by
    filter_upwards [hode] with x hx
    nlinarith only [hx]
  refine ⟨v, huv, hv, hvd, hv₀, hv₁, hv₂, hode', ?_⟩
  intro p hp
  have ha₁ : ContDiff ℝ 1 a := ha.of_le (by simp)
  have hg : AbsolutelyContinuousOnInterval (fun x => a x * deriv v x) l r :=
    ha₁.contDiffOn.absolutelyContinuousOnInterval.fun_mul hvd
  have hPc : Continuous (fun x => (j ^ 2 * c x + V x) * v x) :=
    ((continuous_const.mul hc).add hV).mul hv.continuous
  have hfi : IntervalIntegrable F volume l r :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hlr.le).mpr
      (interval_memLp_integrable hF)
  exact n06_ac_conormal_pairing hlr hg hp.contDiffOn.absolutelyContinuousOnInterval
    (hPc.intervalIntegrable l r) hfi hode'

end ContinuousFlexibility.Analysis
