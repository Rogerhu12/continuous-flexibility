import ContinuousFlexibility.Radial.ModeLocalMeasure
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Natural kernels of the fixed radial operator

The modal inverse identifies the higher even kernels with zero. At the
second mode, its injectivity and the actual normalized border identify the
kernel with the span of the given homogeneous profile. Almost-everywhere
representatives are transported through the actual Hilbert density.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

private theorem referenceKernel_smooth_deriv {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (deriv f) :=
  (contDiff_infty_iff_deriv.mp hf).2

private theorem referenceKernel_continuousOn_jacobi (s : ℝ) {w u : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (radialJacobi s w u) (Icc a b) := by
  have hflux := referenceKernel_smooth_deriv (hw.mul (referenceKernel_smooth_deriv hu))
  have hdw := (referenceKernel_smooth_deriv hw).continuous
  have hpotential : ContinuousOn (fun r => s * deriv w r / r * u r) (Icc a b) :=
    ((continuousOn_const.mul hdw.continuousOn).div continuousOn_id
      (fun r hr => (ha.trans_le hr.1).ne')).mul hu.continuous.continuousOn
  exact hflux.continuous.continuousOn.sub hpotential

/-- The ordinary radial Green identity when the smooth leading coefficient
vanishes at the two finite endpoints. -/
theorem radialJacobi_green_integral (s : ℝ) {w u v : ℝ → ℝ} {a b : ℝ}
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (ha : 0 < a) (hab : a ≤ b) (hwa : w a = 0) (hwb : w b = 0) :
    (∫ r in a..b, u r * radialJacobi s w v r) =
      ∫ r in a..b, v r * radialJacobi s w u r := by
  have hfluxu : ContDiff ℝ ∞ (fun r => w r * deriv u r) :=
    hw.mul (referenceKernel_smooth_deriv hu)
  have hfluxv : ContDiff ℝ ∞ (fun r => w r * deriv v r) :=
    hw.mul (referenceKernel_smooth_deriv hv)
  have hAi : IntervalIntegrable (fun r => u r * radialJacobi s w v r) volume a b :=
    (hu.continuous.continuousOn.mul
      (referenceKernel_continuousOn_jacobi s hw hv ha)).intervalIntegrable_of_Icc hab
  have hBi : IntervalIntegrable (fun r => v r * radialJacobi s w u r) volume a b :=
    (hv.continuous.continuousOn.mul
      (referenceKernel_continuousOn_jacobi s hw hu ha)).intervalIntegrable_of_Icc hab
  have hderiv : ∀ r ∈ uIcc a b,
      HasDerivAt (fun t => u t * (w t * deriv v t) - v t * (w t * deriv u t))
        (u r * radialJacobi s w v r - v r * radialJacobi s w u r) r := by
    intro r _
    have h := ((hu.differentiable (by simp) r).hasDerivAt.mul
      (hfluxv.differentiable (by simp) r).hasDerivAt).sub
      ((hv.differentiable (by simp) r).hasDerivAt.mul
        (hfluxu.differentiable (by simp) r).hasDerivAt)
    refine h.congr_deriv ?_
    simp only [radialJacobi]
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hAi.sub hBi)
  rw [intervalIntegral.integral_sub hAi hBi] at hint
  have hzero :
      (∫ r in a..b, u r * radialJacobi s w v r) -
        (∫ r in a..b, v r * radialJacobi s w u r) = 0 := by
    simpa only [hwa, hwb, zero_mul, mul_zero, sub_self] using hint
  exact sub_eq_zero.mp hzero

/-- Endpoint-flat smooth functions are actual members of the radial Hilbert
space, whose measure is finite. -/
theorem endpointFlat_memLp_radialHilbert {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {u : ℝ → ℝ} (hu : EndpointFlat D u) :
    MemLp u 2 (radialHilbertMeasure D) := by
  letI : IsFiniteMeasure (radialHilbertMeasure D) := radialHilbertMeasure_isFinite hD
  have hc : HasCompactSupport u := by
    apply HasCompactSupport.of_support_subset_isCompact (K := Icc D.a D.b) isCompact_Icc
    intro r hr
    constructor
    · by_contra h
      exact (Function.mem_support.mp hr) (hu.2 r (Or.inl (lt_of_not_ge h).le))
    · by_contra h
      exact (Function.mem_support.mp hr) (hu.2 r (Or.inr (lt_of_not_ge h).le))
  exact hu.1.continuous.memLp_of_hasCompactSupport hc

/-- A smooth actual homogeneous solution belongs to the distributional
natural kernel. The only Hilbert membership hypothesis is the one in that
kernel's definition. -/
theorem naturalRadialNull_of_smooth {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (j : ℕ) {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (hLp : MemLp u 2 (radialHilbertMeasure D))
    (heq : ∀ r ∈ radialCore D, radialJacobi ((j : ℝ) ^ 2) D.w u r = 0) :
    NaturalRadialNull D j u := by
  refine ⟨hLp, ?_⟩
  intro ψ hψ _ _
  have hg := matchingProfileGeometry hD
  have hwa : D.w D.a = 0 := hg.2.2.1.2 D.a (Or.inl le_rfl)
  have hwb : D.w D.b = 0 := hg.2.2.1.2 D.b (Or.inr le_rfl)
  rw [radialJacobi_green_integral ((j : ℝ) ^ 2) hg.2.2.1.1 hu hψ
    hg.1 hg.2.1.le hwa hwb]
  rw [intervalIntegral.integral_of_le hg.2.1.le, integral_Ioc_eq_integral_Ioo]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem (show MeasurableSet (Ioo D.a D.b) from measurableSet_Ioo)]
    with r hr
  rw [heq r hr, mul_zero]

theorem naturalRadialNull_congr {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {j : ℕ} {u v : ℝ → ℝ} (hu : NaturalRadialNull D j u)
    (huv : u =ᵐ[radialHilbertMeasure D] v) : NaturalRadialNull D j v := by
  refine ⟨(memLp_congr_ae huv).mp hu.1, ?_⟩
  intro ψ hψ hc hs
  calc
    (∫ r in D.a..D.b, v r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) =
        ∫ r in D.a..D.b, u r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r := by
      apply matchingInterval_congr_ae hD
      filter_upwards [huv] with r hr
      rw [hr]
    _ = 0 := hu.2 ψ hψ hc hs

theorem naturalRadialNull_const_mul {D : ReferenceData} {j : ℕ}
    {u : ℝ → ℝ} (hu : NaturalRadialNull D j u) (c : ℝ) :
    NaturalRadialNull D j (fun r => c * u r) := by
  refine ⟨hu.1.const_mul c, ?_⟩
  intro ψ hψ hc hs
  calc
    (∫ r in D.a..D.b, (c * u r) * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) =
        c * ∫ r in D.a..D.b, u r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r := by
      simp only [mul_assoc, intervalIntegral.integral_const_mul]
    _ = 0 := by rw [hu.2 ψ hψ hc hs, mul_zero]

private theorem referenceKernel_zero_source_integral {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (ψ : ℝ → ℝ) :
    (∫ r in D.a..D.b, matchingDensity D r * (0 : RadialModeL2 D) r * ψ r) = 0 := by
  calc
    _ = ∫ _r in D.a..D.b, (0 : ℝ) := by
      apply matchingInterval_congr_ae hD
      filter_upwards [Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D)] with r hr
      simp only [hr, Pi.zero_apply, mul_zero, zero_mul]
    _ = 0 := by simp

/-- A Hilbert representative of a natural null vector satisfies the same
modal weak equation, with arbitrary row datum and zero ordinary source. -/
theorem modeLocalEquation_of_naturalRadialNull {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {j : ℕ} {u : ℝ → ℝ}
    (hu : NaturalRadialNull D j u) (U : RadialModeL2 D)
    (hU : (U : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u) (c : ℝ) :
    ModeLocalEquation D j (radialCore D) (U, 0) (0, c) := by
  intro ψ hψ hc hs
  change (∫ r in D.a..D.b, U r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) -
      0 * (∫ r in D.a..D.b, referenceColumn D r * ψ r) =
    -(∫ r in D.a..D.b, matchingDensity D r * (0 : RadialModeL2 D) r * ψ r)
  rw [zero_mul, sub_zero, referenceKernel_zero_source_integral hD, neg_zero]
  calc
    _ = ∫ r in D.a..D.b, u r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r := by
      apply matchingInterval_congr_ae hD
      filter_upwards [hU] with r hr
      rw [hr]
    _ = 0 := hu.2 ψ hψ hc hs

/-- Injectivity of any non-second modal inverse eliminates its natural
unbordered kernel. -/
theorem naturalRadialNull_eq_zero_of_modeInverse {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {j : ℕ} (hj : j ≠ 2)
    {G : RadialModePair D →L[ℝ] RadialModePair D}
    (hG : ModeInverseProperties D j G) {u : ℝ → ℝ}
    (hu : NaturalRadialNull D j u) :
    u =ᵐ[radialHilbertMeasure D] (fun _ => 0) := by
  let U : RadialModeL2 D := hu.1.toLp u
  have hU : (U : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u := hu.1.coeFn_toLp
  have hgraph : ModeFullGraph D j (U, 0) (0, 0) := by
    refine ⟨modeLocalEquation_of_naturalRadialNull hD hu U hU 0, ?_⟩
    simpa only [hj, ite_false] using
      (And.intro rfl rfl : (0 : ℝ) = 0 ∧ (0 : ℝ) = 0)
  have hpair : (U, (0 : ℝ)) = (0 : RadialModePair D) :=
    (hG.2 (U, 0) (0, 0) hgraph).symm.trans (G.map_zero)
  have hzero : U = 0 := congrArg Prod.fst hpair
  rw [hzero] at hU
  exact hU.symm.trans (Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D))

/-- A normalized natural null vector spans the second-mode kernel once the
bordered modal graph has an inverse. -/
theorem naturalRadialNull_two_iff_of_modeInverse {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {φ : ℝ → ℝ}
    (hφ : NaturalRadialNull D 2 φ)
    (hrow : (∫ r in D.a..D.b, referenceColumn D r * φ r) = 1)
    {G : RadialModePair D →L[ℝ] RadialModePair D}
    (hG : ModeInverseProperties D 2 G) (u : ℝ → ℝ) :
    NaturalRadialNull D 2 u ↔
      ∃ c : ℝ, u =ᵐ[radialHilbertMeasure D] (fun r => c * φ r) := by
  constructor
  · intro hu
    let c : ℝ := ∫ r in D.a..D.b, referenceColumn D r * u r
    let U : RadialModeL2 D := hu.1.toLp u
    have hU : (U : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u := hu.1.coeFn_toLp
    have hmul := naturalRadialNull_const_mul hφ c
    let V : RadialModeL2 D := hmul.1.toLp (fun r => c * φ r)
    have hV : (V : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (fun r => c * φ r) :=
      hmul.1.coeFn_toLp
    have hgraphU : ModeFullGraph D 2 (U, 0) (0, c) := by
      refine ⟨modeLocalEquation_of_naturalRadialNull hD hu U hU c, ?_⟩
      change (∫ r in D.a..D.b, referenceColumn D r * U r) = c
      apply matchingInterval_congr_ae hD
      filter_upwards [hU] with r hr
      rw [hr]
    have hgraphV : ModeFullGraph D 2 (V, 0) (0, c) := by
      refine ⟨modeLocalEquation_of_naturalRadialNull hD hmul V hV c, ?_⟩
      change (∫ r in D.a..D.b, referenceColumn D r * V r) = c
      calc
        _ = ∫ r in D.a..D.b, referenceColumn D r * (c * φ r) := by
          apply matchingInterval_congr_ae hD
          filter_upwards [hV] with r hr
          rw [hr]
        _ = ∫ r in D.a..D.b, c * (referenceColumn D r * φ r) := by
          apply intervalIntegral.integral_congr
          intro r _
          ring
        _ = c * ∫ r in D.a..D.b, referenceColumn D r * φ r :=
          intervalIntegral.integral_const_mul _ _
        _ = c := by rw [hrow, mul_one]
    have hpair : (U, (0 : ℝ)) = (V, 0) :=
      (hG.2 (U, 0) (0, c) hgraphU).symm.trans (hG.2 (V, 0) (0, c) hgraphV)
    have hUV : U = V := congrArg Prod.fst hpair
    refine ⟨c, ?_⟩
    rw [hUV] at hU
    exact hU.symm.trans hV
  · rintro ⟨c, hc⟩
    exact naturalRadialNull_congr hD (naturalRadialNull_const_mul hφ c) hc.symm

/-- The actual homogeneous profile and the normalized true border identify
all natural even kernels using the already constructed modal inverses. -/
theorem radialNaturalKernels_of_modeInverses {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (hφ : ∀ r ∈ radialCore D, radialJacobi 4 D.w D.phi r = 0)
    (hmodes : ∀ j : ℕ, 2 ≤ j → Even j →
      ∃ G : RadialModePair D →L[ℝ] RadialModePair D, ModeInverseProperties D j G) :
    RadialNaturalKernels D := by
  have hflat : EndpointFlat D D.phi := (matchingProfileGeometry hD).2.2.2.1
  have hnull : NaturalRadialNull D 2 D.phi := by
    apply naturalRadialNull_of_smooth hD 2 hflat.1 (endpointFlat_memLp_radialHilbert hD hflat)
    intro r hr
    simpa only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] using hφ r hr
  refine ⟨hφ, ?_, ?_⟩
  · obtain ⟨G, hG⟩ := hmodes 2 le_rfl (by decide)
    exact naturalRadialNull_two_iff_of_modeInverse hD hnull hborder.2.2.2.1 hG
  · intro n hn u hu
    obtain ⟨G, hG⟩ := hmodes (2 * n) (by omega) ⟨n, by omega⟩
    exact naturalRadialNull_eq_zero_of_modeInverse hD (by omega) hG hu

end ContinuousFlexibility.Radial
