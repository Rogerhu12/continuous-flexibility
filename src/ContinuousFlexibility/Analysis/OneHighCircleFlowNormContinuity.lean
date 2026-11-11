import ContinuousFlexibility.Analysis.OneHighCircleRealSobolev
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Continuity of the actual circle Sobolev norms in a parameter

The physical Bessel norm is controlled by the supremum norms of the
zeroth and highest actual derivatives. The reverse triangle inequality
therefore proves its continuity for a continuous family of derivative
towers. Periodic smooth real lifts provide these towers canonically.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory Topology
open scoped ContDiff Topology ENNReal

variable {P : ℝ} [Fact (0 < P)]

theorem circle_l2_le_supNorm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : C(AddCircle P, E)) :
    (eLpNorm f 2 AddCircle.haarAddCircle).toReal ≤ ‖f‖ := by
  have he := eLpNorm_le_of_ae_bound (p := (2 : ℝ≥0∞))
    (μ := AddCircle.haarAddCircle)
    f.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun x => f.norm_coe_le_norm x))
  simp only [measure_univ, ENNReal.one_rpow, one_mul] at he
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  simpa only [ENNReal.toReal_ofReal (norm_nonneg f)] using hr

private theorem circle_frequencyWeighted_sub (s : ℝ)
    (f g : C(AddCircle P, ℂ)) :
    frequencyWeighted (circleFrequencyWeight P) s (fourierCoeff (f - g)) =
      frequencyWeighted (circleFrequencyWeight P) s (fourierCoeff f) -
        frequencyWeighted (circleFrequencyWeight P) s (fourierCoeff g) := by
  funext n
  simp only [frequencyWeighted_apply, Pi.sub_apply]
  rw [← circleFourierCoeffCLM_apply, map_sub,
    circleFourierCoeffCLM_apply, circleFourierCoeffCLM_apply, smul_sub]

private theorem circle_sobolevNorm_abs_sub_le {s : ℝ}
    (f g : C(AddCircle P, ℂ))
    (hf : MemLp (frequencyWeighted (circleFrequencyWeight P) s (fourierCoeff f))
      2 Measure.count)
    (hg : MemLp (frequencyWeighted (circleFrequencyWeight P) s (fourierCoeff g))
      2 Measure.count) :
    |circleSobolevNorm s f - circleSobolevNorm s g| ≤ circleSobolevNorm s (f - g) := by
  have hfg := lpNorm_le_lpNorm_add_lpNorm_sub' hg
    (f := frequencyWeighted (circleFrequencyWeight P) s (fourierCoeff f))
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hgf := lpNorm_le_lpNorm_add_lpNorm_sub hf
    (f := frequencyWeighted (circleFrequencyWeight P) s (fourierCoeff g))
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  simp only [circleSobolevNorm, frequencySobolevNorm, circle_frequencyWeighted_sub,
    toReal_eLpNorm]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem circleComplexify_sub (f g : C(AddCircle P, ℝ)) :
    circleComplexify (f - g) = circleComplexify f - circleComplexify g := by
  ext x
  simp only [circleComplexify_apply, ContinuousMap.sub_apply, Complex.ofReal_sub]

/-- Difference of two genuine derivative towers controls the difference
of their actual physical Sobolev norms. -/
theorem circle_real_sobolevNorm_dist_le_derivative_supNorms
    (f g : ℕ → C(AddCircle P, ℝ))
    (hf : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x)
    (hg : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => g k (y : AddCircle P))
        (g (k + 1) (x : AddCircle P)) x)
    (s : ℕ) :
    |circleRealSobolevNorm (s : ℝ) (f 0) - circleRealSobolevNorm (s : ℝ) (g 0)| ≤
      (2 : ℝ) ^ s * (‖f 0 - g 0‖ + ‖f s - g s‖) := by
  have hdiff (k : ℕ) (x : ℝ) :
      HasDerivAt (fun y : ℝ => (f k - g k) (y : AddCircle P))
        ((f (k + 1) - g (k + 1)) (x : AddCircle P)) x :=
    (hf k x).sub (hg k x)
  have hfLp := circle_frequencyWeighted_memLp_of_derivatives
    (fun k => circleComplexify (f k)) (circleComplexify_hasDerivAt f hf) s
  have hgLp := circle_frequencyWeighted_memLp_of_derivatives
    (fun k => circleComplexify (g k)) (circleComplexify_hasDerivAt g hg) s
  have hreverse := circle_sobolevNorm_abs_sub_le
    (circleComplexify (f 0)) (circleComplexify (g 0)) hfLp hgLp
  rw [← circleComplexify_sub] at hreverse
  exact hreverse.trans ((circle_real_sobolevNorm_le_derivative_endpoints
    (fun k => f k - g k) hdiff s).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add (circle_l2_le_supNorm _) (circle_l2_le_supNorm _)) (by positivity)))

/-- Continuous zeroth and highest jets suffice for continuity of each
finite-order Bessel norm. All finiteness comes from the actual tower. -/
theorem continuous_circleRealSobolevNorm_of_derivatives
    {X : Type*} [TopologicalSpace X] (f : X → ℕ → C(AddCircle P, ℝ))
    (hderiv : ∀ t : X, ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f t k (y : AddCircle P))
        (f t (k + 1) (x : AddCircle P)) x)
    (s : ℕ) (hzero : Continuous (fun t => f t 0))
    (hs : Continuous (fun t => f t s)) :
    Continuous (fun t => circleRealSobolevNorm (s : ℝ) (f t 0)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hc : Continuous (fun u => (2 : ℝ) ^ s *
      (‖f u 0 - f t 0‖ + ‖f u s - f t s‖)) :=
    continuous_const.mul
      ((hzero.sub continuous_const).norm.add (hs.sub continuous_const).norm)
  have hlimit : Tendsto (fun u => (2 : ℝ) ^ s *
      (‖f u 0 - f t 0‖ + ‖f u s - f t s‖)) (𝓝 t) (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_add, mul_zero] using
      (hc.continuousAt (x := t)).tendsto
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) ?_ hlimit
  intro u
  rw [Real.dist_eq]
  exact circle_real_sobolevNorm_dist_le_derivative_supNorms
    (f u) (f t) (hderiv u) (hderiv t) s

/-- Joint continuity of actual periodic lift derivatives gives continuity
of the canonical continuous-circle derivative family in supremum norm. -/
theorem continuous_periodicCircleJet_family
    {X : Type*} [TopologicalSpace X] (v : X → ℝ → ℝ)
    (hp : ∀ t, Function.Periodic (v t) P) (hv : ∀ t, ContDiff ℝ ∞ (v t))
    (n : ℕ) (hj : Continuous (fun p : X × ℝ => iteratedDeriv n (v p.1) p.2)) :
    Continuous (fun t => periodicCircleJet (v t) (hp t) (hv t) n) := by
  have hmk : IsOpenQuotientMap (fun x : ℝ => (x : AddCircle P)) :=
    QuotientAddGroup.isOpenQuotientMap_mk
  have hquot := (IsOpenQuotientMap.id (X := X)).prodMap hmk
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply hquot.isQuotientMap.continuous_iff.mpr
  have he :
      (Function.uncurry (fun t x => periodicCircleJet (v t) (hp t) (hv t) n x) ∘
        Prod.map (id : X → X) (fun x : ℝ => (x : AddCircle P))) =
      fun p : X × ℝ => iteratedDeriv n (v p.1) p.2 := by
    funext p
    exact periodicCircleJet_coe_apply (v p.1) (hp p.1) (hv p.1) n p.2
  rw [he]
  exact hj

end ContinuousFlexibility.Analysis
