import ContinuousFlexibility.Analysis.OneHighCircleFlowConstantJets

/-!
# Integrability after subtracting an arbitrary reference speed

The reference is merely time integrable. Continuity of the actual
Sobolev norm in the time and constant parameters proves measurability;
the endpoint-jet bound supplies an integrable majorant. No regularity
of the reference beyond its stated integrability is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ENNReal

variable {P : ℝ} [Fact (0 < P)]

theorem intervalIntegrable_circleSubtractConstantJet
    (f : ℝ → ℕ → C(AddCircle P, ℝ)) {c : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ∀ n, ContinuousOn (fun t => f t n) (Icc a b))
    (hc : IntervalIntegrable c volume a b) (n : ℕ) :
    IntervalIntegrable (fun t => circleSubtractConstantJet (f t) (c t) n) volume a b := by
  let L : ℝ →L[ℝ] C(AddCircle P, ℝ) := ContinuousLinearMap.const ℝ (AddCircle P)
  have hconst : IntervalIntegrable
      (fun t => ContinuousMap.const (AddCircle P) (c t)) volume a b :=
    ⟨L.integrable_comp hc.1, L.integrable_comp hc.2⟩
  have hfn : IntervalIntegrable (fun t => f t n) volume a b :=
    (hf n).intervalIntegrable_of_Icc hab
  by_cases hn : n = 0
  · simpa only [circleSubtractConstantJet, if_pos hn] using hfn.sub hconst
  · simpa only [circleSubtractConstantJet, if_neg hn, sub_zero] using hfn

private theorem continuous_circleSubtractConstantSobolevNorm_clamped
    (f : ℝ → ℕ → C(AddCircle P, ℝ)) {a b : ℝ}
    (hab : a ≤ b) (hf : ∀ n, ContinuousOn (fun t => f t n) (Icc a b))
    (hderiv : ∀ t ∈ Icc a b, ∀ n : ℕ, ∀ θ : ℝ,
      HasDerivAt (fun η : ℝ => f t n (η : AddCircle P))
        (f t (n + 1) (θ : AddCircle P)) θ) (s : ℕ) :
    Continuous (fun p : ℝ × ℝ => circleRealSobolevNorm (s : ℝ)
      (circleSubtractConstantJet (f (max a (min p.1 b))) p.2 0)) := by
  have hclamp : Continuous (fun t : ℝ => max a (min t b)) :=
    continuous_const.max (continuous_id.min continuous_const)
  have hmem (t : ℝ) : max a (min t b) ∈ Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  exact continuous_circleSubtractConstantSobolevNorm
    (fun p : ℝ × ℝ => f (max a (min p.1 b))) (fun p : ℝ × ℝ => p.2)
    (fun n => (hf n).comp_continuous (hclamp.comp continuous_fst) (fun p => hmem p.1))
    (fun p => hderiv (max a (min p.1 b)) (hmem p.1)) continuous_snd s

/-- Measurability follows from joint continuity in the time and constant
parameters, without requiring a continuous reference speed. -/
theorem aestronglyMeasurable_circleSubtractConstantSobolevNorm
    (f : ℝ → ℕ → C(AddCircle P, ℝ)) {c : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ∀ n, ContinuousOn (fun t => f t n) (Icc a b))
    (hderiv : ∀ t ∈ Icc a b, ∀ n : ℕ, ∀ θ : ℝ,
      HasDerivAt (fun η : ℝ => f t n (η : AddCircle P))
        (f t (n + 1) (θ : AddCircle P)) θ)
    (hc : AEStronglyMeasurable c (volume.restrict (uIoc a b))) (s : ℕ) :
    AEStronglyMeasurable (fun t => circleRealSobolevNorm (s : ℝ)
      (circleSubtractConstantJet (f t) (c t) 0)) (volume.restrict (uIoc a b)) := by
  have hparam := continuous_circleSubtractConstantSobolevNorm_clamped f hab hf hderiv s
  have hid : AEStronglyMeasurable (fun t : ℝ => t) (volume.restrict (uIoc a b)) :=
    continuous_id.aestronglyMeasurable
  have hm : AEStronglyMeasurable (fun t => circleRealSobolevNorm (s : ℝ)
      (circleSubtractConstantJet (f (max a (min t b))) (c t) 0))
      (volume.restrict (uIoc a b)) :=
    hparam.comp_aestronglyMeasurable (hid.prodMk hc)
  apply hm.congr
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  have ht' : t ∈ Ioc a b := by simpa only [uIoc_of_le hab] using ht
  rw [min_eq_left ht'.2, max_eq_right ht'.1.le]

/-- Every actual finite-order Sobolev norm is time integrable for the
difference between a continuous smooth circle family and an integrable
angle-independent reference. -/
theorem intervalIntegrable_circleSubtractConstantSobolevNorm
    (f : ℝ → ℕ → C(AddCircle P, ℝ)) {c : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ∀ n, ContinuousOn (fun t => f t n) (Icc a b))
    (hderiv : ∀ t ∈ Icc a b, ∀ n : ℕ, ∀ θ : ℝ,
      HasDerivAt (fun η : ℝ => f t n (η : AddCircle P))
        (f t (n + 1) (θ : AddCircle P)) θ)
    (hc : IntervalIntegrable c volume a b) (s : ℕ) :
    IntervalIntegrable (fun t => circleRealSobolevNorm (s : ℝ)
      (circleSubtractConstantJet (f t) (c t) 0)) volume a b := by
  have hm := aestronglyMeasurable_circleSubtractConstantSobolevNorm f hab hf hderiv
    hc.aestronglyMeasurable_restrict_uIoc s
  have hIzero : IntervalIntegrable (fun t => f t 0) volume a b :=
    (hf 0).intervalIntegrable_of_Icc hab
  have hIs : IntervalIntegrable (fun t => f t s) volume a b :=
    (hf s).intervalIntegrable_of_Icc hab
  have hdom : IntervalIntegrable
      (fun t => (2 : ℝ) ^ s * (‖f t 0‖ + ‖f t s‖ + 2 * |c t|)) volume a b :=
    ((hIzero.norm.add hIs.norm).add (hc.abs.const_mul 2)).const_mul ((2 : ℝ) ^ s)
  apply hdom.mono_fun' hm
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  have ht' : t ∈ Ioc a b := by simpa only [uIoc_of_le hab] using ht
  rw [Real.norm_eq_abs, abs_of_nonneg
    (circle_real_sobolevNorm_nonneg (s : ℝ) (circleSubtractConstantJet (f t) (c t) 0))]
  exact circleSubtractConstantJet_sobolev_le
    (f t) (hderiv t ⟨ht'.1.le, ht'.2⟩) (c t) s

end ContinuousFlexibility.Analysis
