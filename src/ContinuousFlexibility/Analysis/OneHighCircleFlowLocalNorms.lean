module

public import ContinuousFlexibility.Analysis.OneHighCircleFlowLocalization
public import ContinuousFlexibility.Analysis.OneHighCircleFlowReferenceNorms

/-!
# Actual speed norms for a local time neighborhood

The speed jets below come directly from the given speed on the original
closed interval. Their totalization outside that interval is used only to
write ordinary time integrals. The derived global localization has exactly
the same jets and integrated norms on the interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff ENNReal

variable {a b ε : ℝ}

theorem circleFlowLocal_time_mem (hε : 0 < ε) {t : ℝ} (ht : t ∈ Icc a b) :
    t ∈ Ioo (a - ε) (b + ε) :=
  ⟨by linarith [ht.1], by linarith [ht.2]⟩

variable {P : ℝ} [Fact (0 < P)] {G : PolarPoint → ℝ}
  (hε : 0 < ε)
  (hG : ContDiffOn ℝ ∞ G (Ioo (a - ε) (b + ε) ×ˢ (univ : Set ℝ)))
  (hperiod : ∀ t ∈ Ioo (a - ε) (b + ε),
    Function.Periodic (fun θ => G (t, θ)) P)

/-- Canonical angular jets of the original, locally smooth speed. -/
def circleFlowLocalSpeedJet (t : ℝ) (n : ℕ) : C(AddCircle P, ℝ) :=
  if ht : t ∈ Icc a b then
    periodicCircleJet (fun θ => G (t, θ))
      (hperiod t (circleFlowLocal_time_mem hε ht))
      (contDiff_circleFlowLocal_slice isOpen_Ioo hG (circleFlowLocal_time_mem hε ht)) n
  else 0

theorem circleFlowLocalSpeedJet_coe_apply {t : ℝ} (ht : t ∈ Icc a b)
    (n : ℕ) (θ : ℝ) :
    circleFlowLocalSpeedJet hε hG hperiod t n (θ : AddCircle P) =
      iteratedDeriv n (fun η => G (t, η)) θ := by
  simp only [circleFlowLocalSpeedJet, dif_pos ht, periodicCircleJet_coe_apply]

/-- The integrated derivative norm uses the original speed only. -/
def circleFlowLocalLambda (s : ℕ) : ℝ :=
  ∫ t in a..b, circleRealSobolevNorm (s : ℝ) (circleFlowLocalSpeedJet hε hG hperiod t 1)

/-- The reference-size integral also uses the original speed only. -/
def circleFlowLocalReferenceSize (c : ℝ → ℝ) (s : ℕ) : ℝ :=
  ∫ t in a..b, circleRealSobolevNorm (s : ℝ)
    (circleSubtractConstantJet (circleFlowLocalSpeedJet hε hG hperiod t) (c t) 0)

theorem circleFlowSpeedJet_localized_eq (hab : a ≤ b)
    {t : ℝ} (ht : t ∈ Icc a b) (n : ℕ) :
    circleFlowSpeedJet (circleFlowLocalizedSpeed G hab hε)
        (contDiff_circleFlowLocalizedSpeed hab hε hG)
        (circleFlowLocalizedSpeed_periodic hab hε hperiod) t n =
      circleFlowLocalSpeedJet hε hG hperiod t n := by
  ext x
  refine QuotientAddGroup.induction_on x ?_
  intro θ
  simp only [circleFlowSpeedJet_coe_apply,
    circleFlowLocalSpeedJet_coe_apply hε hG hperiod ht n θ]
  rw [circleFlowLocalizedSpeed_slice_eq hab hε ht]

theorem continuousOn_circleFlowLocalSpeedJet (hab : a ≤ b) (n : ℕ) :
    ContinuousOn (fun t => circleFlowLocalSpeedJet hε hG hperiod t n) (Icc a b) := by
  have h : ContinuousOn (fun t =>
      circleFlowSpeedJet (circleFlowLocalizedSpeed G hab hε)
        (contDiff_circleFlowLocalizedSpeed hab hε hG)
        (circleFlowLocalizedSpeed_periodic hab hε hperiod) t n) (Icc a b) :=
    (continuous_circleFlowSpeedJet (circleFlowLocalizedSpeed G hab hε)
      (contDiff_circleFlowLocalizedSpeed hab hε hG)
      (circleFlowLocalizedSpeed_periodic hab hε hperiod) n).continuousOn
  exact h.congr (fun t ht => (circleFlowSpeedJet_localized_eq hε hG hperiod hab ht n).symm)

theorem continuousOn_circleFlowLocalSpeedSobolevNorm (hab : a ≤ b) (s k : ℕ) :
    ContinuousOn (fun t => circleRealSobolevNorm (s : ℝ)
      (circleFlowLocalSpeedJet hε hG hperiod t k)) (Icc a b) := by
  have h : ContinuousOn (fun t => circleRealSobolevNorm (s : ℝ)
      (circleFlowSpeedJet (circleFlowLocalizedSpeed G hab hε)
        (contDiff_circleFlowLocalizedSpeed hab hε hG)
        (circleFlowLocalizedSpeed_periodic hab hε hperiod) t k)) (Icc a b) :=
    (continuous_circleFlowSpeedSobolevNorm (circleFlowLocalizedSpeed G hab hε)
      (contDiff_circleFlowLocalizedSpeed hab hε hG)
      (circleFlowLocalizedSpeed_periodic hab hε hperiod) s k).continuousOn
  apply h.congr
  intro t ht
  dsimp only
  rw [circleFlowSpeedJet_localized_eq hε hG hperiod hab ht k]

theorem intervalIntegrable_circleFlowLocalSpeedSobolevNorm
    (hab : a ≤ b) (s k : ℕ) :
    IntervalIntegrable (fun t => circleRealSobolevNorm (s : ℝ)
      (circleFlowLocalSpeedJet hε hG hperiod t k)) volume a b :=
  (continuousOn_circleFlowLocalSpeedSobolevNorm hε hG hperiod hab s k).intervalIntegrable_of_Icc hab

theorem circleFlowLambda_localized_eq (hab : a ≤ b) (s : ℕ) :
    circleFlowLambda (circleFlowLocalizedSpeed G hab hε)
        (contDiff_circleFlowLocalizedSpeed hab hε hG)
        (circleFlowLocalizedSpeed_periodic hab hε hperiod) s a b =
      circleFlowLocalLambda hε hG hperiod s := by
  dsimp only [circleFlowLambda, circleFlowLocalLambda]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
  dsimp only
  rw [circleFlowSpeedJet_localized_eq hε hG hperiod hab ht' 1]

theorem circleFlowReferenceSize_localized_eq (hab : a ≤ b)
    (c : ℝ → ℝ) (s : ℕ) :
    circleFlowReferenceSize (circleFlowLocalizedSpeed G hab hε)
        (contDiff_circleFlowLocalizedSpeed hab hε hG)
        (circleFlowLocalizedSpeed_periodic hab hε hperiod) c s a b =
      circleFlowLocalReferenceSize hε hG hperiod c s := by
  dsimp only [circleFlowReferenceSize, circleFlowReferenceNorm, circleFlowLocalReferenceSize]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
  have hjet :
      circleFlowSpeedJet (circleFlowLocalizedSpeed G hab hε)
        (contDiff_circleFlowLocalizedSpeed hab hε hG)
        (circleFlowLocalizedSpeed_periodic hab hε hperiod) t =
      circleFlowLocalSpeedJet hε hG hperiod t :=
    funext (circleFlowSpeedJet_localized_eq hε hG hperiod hab ht')
  dsimp only
  rw [hjet]

end ContinuousFlexibility.Analysis
