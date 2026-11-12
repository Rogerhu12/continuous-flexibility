import ContinuousFlexibility.Radial.ReferenceRawKernelSchur
import ContinuousFlexibility.Radial.MatchedPhysicalChannelComparison

/-!
# From actual modal channel estimates to the physical raw envelope

The density conversion already proved for all four kinds of channel
costs only one fixed coefficient exponential at each endpoint. This
short bridge absorbs those two costs into the unweighted modal envelope.
An estimate for the actual modal channels remains an explicit input;
no such estimate is inferred from the matching formula alone.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open ContinuousFlexibility.Radial

theorem referenceChannelDensityCost_le (D : ReferenceData) {K : ℝ}
    (hK : 0 < K) (k : ℕ) :
    matchedChannelDensityCost D K k ≤
      (K + 1) * Real.exp (K * radialQ (referenceRawChannelLevel D k)) := by
  cases k with
  | zero =>
      change 1 ≤ (K + 1) * Real.exp (K * radialQ 0)
      have hq : radialQ 0 = 0 := by norm_num [radialQ]
      rw [hq, mul_zero, Real.exp_zero, mul_one]
      linarith
  | succ k =>
      change Real.sqrt (K * radialE (D.cellIndex k) ^ K) ≤
        (K + 1) * Real.exp (K * radialQ (D.cellIndex k))
      have hpow : radialE (D.cellIndex k) ^ K =
          Real.exp (K * radialQ (D.cellIndex k)) := by
        rw [radialE, ← Real.exp_mul]
        congr 1
        ring
      rw [hpow]
      let e : ℝ := Real.exp (K * radialQ (D.cellIndex k))
      have he : 1 ≤ e := by
        have hh := Real.exp_le_exp.mpr
          (mul_nonneg hK.le (radialQ_nonneg (D.cellIndex k)))
        simpa only [Real.exp_zero, e] using hh
      have hx : 0 ≤ K * e := mul_nonneg hK.le (zero_le_one.trans he)
      have hs : Real.sqrt (K * e) ≤ K * e + 1 := by
        have hsq := Real.sq_sqrt hx
        have hn := Real.sqrt_nonneg (K * e)
        nlinarith only [hsq, hn, sq_nonneg (Real.sqrt (K * e) - 1)]
      exact hs.trans (by nlinarith only [he])

/-- Density costs replace the modal exponent a by a + K and its
constant C₀ by (K + 1)² C₀, uniformly in every actual operator channel. -/
theorem referenceRawKernel_envelope_of_modal_channels {D : ReferenceData}
    (hD : IsAccumulatingProfile D)
    (G : ℕ → RadialModePair D →L[ℝ] RadialModePair D)
    {C₀ a : ℝ} (hC₀ : 0 < C₀)
    (hmodal : ∀ n k m,
      ‖matchedModeChannel D hD.choose_spec.2.1 k ∘L
          (G n ∘L matchedModeScalarGate D (decide (n = 0))) ∘L
            matchedModeChannel D hD.choose_spec.2.1 m‖ ≤
        C₀ * Real.exp
          (a * (radialQ (referenceRawChannelLevel D k) +
            radialQ (referenceRawChannelLevel D m)) -
            |radialS (referenceRawChannelLevel D k) -
              radialS (referenceRawChannelLevel D m)|)) :
    ∃ C₁ a₁ : ℝ, 0 < C₁ ∧ ∀ n k m,
      matchedPhysicalRawKernel D hD hD.choose_spec.2.1
          (G n ∘L matchedModeScalarGate D (decide (n = 0))) k m ≤
        C₁ * Real.exp
          (a₁ * (radialQ (referenceRawChannelLevel D k) +
            radialQ (referenceRawChannelLevel D m)) -
            |radialS (referenceRawChannelLevel D k) -
              radialS (referenceRawChannelLevel D m)|) := by
  obtain ⟨K, hK, hconversion⟩ :=
    exists_matchedPhysicalRawKernel_density_cost hD hD.choose_spec.2.1
  have hcost0 (k : ℕ) : 0 ≤ matchedChannelDensityCost D K k := by
    cases k <;> dsimp only [matchedChannelDensityCost] <;> positivity
  refine ⟨(K + 1) ^ 2 * C₀, a + K, by positivity, ?_⟩
  intro n k m
  have hp :
      matchedChannelDensityCost D K k * matchedChannelDensityCost D K m ≤
        ((K + 1) * Real.exp (K * radialQ (referenceRawChannelLevel D k))) *
          ((K + 1) * Real.exp (K * radialQ (referenceRawChannelLevel D m))) :=
    mul_le_mul (referenceChannelDensityCost_le D hK k)
      (referenceChannelDensityCost_le D hK m) (hcost0 m) (by positivity)
  apply (hconversion (G n ∘L matchedModeScalarGate D (decide (n = 0))) k m).trans
  calc
    _ ≤ (((K + 1) * Real.exp (K * radialQ (referenceRawChannelLevel D k))) *
          ((K + 1) * Real.exp (K * radialQ (referenceRawChannelLevel D m)))) *
        (C₀ * Real.exp
          (a * (radialQ (referenceRawChannelLevel D k) +
            radialQ (referenceRawChannelLevel D m)) -
            |radialS (referenceRawChannelLevel D k) -
              radialS (referenceRawChannelLevel D m)|)) :=
      mul_le_mul hp (hmodal n k m) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [show (a + K) *
          (radialQ (referenceRawChannelLevel D k) + radialQ (referenceRawChannelLevel D m)) -
          |radialS (referenceRawChannelLevel D k) - radialS (referenceRawChannelLevel D m)| =
        K * radialQ (referenceRawChannelLevel D k) +
          K * radialQ (referenceRawChannelLevel D m) +
          (a * (radialQ (referenceRawChannelLevel D k) + radialQ (referenceRawChannelLevel D m)) -
            |radialS (referenceRawChannelLevel D k) -
              radialS (referenceRawChannelLevel D m)|) by ring,
        Real.exp_add, Real.exp_add]
      ring

/-- The established reference-space construction now needs only bounds
for the actual modal channels and the actual finite level fibers. -/
theorem referenceSchur_common_inverse_of_modal_envelope {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (G : ℕ → RadialModePair D →L[ℝ] RadialModePair D)
    (hG : ∀ n : ℕ, ModeInverseProperties D (2 * (n + 1)) (G n))
    (N : ℕ) (hfibers : ∀ n, Set.Finite {m | D.cellIndex m = n})
    (hcard : ∀ n, Set.ncard {m | D.cellIndex m = n} ≤ N)
    {C₀ a : ℝ} (hC₀ : 0 < C₀)
    (hmodal : ∀ n k m,
      ‖matchedModeChannel D hD.choose_spec.2.1 k ∘L
          (G n ∘L matchedModeScalarGate D (decide (n = 0))) ∘L
            matchedModeChannel D hD.choose_spec.2.1 m‖ ≤
        C₀ * Real.exp
          (a * (radialQ (referenceRawChannelLevel D k) +
            radialQ (referenceRawChannelLevel D m)) -
            |radialS (referenceRawChannelLevel D k) -
              radialS (referenceRawChannelLevel D m)|)) :
    ∃ M₀ M₁ : ℝ, 0 ≤ M₁ ∧ ∃ H : RadialSource → RadialUnknown,
      ∀ γ : ℝ,
      γ = referenceBeta - 1 / 8 ∨ γ = referenceBeta ∨ γ = referenceBeta + 1 / 8 →
        ReferenceInverseProperties D γ M₀ M₁ H := by
  obtain ⟨C₁, a₁, hC₁, hraw⟩ :=
    referenceRawKernel_envelope_of_modal_channels hD G hC₀ hmodal
  exact referenceSchur_common_inverse_of_raw_envelope
    hD hborder G hG N hfibers hcard hC₁ hraw

end ContinuousFlexibility.Statements
