import ContinuousFlexibility.Radial.OuterOutwardCoreState

/-!
# The selected-band envelope for the same actual outer pair

The original outward-core theorem supplies the value/flux estimate for
the constructed pair, including its initial compact band.  The upper
frequency cutoff at this same transition cell absorbs its action into
the coefficient weight.  Constants may depend on the fixed actual
profile; they are chosen before the frequency and the pair.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

/-- The upper action estimate is valid at the selected cell itself,
including frequencies below its old lower band endpoint. -/
theorem matchedTransition_action_lt_of_upper
    {T : MorseChainData} {Cstar : ℝ} {n j : ℕ}
    (hd : T.d n = morseChainInteger n)
    (hupper : (j : ℝ) < radialFrequencyThreshold T Cstar n) :
    (j : ℝ) * sqrt (morseChainA T n) < Cstar * radialQ n := by
  have hA : 0 < morseChainA T n :=
    (div_pos (exp_pos (-(n : ℝ) ^ 2)) (by norm_num : (0 : ℝ) < 3)).trans_le
      (morseChainA_exp_bounds T n hd).1
  exact (lt_div_iff₀ (sqrt_pos.mpr hA)).mp hupper

/-- The actual quadratic/action exponent fits the same coefficient
weight using only the upper frequency cutoff. -/
theorem matchedTransition_exponent_le_of_upper
    {T : MorseChainData} {Cstar : ℝ} {n j : ℕ}
    (hd : T.d n = morseChainInteger n)
    (hupper : (j : ℝ) < radialFrequencyThreshold T Cstar n) (q b : ℝ) :
    q * (n : ℝ) ^ 2 + b * ((j : ℝ) * sqrt (morseChainA T n)) ≤
      (|q| + |b| * Cstar) * radialQ n := by
  have hq : q * (n : ℝ) ^ 2 ≤ |q| * radialQ n :=
    (mul_le_mul_of_nonneg_right (le_abs_self q) (sq_nonneg (n : ℝ))).trans
      (mul_le_mul_of_nonneg_left (radial_nat_sq_le_Q n) (abs_nonneg q))
  have hb : b * ((j : ℝ) * sqrt (morseChainA T n)) ≤
      |b| * (Cstar * radialQ n) :=
    (mul_le_mul_of_nonneg_right (le_abs_self b)
      (mul_nonneg (Nat.cast_nonneg j) (sqrt_nonneg _))).trans
      (mul_le_mul_of_nonneg_left (matchedTransition_action_lt_of_upper hd hupper).le
        (abs_nonneg b))
  calc
    _ ≤ |q| * radialQ n + |b| * (Cstar * radialQ n) := add_le_add hq hb
    _ = _ := by ring

/-- A common coefficient controls all four components of the supplied
actual fundamental pair throughout its actual core.  In particular,
the same natural solution has `|V(c)| ≤ exp(A Q_n)` at the deep entrance.
The first frequency band is included; no boundary value is divided by. -/
theorem exists_matchedMorse_actual_core_pair_bound
    {M : MorseChainData} {σ : ℕ → ℝ} {D₀ D : ReferenceData} {C : ℕ → ℝ}
    {Cstar L : ℝ}
    (h₀ : MorseChainRealization M (fun _ => 1) D₀ C)
    (h : MorseChainRealization M σ D C)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) (hCstar : 0 < Cstar) (hL : 0 ≤ L) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (entry : ℝ) (he : entry ∈ morseInitialMiddle M) (right : Bool)
        (n j : ℕ) (hband : radialFrequencyBand M Cstar n j)
        (lam : ℝ) (hlam : 0 < lam),
        lam / morseChainAmplitude M σ n ≤ exp (L * (n : ℝ) ^ 2) →
        morseChainAmplitude M σ n / lam ≤ exp (L * (n : ℝ) ^ 2) →
        ∀ (b : ℝ) (P ZP Q ZQ : ℝ → ℝ)
          (H : OuterFundamentalStatePair
            (fun x => lam / outerTailOutwardWeight D right x)
            (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
            P ZP Q ZQ (morseTransitionOutwardLeft M entry right n)
              (morseTransitionOutwardRight M entry right n) b),
          morseTransitionOutwardRight M entry right n < b →
          ∀ x ∈ Icc (morseTransitionOutwardLeft M entry right n)
              (morseTransitionOutwardRight M entry right n),
            |H.U x| ≤ exp (A * radialQ n) ∧
              |H.ZU x| ≤ exp (A * radialQ n) ∧
              |H.V x| ≤ exp (A * radialQ n) ∧
              |H.ZV x| ≤ exp (A * radialQ n) := by
  obtain ⟨K, hcell⟩ := exists_morseRealizedCellEstimates h₀
  let q := morseTransitionEnergyConstant M σ D C K Cstar L
  let co := outerFullCoreActionExponent C K D.a
  let A := |q| + |co| * Cstar + 1
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro entry he right n j hband lam hlam hhi hlo b P ZP Q ZQ H hcb x hx
  have hQ : 0 ≤ radialQ n := (sq_nonneg (n : ℝ)).trans (radial_nat_sq_le_Q n)
  have hcost : q * (n : ℝ) ^ 2 + co * ((j : ℝ) * sqrt (morseChainA M n)) ≤
      A * radialQ n :=
    (matchedTransition_exponent_le_of_upper (h.d_eq n hband.1) hband.2.2 q co).trans
      (mul_le_mul_of_nonneg_right (by dsimp only [A]; linarith) hQ)
  have hE := exp_le_exp.mpr hcost
  have hb := OuterFundamentalStatePair.morseTransition_core_bounds
    h hσ hcell hlam hL he right hband hhi hlo H hcb x hx
  exact ⟨hb.1.trans hE, hb.2.1.trans hE, hb.2.2.1.trans hE, hb.2.2.2.trans hE⟩

end ContinuousFlexibility.Radial
