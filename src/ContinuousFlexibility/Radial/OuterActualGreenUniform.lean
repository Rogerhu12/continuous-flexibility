module

public import ContinuousFlexibility.Radial.OuterActualGreenData
public import ContinuousFlexibility.Radial.OuterDeepUniform
public import ContinuousFlexibility.Radial.OuterPhysicalTailBasisNorm

/-!
# Uniform actual outer Green data from the realized Morse family

The cell certificate, natural-mass constant, deep cutoff and final
envelope exponents are all chosen before the height sequence, physical
frequency, endpoint, middle cut and allowed state scale. Every tail,
basis, homogeneous pair and inverse is then constructed on the actual
profile. No deep hypothesis or final norm estimate is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

/-- Uniform actual construction of the weighted outer Robin inverse,
including its same-basis core, natural-vector and operator norm estimates. -/
theorem exists_uniform_morseOuterGreenData
    (M : MorseChainData) (C : ℕ → ℝ) (family : (ℕ → ℝ) → ReferenceData)
    (hfamily : ∀ σ, (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) →
      MorseChainRealization M σ (family σ) C ∧
        MorseMassResistanceBounds M σ (family σ) C)
    (hends : ∀ σ τ, (family σ).a = (family τ).a ∧
      (family σ).b = (family τ).b)
    {Cstar L η K : ℝ} (hCstar : 0 < Cstar) (hL : 0 ≤ L)
    (hηpos : 0 < η) (hη : η ≤ 1 / 16) (hK : 32 ≤ K)
    (hKinv : 10 * tailSmoothStepConstant + 2 ≤ K) (minimum : ℕ) :
    ∃ Cbound Co : ℝ, 0 < Cbound ∧ 0 < Co ∧
      ∃ N₀ : ℕ, minimum ≤ N₀ ∧ M.index + 3 ≤ N₀ ∧ 31 ≤ N₀ ∧
        ∀ n : ℕ, N₀ ≤ n → ∀ σ, (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) →
          ∀ j : ℕ, 2 ≤ j → (j : ℝ) < radialFrequencyThreshold M Cstar n →
            ∀ entry : ℝ, entry ∈ morseInitialMiddle M → ∀ right : Bool,
              ∀ lam : ℝ, 0 < lam →
                lam / morseChainAmplitude M σ n ≤ exp (L * (n : ℝ) ^ 2) →
                morseChainAmplitude M σ n / lam ≤ exp (L * (n : ℝ) ^ 2) →
                Nonempty (MorseOuterGreenData M (family σ) right n j
                  entry η K lam Cbound Co) := by
  let σ₀ : ℕ → ℝ := fun _ => 1
  let D₀ := family σ₀
  have hσ₀ : ∀ k, 1 ≤ σ₀ k ∧ σ₀ k ≤ 2 :=
    fun _ => ⟨le_rfl, by norm_num [σ₀]⟩
  have h₀ : MorseChainRealization M (fun _ => 1) D₀ C := (hfamily σ₀ hσ₀).1
  obtain ⟨B, hcell⟩ := exists_morseRealizedCellEstimates h₀
  obtain ⟨Pexp, hPexp, hnorm⟩ :=
    exists_morsePhysicalTailBasis_all_indices_norm_of_upper h₀ hcell hCstar
  let Qe := outerFullCoreQuadraticExponent C B D₀.a Cstar L
  let Qm := L + 135 + 2 * outerCoreMassPrefactor D₀ D₀ C B
  let Qp := Pexp + L
  let Q := Qe + Qm + Qp + 1
  let Co := outerFullCoreActionExponent C B D₀.a
  have hB := hcell.pos
  have hC := h₀.constants_pos 0
  have ha := h₀.geometry.1
  have hQe : 0 ≤ Qe := by
    dsimp only [Qe, outerFullCoreQuadraticExponent, outerCoreInteriorQuadraticExponent,
      outerCoreQuadraticExponent, outerOutgoingQuadraticExponent, outerFrequencyExponent,
      outerJoinPrefactor]
    positivity
  have hQm : 0 ≤ Qm := by dsimp only [Qm, outerCoreMassPrefactor]; positivity
  have hQp : 0 ≤ Qp := by dsimp only [Qp]; linarith only [hPexp, hL]
  have hQ : 0 ≤ Q := by dsimp only [Q]; linarith only [hQe, hQm, hQp]
  have hCo : 0 < Co := by
    dsimp only [Co, outerFullCoreActionExponent, outerCoreActionExponent, outerOutgoingActionExponent]
    positivity
  obtain ⟨N₀, hmin, hidx, h31, hdeep⟩ :=
    outer_exists_uniform_actual_deepTailPhysical M C family hfamily hends hCstar hηpos
      (hη.trans_lt (by norm_num : (1 / 16 : ℝ) < 1))
      (by linarith only [hK] : 1 < K) (max minimum (M.index + 3))
  refine ⟨12 + 4 * Q, Co, by linarith only [hQ], hCo, N₀,
    (le_max_left _ _).trans hmin, (le_max_right _ _).trans hmin, h31, ?_⟩
  intro n hn σ hσ j hj hupper entry he right lam hlam hhi hlo
  have hnidx : M.index < n := by
    have hidx3 : M.index + 3 ≤ N₀ := (le_max_right _ _).trans hmin
    omega
  have hn1 : 1 ≤ n := by omega
  have h := (hfamily σ hσ).1
  have ht := hdeep n hn σ hσ j hj hupper right
  have hentryMass := morseOuterDeepEntrance_mass_left_le h right n hnidx.le
  obtain ⟨F, hP, hPnorm⟩ := hnorm σ (family σ) C hσ h n hn1 hnidx.le j hupper
    right (morseOuterDeepEntrance M right n) η K hentryMass hη hK ht.2.1
  have hPscale : ‖hP.toLp F.P‖ ≤ sqrt lam * exp (Qp * (n : ℝ) ^ 2) :=
    outer_natural_norm_change_scale hlam (morseChainAmplitude_pos M σ hσ n).le hL hlo hPnorm
  have hdata := exists_morseOuterGreenData_of_deep h₀ h hσ hcell hlam hL he right
    hnidx hj hupper hhi hlo hη hK hKinv ht.2.1 ht.2.2 ht.1 F hP hQp hPscale
  have hsame : (family σ).a = D₀.a := (hends σ σ₀).1
  dsimp only at hdata
  simpa only [Q, Qe, Qm, Qp, Co, outerCoreMassPrefactor, hsame] using hdata

end ContinuousFlexibility.Radial
