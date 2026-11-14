module

public import ContinuousFlexibility.Radial.OuterActualGreenUniform
public import ContinuousFlexibility.Radial.OuterManuscriptBounds
public import ContinuousFlexibility.Radial.OuterMorseKernelEnvelope
public import ContinuousFlexibility.Radial.OuterOrdinaryJacobiSource
public import ContinuousFlexibility.Radial.FlatEndpointUnweightedObstruction

/-!
# Uniform actual outer inverses and their manuscript estimates

All constants and the initial cutoff are chosen before the height
sequence, cell, frequency, orientation, state scale or localizer. The
conclusion retains one actual basis, one normalized homogeneous pair,
one Robin inverse, and the four core/deep inputs for that same basis.

The ordinary estimates here are localized. The proposed global ordinary
L² bound in the manuscript is contradicted by the flat-endpoint theorem
imported above; no bounded global ordinary inverse is asserted.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open ContinuousFlexibility.Statements

/-- The valid assertions of Lemmas 6.4 and 6.5, with common constants
and the full cubic localized decay, for the actual realized family.
The full inverse and all its localizations use the same physical kernel. -/
theorem exists_uniform_morseOuterInverse
    (M : MorseChainData) (C : ℕ → ℝ) (family : (ℕ → ℝ) → ReferenceData)
    (hfamily : ∀ σ, (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) →
      MorseChainRealization M σ (family σ) C ∧
        MorseMassResistanceBounds M σ (family σ) C)
    (hends : ∀ σ τ, (family σ).a = (family τ).a ∧
      (family σ).b = (family τ).b)
    {Cstar L η K : ℝ} (hCstar : 0 < Cstar) (hL : 0 ≤ L)
    (hηpos : 0 < η) (hη : η ≤ 1 / 16) (hK : 32 ≤ K)
    (hKinv : 10 * tailSmoothStepConstant + 2 ≤ K) (minimum : ℕ) :
    ∃ Cbound Co Cenv : ℝ, 0 < Cbound ∧ 0 < Co ∧ 0 < Cenv ∧
      ∃ N₀ : ℕ, minimum ≤ N₀ ∧ M.index + 3 ≤ N₀ ∧ 31 ≤ N₀ ∧
        ∀ n : ℕ, N₀ ≤ n → ∀ σ, ∀ hσ : (∀ k, 1 ≤ σ k ∧ σ k ≤ 2),
          ∀ j : ℕ, 2 ≤ j → (j : ℝ) < radialFrequencyThreshold M Cstar n →
            ∀ entry : ℝ, entry ∈ morseInitialMiddle M → ∀ right : Bool,
              ∀ lam : ℝ, 0 < lam →
                lam / morseChainAmplitude M σ n ≤ exp (L * (n : ℝ) ^ 2) →
                morseChainAmplitude M σ n / lam ≤ exp (L * (n : ℝ) ^ 2) →
                ∃ G : MorseOuterGreenData M (family σ) right n j
                    entry η K lam Cbound Co,
                  MorseOuterInverseBounds G (hfamily σ hσ).1.accumulating.2.1 Cenv := by
  let σ₀ : ℕ → ℝ := fun _ => 1
  let D₀ := family σ₀
  have hσ₀ : ∀ k, 1 ≤ σ₀ k ∧ σ₀ k ≤ 2 :=
    fun _ => ⟨le_rfl, by norm_num [σ₀]⟩
  have h₀ := (hfamily σ₀ hσ₀).1
  have hC0 : 0 < C 0 := h₀.constants_pos 0
  have hb0 : 0 < D₀.b := h₀.geometry.1.trans h₀.geometry.2.1
  obtain ⟨Nl, hlabels⟩ := eventually_atTop.mp
    (morseOuter_eventually_uniform_localizer_labels M C family
      (fun σ hσ => (hfamily σ hσ).1) hends)
  obtain ⟨Cbound, Co, hCb, hCo, N₀, hmin, hidx, h31, hdata⟩ :=
    exists_uniform_morseOuterGreenData M C family hfamily hends hCstar hL hηpos hη hK hKinv
      (max minimum Nl)
  obtain ⟨Q, hQ, hpoint⟩ := exists_morseOuterGreen_kernel_envelope_uniform
    hC0 hb0 hL hCb.le hCo.le
  let W := outerMorseOperatorExponent D₀.a D₀.b C Q hQ.le
  let O := outerMorseOrdinaryExponent D₀.a D₀.b C Q hQ.le
  let Cenv := max Cbound (max W O)
  have hCenv : Cbound ≤ Cenv := le_max_left _ _
  have hWenv : W ≤ Cenv := (le_max_left _ _).trans (le_max_right _ _)
  have hOenv : O ≤ Cenv := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨Cbound, Co, Cenv, hCb, hCo, hCb.trans_le hCenv,
    N₀, (le_max_left _ _).trans hmin, hidx, h31, ?_⟩
  intro n hn σ hσ j hj hupper entry he right lam hlam hhi hlo
  have hreal := (hfamily σ hσ).1
  have hmass := (hfamily σ hσ).2
  have hsame := hends σ σ₀
  have hnidx : M.index + 3 ≤ n := hidx.trans hn
  have hnl : Nl ≤ n := (le_max_right _ _).trans (hmin.trans hn)
  have hlabelsσ := (hlabels n hnl).2 σ hσ
  obtain ⟨G⟩ := hdata n hn σ hσ j hj hupper entry he right lam hlam hhi hlo
  have hpointG := hpoint M σ (family σ) hreal hσ hmass hsame.2 right n j entry η K lam
    (by omega : M.index ≤ n) (h31.trans hn) hj he hη hK hlam hlo G
  refine ⟨G, ?_⟩
  exact G.manuscript_bounds hreal hreal.accumulating.2.1 hsame.1 hsame.2 he hnidx hlabelsσ
    hlam hCb.le hQ.le hCenv hWenv hOenv hpointG

/-- Fix the two auxiliary tail-construction constants internally. The
remaining hypotheses are only the realized family, its frequency scale,
and the permitted change of physical state scale. -/
theorem exists_uniform_morseOuterInverse_fixed_parameters
    (M : MorseChainData) (C : ℕ → ℝ) (family : (ℕ → ℝ) → ReferenceData)
    (hfamily : ∀ σ, (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) →
      MorseChainRealization M σ (family σ) C ∧
        MorseMassResistanceBounds M σ (family σ) C)
    (hends : ∀ σ τ, (family σ).a = (family τ).a ∧
      (family σ).b = (family τ).b)
    {Cstar L : ℝ} (hCstar : 0 < Cstar) (hL : 0 ≤ L) (minimum : ℕ) :
    let η : ℝ := 1 / 16
    let K : ℝ := max 32 (10 * tailSmoothStepConstant + 2)
    ∃ Cbound Co Cenv : ℝ, 0 < Cbound ∧ 0 < Co ∧ 0 < Cenv ∧
      ∃ N₀ : ℕ, minimum ≤ N₀ ∧ M.index + 3 ≤ N₀ ∧ 31 ≤ N₀ ∧
        ∀ n : ℕ, N₀ ≤ n → ∀ σ, ∀ hσ : (∀ k, 1 ≤ σ k ∧ σ k ≤ 2),
          ∀ j : ℕ, 2 ≤ j → (j : ℝ) < radialFrequencyThreshold M Cstar n →
            ∀ entry : ℝ, entry ∈ morseInitialMiddle M → ∀ right : Bool,
              ∀ lam : ℝ, 0 < lam →
                lam / morseChainAmplitude M σ n ≤ exp (L * (n : ℝ) ^ 2) →
                morseChainAmplitude M σ n / lam ≤ exp (L * (n : ℝ) ^ 2) →
                ∃ G : MorseOuterGreenData M (family σ) right n j
                    entry η K lam Cbound Co,
                  MorseOuterInverseBounds G (hfamily σ hσ).1.accumulating.2.1 Cenv := by
  dsimp only
  exact exists_uniform_morseOuterInverse M C family hfamily hends hCstar hL
    (by norm_num : 0 < (1 / 16 : ℝ)) le_rfl (le_max_left _ _) (le_max_right _ _) minimum

#print axioms exists_uniform_morseOuterInverse_fixed_parameters

#print axioms exists_uniform_morseOuterInverse
#print axioms OuterPhysicalRobinInverse.assertions
#print axioms OuterPhysicalRobinInverse.ordinary_jacobi_source
#print axioms accumulatingProfile_no_unweighted_outer_inverse

end ContinuousFlexibility.Radial
