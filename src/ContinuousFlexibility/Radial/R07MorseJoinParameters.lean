import ContinuousFlexibility.Radial.R07LogGermParameter
import ContinuousFlexibility.Radial.MorseChainProfileGluing

/-!
# The height parameters of the chosen Morse joins

The actual join family was defined using choices of smooth extensions.  Its
values on each physical join nevertheless have a fixed formula in the two
logarithmic cell amplitudes.  This file proves that fact for the existing
family, rather than adding any continuity or equivariance hypotheses to it.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff BigOperators

/-- The unit height sequence, used only as a fixed reference profile. -/
def morseUnitHeights : ℕ → ℝ := fun _ => 1

theorem morseUnitHeights_admissible (n : ℕ) :
    1 ≤ morseUnitHeights n ∧ morseUnitHeights n ≤ 2 := by
  norm_num [morseUnitHeights]

private def morseDoubleInitialHeight (T : Statements.MorseChainData) : ℕ → ℝ :=
  fun n => if n = T.index then 2 else 1

private theorem morseDoubleInitialHeight_admissible (T : Statements.MorseChainData) (n : ℕ) :
    1 ≤ morseDoubleInitialHeight T n ∧ morseDoubleInitialHeight T n ≤ 2 := by
  unfold morseDoubleInitialHeight
  split_ifs <;> norm_num

private theorem morseChainAmplitude_doubleInitial (T : Statements.MorseChainData)
    {n : ℕ} (hn : T.index ≤ n) :
    Statements.morseChainAmplitude T (morseDoubleInitialHeight T) n =
      2 * Statements.morseChainAmplitude T morseUnitHeights n := by
  have hp : (∏ i ∈ Finset.Icc T.index n, morseDoubleInitialHeight T i) = 2 := by
    rw [Finset.prod_eq_single T.index]
    · simp only [morseDoubleInitialHeight, if_pos rfl]
    · intro i _ hi
      simp only [morseDoubleInitialHeight, if_neg hi]
    · intro hnot
      exact False.elim (hnot (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩))
  simp only [Statements.morseChainAmplitude, hp, morseUnitHeights, Finset.prod_const_one,
    mul_one, mul_comm]

theorem morseChainPhysicalModelHeight_amplitude {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (A : ℝ) (side : Bool) (k : ℕ) (x : ℝ) :
    morseChainPhysicalModelHeight G A side k x =
      A * morseChainPhysicalModelHeight G 1 side k x := by
  simp only [morseChainPhysicalModelHeight, one_mul, mul_assoc]

theorem morseChainPhysicalModelLog_amplitude {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (A : ℝ) (side : Bool) (k : ℕ) (x : ℝ) :
    morseChainPhysicalModelLog G A side k x =
      log (A * morseChainPhysicalModelHeight G 1 side k x) := by
  simp only [morseChainPhysicalModelLog, morseCollarLogProfile,
    morseChainPhysicalModelHeight, one_mul, mul_assoc]

/-- The log-amplitude relative to the unit height sequence. -/
def morseChainHeightLogRatio (T : Statements.MorseChainData) (σ : ℕ → ℝ) (n : ℕ) : ℝ :=
  log (Statements.morseChainAmplitude T σ n) -
    log (Statements.morseChainAmplitude T morseUnitHeights n)

/-- Both collar logarithms of the actual chosen join differ from the unit
ones by the corresponding cell log-amplitude.  One connected-collar argument
treats both endpoints. -/
theorem morseChainChosenJoin_log_germs {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (σ : ℕ → ℝ)
    (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) (side : Bool) (k : ℕ) :
    let P := morseChainChosenJoin G σ hσ side k
    let P₀ := morseChainChosenJoin G morseUnitHeights morseUnitHeights_admissible side k
    let a := T.joinLeft side (T.index + k)
    let b := T.joinRight side (T.index + k)
    let h := morseChainProfileJoinCutoff T side k
    (∀ x ∈ Icc a (a + h), P.leftLog =ᶠ[𝓝 x] fun y => P₀.leftLog y +
      morseChainHeightLogRatio T σ (T.index + morseChainJoinDeparture side k)) ∧
    (∀ x ∈ Icc (b - h) b, P.rightLog =ᶠ[𝓝 x] fun y => P₀.rightLog y +
      morseChainHeightLogRatio T σ (T.index + morseChainJoinArrival side k)) := by
  dsimp only
  let P (τ : ℕ → ℝ) (hτ : ∀ n, 1 ≤ τ n ∧ τ n ≤ 2) :=
    morseChainChosenJoin G τ hτ side k
  let a := T.joinLeft side (T.index + k)
  let b := T.joinRight side (T.index + k)
  let h := morseChainProfileJoinCutoff T side k
  have hh : 0 < h := div_pos (sub_pos.mpr (morseChainPhysicalJoin_order G side k))
    (by norm_num : (0 : ℝ) < 4)
  have hshift (rightBoundary : Bool) :
      let i := if rightBoundary then morseChainJoinArrival side k else morseChainJoinDeparture side k
      let s := if rightBoundary then Icc (b - h) b else Icc a (a + h)
      let F (τ : ℕ → ℝ) (hτ : ∀ n, 1 ≤ τ n ∧ τ n ≤ 2) :=
        if rightBoundary then (P τ hτ).rightLog else (P τ hτ).leftLog
      ∀ x ∈ s, F σ hσ =ᶠ[𝓝 x] fun y =>
        F morseUnitHeights morseUnitHeights_admissible y +
          morseChainHeightLogRatio T σ (T.index + i) := by
    dsimp only
    let i := if rightBoundary then morseChainJoinArrival side k else morseChainJoinDeparture side k
    let s : Set ℝ := if rightBoundary then Icc (b - h) b else Icc a (a + h)
    let x₀ := if rightBoundary then b else a
    let F (τ : ℕ → ℝ) (hτ : ∀ n, 1 ≤ τ n ∧ τ n ≤ 2) : ℝ → ℝ :=
      if rightBoundary then (P τ hτ).rightLog else (P τ hτ).leftLog
    let W := morseChainPhysicalModelHeight G 1 side i
    let A (τ : ℕ → ℝ) := Statements.morseChainAmplitude T τ (T.index + i)
    have hA (τ : ℕ → ℝ) (hτ : ∀ n, 1 ≤ τ n ∧ τ n ≤ 2) : 0 < A τ :=
      morseChainAmplitude_pos T τ hτ _
    have hF (τ : ℕ → ℝ) (hτ : ∀ n, 1 ≤ τ n ∧ τ n ≤ 2) : Continuous (F τ hτ) := by
      cases rightBoundary
      · exact (P τ hτ).left_smooth.continuous
      · exact (P τ hτ).right_smooth.continuous
    have hg (τ : ℕ → ℝ) (hτ : ∀ n, 1 ≤ τ n ∧ τ n ≤ 2) :
        ∀ x ∈ s, F τ hτ =ᶠ[𝓝 x] fun y => log (A τ * W y) := by
      intro x hx
      have hG : F τ hτ =ᶠ[𝓝 x] morseChainPhysicalModelLog G (A τ) side i := by
        cases rightBoundary
        · exact (P τ hτ).left_germs x hx
        · exact (P τ hτ).right_germs x hx
      exact hG.trans (Filter.Eventually.of_forall fun y =>
        morseChainPhysicalModelLog_amplitude G (A τ) side i y)
    have hs : IsPreconnected s := by cases rightBoundary <;> exact isPreconnected_Icc
    have hx₀ : x₀ ∈ s := by
      cases rightBoundary
      · exact ⟨le_rfl, le_add_of_nonneg_right hh.le⟩
      · exact ⟨sub_le_self _ hh.le, le_rfl⟩
    have hW₀ : W x₀ ≠ 0 := by
      have heq : morseChainProfileJoinShape T side k
          (P morseUnitHeights morseUnitHeights_admissible).leftLog
          (P morseUnitHeights morseUnitHeights_admissible).rightLog x₀ =
          A morseUnitHeights * W x₀ := by
        have hE : morseChainProfileJoinShape T side k
            (P morseUnitHeights morseUnitHeights_admissible).leftLog
            (P morseUnitHeights morseUnitHeights_admissible).rightLog x₀ =
            morseChainPhysicalModelHeight G (A morseUnitHeights) side i x₀ := by
          cases rightBoundary
          · exact (P morseUnitHeights morseUnitHeights_admissible).left_height.eq_of_nhds
          · exact (P morseUnitHeights morseUnitHeights_admissible).right_height.eq_of_nhds
        exact hE.trans (morseChainPhysicalModelHeight_amplitude G _ side i x₀)
      intro hz
      have hp := (P morseUnitHeights morseUnitHeights_admissible).positive x₀
      rw [heq, hz, mul_zero] at hp
      exact (lt_irrefl (0 : ℝ)) hp
    have hdouble : A (morseDoubleInitialHeight T) = 2 * A morseUnitHeights :=
      morseChainAmplitude_doubleInitial T (Nat.le_add_right _ _)
    have hlog : log (A (morseDoubleInitialHeight T)) - log (A morseUnitHeights) ≠ 0 := by
      rw [hdouble, log_mul (by norm_num : (2 : ℝ) ≠ 0) (hA _ morseUnitHeights_admissible).ne']
      have h₂ : 0 < log (2 : ℝ) := log_pos (by norm_num)
      linarith only [h₂]
    have hne := eventually_ne_zero_of_two_log_germs hs
      (hA _ morseUnitHeights_admissible) (hA _ (morseDoubleInitialHeight_admissible T)) hlog
      (hF _ morseUnitHeights_admissible) (hF _ (morseDoubleInitialHeight_admissible T))
      (hg _ morseUnitHeights_admissible) (hg _ (morseDoubleInitialHeight_admissible T)) hx₀ hW₀
    exact log_germ_amplitude_shift (hA σ hσ) (hA _ morseUnitHeights_admissible)
      (hg σ hσ) (hg _ morseUnitHeights_admissible) hne
  exact ⟨hshift false, hshift true⟩

/-- Explicit logarithmic parameter dependence of the existing chosen join. -/
theorem morseChainChosenJoinProfile_eq_log_ratios {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (σ : ℕ → ℝ)
    (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) (side : Bool) (k : ℕ) {x : ℝ}
    (hx : x ∈ Icc (T.joinLeft side (T.index + k)) (T.joinRight side (T.index + k))) :
    morseChainChosenJoinProfile G σ hσ side k x =
      exp (log (morseChainChosenJoinProfile G morseUnitHeights
          morseUnitHeights_admissible side k x) +
        morseChainHeightLogRatio T σ (T.index + morseChainJoinDeparture side k) +
        (morseChainHeightLogRatio T σ (T.index + morseChainJoinArrival side k) -
          morseChainHeightLogRatio T σ (T.index + morseChainJoinDeparture side k)) *
          morseJoinHeightCoordinate (T.joinLeft side (T.index + k))
            (T.joinRight side (T.index + k)) (morseChainProfileJoinCutoff T side k)
            (morseChainProfileJoinCutoff T side k) x) := by
  let P₀ := morseChainChosenJoin G morseUnitHeights morseUnitHeights_admissible side k
  obtain ⟨hL, hR⟩ := morseChainChosenJoin_log_germs G σ hσ side k
  have hab := morseChainPhysicalJoin_order G side k
  have hh : 0 < morseChainProfileJoinCutoff T side k :=
    div_pos (sub_pos.mpr hab) (by norm_num)
  have he := morseJoinLog_add_const_of_germs hab.le hh hh P₀.left_smooth P₀.right_smooth hL hR hx
  unfold morseChainChosenJoinProfile morseChainProfileJoinShape morseJoinProfile
  rw [log_exp]
  exact congrArg exp he

theorem continuous_morseChainAmplitude (T : Statements.MorseChainData) (n : ℕ) :
    Continuous (fun σ : ℕ → ℝ => Statements.morseChainAmplitude T σ n) := by
  apply continuous_const.mul
  exact continuous_finsetProd _ (fun i _ => continuous_apply i)

theorem continuous_morseChainHeightLogRatio (T : Statements.MorseChainData) (n : ℕ) :
    Continuous (fun σ : Statements.HeightRatios => morseChainHeightLogRatio T σ.val n) := by
  apply Continuous.sub_const
  apply ((continuous_morseChainAmplitude T n).comp continuous_subtype_val).log
  intro σ
  exact (morseChainAmplitude_pos T σ.val σ.property n).ne'

/-- Product-topology continuity of the actual, choice-defined join height,
jointly in all admissible height ratios and its physical coordinate. -/
theorem continuousOn_morseChainChosenJoinProfile {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (k : ℕ) :
    ContinuousOn (fun z : Statements.HeightRatios × ℝ =>
      morseChainChosenJoinProfile G z.1.val z.1.property side k z.2)
      {z | z.2 ∈ Icc (T.joinLeft side (T.index + k)) (T.joinRight side (T.index + k))} := by
  let P₀ := morseChainChosenJoin G morseUnitHeights morseUnitHeights_admissible side k
  let a := T.joinLeft side (T.index + k)
  let b := T.joinRight side (T.index + k)
  let h := morseChainProfileJoinCutoff T side k
  let cL : Statements.HeightRatios → ℝ :=
    fun σ => morseChainHeightLogRatio T σ.val (T.index + morseChainJoinDeparture side k)
  let cR : Statements.HeightRatios → ℝ :=
    fun σ => morseChainHeightLogRatio T σ.val (T.index + morseChainJoinArrival side k)
  have hL : Continuous cL := continuous_morseChainHeightLogRatio T _
  have hR : Continuous cR := continuous_morseChainHeightLogRatio T _
  have hc : Continuous (fun z : Statements.HeightRatios × ℝ =>
      morseJoinProfile a b h h (fun y => P₀.leftLog y + cL z.1)
        (fun y => P₀.rightLog y + cR z.1) z.2) :=
    continuous_morseJoinProfile_add_const P₀.left_smooth P₀.right_smooth
      (hL.comp continuous_fst) (hR.comp continuous_fst) continuous_snd
  refine hc.continuousOn.congr ?_
  intro z hz
  obtain ⟨hgL, hgR⟩ := morseChainChosenJoin_log_germs G z.1.val z.1.property side k
  have hab := morseChainPhysicalJoin_order G side k
  have hh : 0 < morseChainProfileJoinCutoff T side k :=
    div_pos (sub_pos.mpr hab) (by norm_num)
  exact morseJoinProfile_eqOn_of_germs hab.le hh hh hgL hgR hz

end ContinuousFlexibility.Radial
