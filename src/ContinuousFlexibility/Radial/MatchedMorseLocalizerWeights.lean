import ContinuousFlexibility.Radial.MatchedMorseLocalizerPieces
import ContinuousFlexibility.Radial.MatchedMorsePieceWeights
import ContinuousFlexibility.Radial.MatchedMorseNearWeights
import ContinuousFlexibility.Radial.InnerPhysicalSourceBridge

/-!
# Uniform actual weight comparisons on the true localizers

The two original physical weight signs are compared with the canonical
old labels. The fixed initial seam index absorbs the finitely many
initial labels. Every later label meets only neighboring original
pieces. All constants are independent of the retained length and mode.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory ContinuousFlexibility.Statements

def matchedMorseLocalizerWeightConstant (N J : ℕ) : ℝ :=
  exp (2 * radialS N + 38 * radialQ (J + 1) + radialS (J + 1))

theorem matchedMorseLocalizerWeightConstant_ge_one (N J : ℕ) :
    1 ≤ matchedMorseLocalizerWeightConstant N J := by
  apply one_le_exp_iff.mpr
  have hN : 0 ≤ radialS N := by unfold radialS; positivity
  have hJ : 0 ≤ radialS (J + 1) := by unfold radialS; positivity
  have hQ := radialQ_nonneg (J + 1)
  nlinarith only [hN, hJ, hQ]

theorem matchedMorseLocalizerWeightConstant_ge_base (N J : ℕ) :
    exp (radialS N) ≤ matchedMorseLocalizerWeightConstant N J := by
  apply exp_le_exp.mpr
  have hN : 0 ≤ radialS N := by unfold radialS; positivity
  have hJ : 0 ≤ radialS (J + 1) := by unfold radialS; positivity
  have hQ := radialQ_nonneg (J + 1)
  nlinarith only [hN, hJ, hQ]

section ActualChain

variable {T : MorseChainData} {σ₀ : ℕ → ℝ} {old : ReferenceData} {cost : ℕ → ℝ}
  (h : MorseChainRealization T σ₀ old cost) (κ : Bool → ℝ) (hκ : ∀ side, 0 < κ side)
  {N K : ℕ} (hN : T.index ≤ N) (hlarge : 4096 ≤ N) {center : Fin 2 → ℝ}
  (hc : center 0 < center 1)
  (hcl : κ false * innerMorseChainCut T false N 1 < center 0)
  (hcr : center 1 < κ true * innerMorseChainCut T true N 0)
  (D : ReferenceData) (hD : RadialProfileGeometry D) (hK : 0 < K)
  (hLcore : scaledMorseInnerOuterPoint T κ N K false ∈ radialCore D)
  (hRcore : scaledMorseInnerOuterPoint T κ N K true ∈ radialCore D)
  (e : ℝ ≃o ℝ)
  (he : ∀ side x, (if side then morseChainSeam T true N ≤ x
    else x ≤ morseChainSeam T false N) → e.symm x = κ side * x)
  (hχ : ∀ m x, D.localizer m x = old.localizer m (e x))
  {J : ℕ} (hJ : N ≤ J)
  (hwindow : ∀ m, old.cellIndex m ≤ N → ∀ y, old.localizer m y ≠ 0 →
    y ∈ Icc (morseChainSeam T false J) (morseChainSeam T true J))

local notation "G" => scaledMorseInnerChainGeometry h κ hκ hN hc hcl hcr D hD hK hLcore hRcore
local notation "R" => matchedMorseLocalizerWeightConstant N J

include hlarge he hχ hJ hwindow

/-- The inverse output multiplier includes exactly the original loss
37. Its local cost is uniform in the same finite chain. -/
theorem matchedScaledMorse_localizer_weight_bounds
    (l r : Fin (2 * (2 * K + 1) + 1) → ℝ)
    {σ : ℝ} (hσ : |σ| ≤ 1) {m : ℕ}
    (p : Fin (2 * (2 * K + 1) + 1)) {x : ℝ}
    (hχx : D.localizer m x ≠ 0)
    (hx : x ∈ Ioo ((G).left p) ((G).right p)) :
    |(innerMorseInnerLoss N K G 37 x *
        (innerMorseInnerWeight N K 0 1 G l r x) ^ σ)⁻¹| ≤
        R * exp (41414 * radialQ (old.cellIndex m) - σ * radialS (old.cellIndex m)) ∧
      |(innerMorseInnerWeight N K 0 1 G l r x) ^ σ| ≤
        R * exp (41414 * radialQ (old.cellIndex m) + σ * radialS (old.cellIndex m)) := by
  have htransfer (τ : ℝ) (hτ : |τ| ≤ 1) :
      exp (radialS N) * exp (38 * radialQ (innerMorseInnerPieceIndex N K p) +
        τ * radialS (innerMorseInnerPieceIndex N K p)) ≤
      R * exp (41414 * radialQ (old.cellIndex m) + τ * radialS (old.cellIndex m)) := by
    by_cases hm : N < old.cellIndex m
    · have hp := matchedScaledMorse_localizer_piece_index h κ hκ hN hc hcl hcr
        D hD hK hLcore hRcore e he hχ hm p hχx hx
      have hn : 2 ≤ old.cellIndex m := by omega
      have hh := matchedMorse_piece_exp_near hn hp.1 hp.2
        (by norm_num : (0 : ℝ) ≤ 38) hτ
      norm_num only [show (1089 : ℝ) * 38 + 32 = 41414 by norm_num] at hh
      exact mul_le_mul (matchedMorseLocalizerWeightConstant_ge_base N J) hh
        (exp_pos _).le (zero_le_one.trans (matchedMorseLocalizerWeightConstant_ge_one N J))
    · have hm₀ : old.cellIndex m ≤ N := le_of_not_gt hm
      have hwin : ∀ y, D.localizer m y ≠ 0 →
          e y ∈ Icc (morseChainSeam T false J) (morseChainSeam T true J) := by
        intro y hy
        apply hwindow m hm₀ (e y)
        simpa only [hχ m y] using hy
      have hp := matchedScaledMorse_initial_localizer_piece_index h κ hκ hN hc hcl hcr
        D hD hK hLcore hRcore e he hχ hJ hwin p hχx hx
      have hh := matchedMorse_piece_exp_initial (a := 41414) (b := 38)
        hm₀ hp (by norm_num) (by norm_num) hτ
      have heq : exp (radialS N) *
          exp (38 * radialQ (J + 1) + radialS (J + 1) + radialS N) = R := by
        rw [← exp_add]
        unfold matchedMorseLocalizerWeightConstant
        congr 1
        ring
      calc
        _ ≤ exp (radialS N) *
            (exp (38 * radialQ (J + 1) + radialS (J + 1) + radialS N) *
              exp (41414 * radialQ (old.cellIndex m) + τ * radialS (old.cellIndex m))) :=
          mul_le_mul_of_nonneg_left hh (exp_pos _).le
        _ = _ := by rw [← mul_assoc, heq]
  have hp := matchedMorse_actual_piece_exp_bounds N K hK hlarge G l r hσ p hx
  have hn := htransfer (-σ) (by simpa only [abs_neg] using hσ)
  have hn' :
      exp (radialS N) * exp (38 * radialQ (innerMorseInnerPieceIndex N K p) -
        σ * radialS (innerMorseInnerPieceIndex N K p)) ≤
      R * exp (41414 * radialQ (old.cellIndex m) - σ * radialS (old.cellIndex m)) := by
    simpa only [neg_mul, sub_eq_add_neg] using hn
  exact ⟨hp.2.trans hn', hp.1.trans (htransfer σ hσ)⟩

/-- The finitely many actual cuts are null for the original physical
Hilbert measure, so the piecewise bound holds on the whole inner region. -/
theorem matchedScaledMorse_localizer_weight_ae
    (hAcc : IsAccumulatingProfile D)
    (l r : Fin (2 * (2 * K + 1) + 1) → ℝ)
    {σ : ℝ} (hσ : |σ| ≤ 1) (m : ℕ) :
    ∀ᵐ x ∂radialHilbertMeasure D, D.localizer m x ≠ 0 →
      x ∈ Ioo ((G).left 0) ((G).right (Fin.last (2 * (2 * K + 1)))) →
      |(innerMorseInnerLoss N K G 37 x *
          (innerMorseInnerWeight N K 0 1 G l r x) ^ σ)⁻¹| ≤
          R * exp (41414 * radialQ (old.cellIndex m) - σ * radialS (old.cellIndex m)) ∧
        |(innerMorseInnerWeight N K 0 1 G l r x) ^ σ| ≤
          R * exp (41414 * radialQ (old.cellIndex m) + σ * radialS (old.cellIndex m)) := by
  filter_upwards [innerRadialChainRegion_ae hAcc G] with x hregion hχx hx
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hregion.mpr hx)
  exact matchedScaledMorse_localizer_weight_bounds h κ hκ hN hlarge hc hcl hcr
    D hD hK hLcore hRcore e he hχ hJ hwindow l r hσ p hχx hp

end ActualChain

end ContinuousFlexibility.Radial
