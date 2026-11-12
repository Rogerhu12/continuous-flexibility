import ContinuousFlexibility.Radial.MatchedMorseLocalizerWeights
import ContinuousFlexibility.Radial.RetainedMorseInnerGeometry

/-!
# Actual localizers in the original retained chain

The original retained geometry is definitionally the scaled chain used
by the physical window theorem. This wrapper keeps that object and
records the canonical old labels before the reference index floor.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory ContinuousFlexibility.Statements

namespace SeedRetainedPair

variable {S : SelectedTailData} {K₀ : SeedCentralCutoff} {headLength length T : ℝ}
  (P : SeedRetainedPair S K₀ headLength length) {Γ : ConnectedReferenceGeometry}
  (hD : RadialProfileGeometry Γ.reference) (hw : Γ.reference.w = P.pair.profile)
  (hS : IsSelectedTail S) (G₀ : MorseChainGeometryWitness S.chain)
  (hfirst : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
  (hhead : 0 < headLength) (hT : 0 < T)
  (hleft : Γ.centralLeft = exp K₀.left) (hright : Γ.centralRight = exp K₀.right)
  (hTL : Γ.centralLeft < centralRadius (-T)) (hTR : centralRadius T < Γ.centralRight)
  (k : ℕ) (hk : 0 < k)
  (hN : 4096 ≤ S.chain.index) (e : ℝ ≃o ℝ)
  (he : ∀ side x, (if side then morseChainSeam S.chain true S.chain.index ≤ x
    else x ≤ morseChainSeam S.chain false S.chain.index) →
      e.symm x = P.sideRadius side * x)
  (hχ : ∀ m x, Γ.reference.localizer m x = (S.family S.sigma).localizer m (e x))
  {J : ℕ} (hJ : S.chain.index ≤ J)
  (hwindow : ∀ m, (S.family S.sigma).cellIndex m ≤ S.chain.index →
    ∀ x, (S.family S.sigma).localizer m x ≠ 0 →
      x ∈ Icc (morseChainSeam S.chain false J) (morseChainSeam S.chain true J))

local notation "H" => P.retainedMorseInnerGeometry hD hw hS G₀ hfirst hhead hT
  hleft hright hTL hTR k hk

include hN he hχ hJ hwindow

theorem retainedMorse_localizer_weight_ae (hAcc : IsAccumulatingProfile Γ.reference)
    (l r : Fin (2 * (2 * k + 1) + 1) → ℝ) {σ : ℝ} (hσ : |σ| ≤ 1) (m : ℕ) :
    ∀ᵐ x ∂radialHilbertMeasure Γ.reference, Γ.reference.localizer m x ≠ 0 →
      x ∈ Ioo ((H).left 0) ((H).right (Fin.last (2 * (2 * k + 1)))) →
      |(innerMorseInnerLoss S.chain.index k H 37 x *
          (innerMorseInnerWeight S.chain.index k 0 1 H l r x) ^ σ)⁻¹| ≤
          matchedMorseLocalizerWeightConstant S.chain.index J *
            exp (41414 * radialQ ((S.family S.sigma).cellIndex m) -
              σ * radialS ((S.family S.sigma).cellIndex m)) ∧
        |(innerMorseInnerWeight S.chain.index k 0 1 H l r x) ^ σ| ≤
          matchedMorseLocalizerWeightConstant S.chain.index J *
            exp (41414 * radialQ ((S.family S.sigma).cellIndex m) +
              σ * radialS ((S.family S.sigma).cellIndex m)) := by
  have hc := P.retained_morse_center_order hS G₀ hfirst hhead hT
    hleft hright hTL hTR
  exact matchedScaledMorse_localizer_weight_ae (hS.2.2.2.1 S.sigma hS.2.2.1).1
    P.sideRadius P.sideRadius_pos le_rfl hN hc.1 hc.2.1 hc.2.2 Γ.reference hD hk
    (P.retained_morse_outer_mem_core hD hw hS G₀ hfirst k false)
    (P.retained_morse_outer_mem_core hD hw hS G₀ hfirst k true)
    e he hχ hJ hwindow hAcc l r hσ m

end SeedRetainedPair

end ContinuousFlexibility.Radial
