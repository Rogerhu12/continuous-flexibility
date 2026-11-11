import ContinuousFlexibility.Radial.ScaledMorseInnerGaps
import ContinuousFlexibility.Radial.RetainedMorseGapSlope
import ContinuousFlexibility.Radial.ReferenceFirstGapSlope

/-!
# The actual finite inner geometry of the retained pair

The central buffer is fixed before the retained pair. Every tail cut and
outer endpoint is the physical dilation of the old selected cell. Their
membership in the new core follows from the retained profile identity.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements

def retainedMorseCenterCuts (T : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then centralRadius (-T) else centralRadius T

namespace SeedRetainedPair

variable {S : SelectedTailData} {K : SeedCentralCutoff} {q length T : ℝ}
  (P : SeedRetainedPair S K q length) {Γ : ConnectedReferenceGeometry}
  (hD : RadialProfileGeometry Γ.reference) (hw : Γ.reference.w = P.pair.profile)
  (hS : IsSelectedTail S) (G₀ : MorseChainGeometryWitness S.chain)
  (hfirst : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
  (hq : 0 < q) (hT : 0 < T)
  (hleft : Γ.centralLeft = exp K.left) (hright : Γ.centralRight = exp K.right)
  (hTL : Γ.centralLeft < centralRadius (-T)) (hTR : centralRadius T < Γ.centralRight)

include hq hleft hright in
theorem retained_first_cuts_outside_central :
    P.sideRadius false * S.cut false S.chain.index < Γ.centralLeft ∧
      Γ.centralRight < P.sideRadius true * S.cut true S.chain.index := by
  constructor
  · rw [hleft]
    exact P.pair.left_entry.trans (exp_lt_exp.mpr (by linarith only [hq]))
  · rw [hright]
    exact (exp_lt_exp.mpr (by linarith only [hq])).trans P.pair.right_entry

include hD hw hS G₀ hfirst in
theorem retained_morse_outer_mem_core (k : ℕ) (side : Bool) :
    scaledMorseInnerOuterPoint S.chain P.sideRadius S.chain.index k side ∈ radialCore Γ.reference := by
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hm : S.chain.index ≤ S.chain.index + (k - 1) := Nat.le_add_right _ _
  obtain ⟨_, _, _, hl, hr, _, _⟩ := hreal.retained_data side _ hm
  apply P.reference_morse_cell_mem_core hw hS G₀ hfirst hD side hm
  cases side
  · exact left_mem_Icc.mpr (hl.trans hr).le
  · exact right_mem_Icc.mpr (hl.trans hr).le

include hS G₀ hfirst hq hT hleft hright hTL hTR in
theorem retained_morse_center_order :
    retainedMorseCenterCuts T 0 < retainedMorseCenterCuts T 1 ∧
      P.sideRadius false * innerMorseChainCut S.chain false S.chain.index 1 <
        retainedMorseCenterCuts T 0 ∧
      retainedMorseCenterCuts T 1 <
        P.sideRadius true * innerMorseChainCut S.chain true S.chain.index 0 := by
  have hcuts := P.retained_first_cuts_outside_central hq hleft hright
  have hl := (selected_morseCut_retained hS G₀ hfirst false le_rfl 1).2
  have hr := (selected_morseCut_retained hS G₀ hfirst true le_rfl 0).2
  change centralRadius (-T) < centralRadius T ∧
    P.sideRadius false * innerMorseChainCut S.chain false S.chain.index 1 < centralRadius (-T) ∧
    centralRadius T < P.sideRadius true * innerMorseChainCut S.chain true S.chain.index 0
  exact ⟨strictMono_centralRadius (by linarith only [hT]),
    (mul_le_mul_of_nonneg_left hl (P.sideRadius_pos false).le).trans_lt
      (hcuts.1.trans hTL),
    (hTR.trans hcuts.2).trans_le
      (mul_le_mul_of_nonneg_left hr (P.sideRadius_pos true).le)⟩

def retainedMorseInnerGeometry (k : ℕ) (hk : 0 < k) :
    InnerRadialChainGeometry Γ.reference (2 * (2 * k + 1)) :=
  scaledMorseInnerChainGeometry (hS.2.2.2.1 S.sigma hS.2.2.1).1
    P.sideRadius P.sideRadius_pos (le_refl S.chain.index)
    (P.retained_morse_center_order hS G₀ hfirst hq hT hleft hright hTL hTR).1
    (P.retained_morse_center_order hS G₀ hfirst hq hT hleft hright hTL hTR).2.1
    (P.retained_morse_center_order hS G₀ hfirst hq hT hleft hright hTL hTR).2.2
    Γ.reference hD hk (P.retained_morse_outer_mem_core hD hw hS G₀ hfirst k false)
    (P.retained_morse_outer_mem_core hD hw hS G₀ hfirst k true)

variable (k : ℕ) (hk : 0 < k)
local notation "H" => P.retainedMorseInnerGeometry hD hw hS G₀ hfirst hq hT
  hleft hright hTL hTR k hk

theorem retainedMorseInnerGeometry_center :
    (H).left (innerModelChainPiece (innerMorseInnerCenter k)) = centralRadius (-T) ∧
      (H).right (innerModelChainPiece (innerMorseInnerCenter k)) = centralRadius T := by
  dsimp only [retainedMorseInnerGeometry]
  rw [scaledMorseInnerChainGeometry_left, scaledMorseInnerChainGeometry_right,
    scaledMorseInnerModelCuts_center, scaledMorseInnerModelCuts_center]
  norm_num [retainedMorseCenterCuts]

theorem retainedMorseInnerGeometry_tail (side : Bool) (p : Fin k) :
    (H).left (innerModelChainPiece (innerMorseInnerTailSlot k side p)) =
      P.sideRadius side * innerMorseChainCut S.chain side
        (innerMorseInnerTailIndex S.chain.index k side p) 0 ∧
      (H).right (innerModelChainPiece (innerMorseInnerTailSlot k side p)) =
      P.sideRadius side * innerMorseChainCut S.chain side
        (innerMorseInnerTailIndex S.chain.index k side p) 1 := by
  dsimp only [retainedMorseInnerGeometry]
  exact scaledMorseInnerChainGeometry_tail (hS.2.2.2.1 S.sigma hS.2.2.1).1
    P.sideRadius P.sideRadius_pos (le_refl S.chain.index)
    (P.retained_morse_center_order hS G₀ hfirst hq hT hleft hright hTL hTR).1
    (P.retained_morse_center_order hS G₀ hfirst hq hT hleft hright hTL hTR).2.1
    (P.retained_morse_center_order hS G₀ hfirst hq hT hleft hright hTL hTR).2.2
    Γ.reference hD hk (P.retained_morse_outer_mem_core hD hw hS G₀ hfirst k false)
    (P.retained_morse_outer_mem_core hD hw hS G₀ hfirst k true) side p

theorem retainedMorseInnerGeometry_terminal (side : Bool) :
    (H).left (innerModelChainGap (innerMorseTerminalGapSlot k side)) =
      P.sideRadius side * S.chain.radius side (S.chain.index + (k - 1))
        (innerMorseOuterCapStart (morseChainA S.chain (S.chain.index + (k - 1)))
          (morseChainB S.chain (S.chain.index + (k - 1))) side) ∧
      (H).right (innerModelChainGap (innerMorseTerminalGapSlot k side)) =
      P.sideRadius side * S.chain.radius side (S.chain.index + (k - 1))
        (innerMorseOuterCapEnd (morseChainA S.chain (S.chain.index + (k - 1)))
          (morseChainB S.chain (S.chain.index + (k - 1))) side) := by
  dsimp only [retainedMorseInnerGeometry]
  exact scaledMorseInnerChainGeometry_terminal (hS.2.2.2.1 S.sigma hS.2.2.1).1
    P.sideRadius P.sideRadius_pos (le_refl S.chain.index)
    (P.retained_morse_center_order hS G₀ hfirst hq hT hleft hright hTL hTR).1
    (P.retained_morse_center_order hS G₀ hfirst hq hT hleft hright hTL hTR).2.1
    (P.retained_morse_center_order hS G₀ hfirst hq hT hleft hright hTL hTR).2.2
    Γ.reference hD hk (P.retained_morse_outer_mem_core hD hw hS G₀ hfirst k false)
    (P.retained_morse_outer_mem_core hD hw hS G₀ hfirst k true) side

theorem retainedMorseInnerGeometry_middle (side : Bool) :
    (H).left (innerModelChainGap (innerMorseMiddleGapSlot k side)) =
      scaledMorseMiddleGapLeft S.chain P.sideRadius S.chain.index
        (retainedMorseCenterCuts T) side ∧
      (H).right (innerModelChainGap (innerMorseMiddleGapSlot k side)) =
      scaledMorseMiddleGapRight S.chain P.sideRadius S.chain.index
        (retainedMorseCenterCuts T) side := by
  dsimp only [retainedMorseInnerGeometry]
  exact scaledMorseInnerChainGeometry_middle (hS.2.2.2.1 S.sigma hS.2.2.1).1
    P.sideRadius P.sideRadius_pos (le_refl S.chain.index)
    (P.retained_morse_center_order hS G₀ hfirst hq hT hleft hright hTL hTR).1
    (P.retained_morse_center_order hS G₀ hfirst hq hT hleft hright hTL hTR).2.1
    (P.retained_morse_center_order hS G₀ hfirst hq hT hleft hright hTL hTR).2.2
    Γ.reference hD hk (P.retained_morse_outer_mem_core hD hw hS G₀ hfirst k false)
    (P.retained_morse_outer_mem_core hD hw hS G₀ hfirst k true) side

theorem retainedMorseInnerGeometry_tailGap (side : Bool) (p : Fin (k - 1)) :
    (H).left (innerModelChainGap (innerMorseTailGapSlot k side p)) =
      P.sideRadius side * innerMorseTailGapLeft S.chain side
        (innerMorseTailGapCell S.chain.index k side p) ∧
      (H).right (innerModelChainGap (innerMorseTailGapSlot k side p)) =
      P.sideRadius side * innerMorseTailGapRight S.chain side
        (innerMorseTailGapCell S.chain.index k side p) := by
  dsimp only [retainedMorseInnerGeometry]
  exact scaledMorseInnerChainGeometry_tailGap (hS.2.2.2.1 S.sigma hS.2.2.1).1
    P.sideRadius P.sideRadius_pos (le_refl S.chain.index)
    (P.retained_morse_center_order hS G₀ hfirst hq hT hleft hright hTL hTR).1
    (P.retained_morse_center_order hS G₀ hfirst hq hT hleft hright hTL hTR).2.1
    (P.retained_morse_center_order hS G₀ hfirst hq hT hleft hright hTL hTR).2.2
    Γ.reference hD hk (P.retained_morse_outer_mem_core hD hw hS G₀ hfirst k false)
    (P.retained_morse_outer_mem_core hD hw hS G₀ hfirst k true) side p

theorem retainedMorseInnerGeometry_outer
    (hjoin : ∀ side n, S.chain.index < n →
      S.joinInner side n = r07PreviousCellJoin S.chain side (n - 1)) :
    (H).left 0 = P.sideRadius false * S.joinInner false (S.chain.index + k) ∧
      (H).right (Fin.last (2 * (2 * k + 1))) =
        P.sideRadius true * S.joinInner true (S.chain.index + k) := by
  have he : S.chain.index + k - 1 = S.chain.index + (k - 1) := by omega
  have hout (side : Bool) :
      scaledMorseInnerOuterPoint S.chain P.sideRadius S.chain.index k side =
        P.sideRadius side * S.joinInner side (S.chain.index + k) := by
    rw [hjoin side _ (by omega), he]
    rfl
  constructor
  · change innerModelChainCuts
      (scaledMorseInnerModelCuts S.chain P.sideRadius S.chain.index k (retainedMorseCenterCuts T))
      (scaledMorseInnerOuterPoint S.chain P.sideRadius S.chain.index k false)
      (scaledMorseInnerOuterPoint S.chain P.sideRadius S.chain.index k true) 0 = _
    rw [innerModelChainCuts_first]
    exact hout false
  · have heq : (Fin.last (2 * (2 * k + 1))).succ =
        Fin.last (2 * (2 * k + 1) + 1) := Fin.succ_last _
    change innerModelChainCuts
      (scaledMorseInnerModelCuts S.chain P.sideRadius S.chain.index k (retainedMorseCenterCuts T))
      (scaledMorseInnerOuterPoint S.chain P.sideRadius S.chain.index k false)
      (scaledMorseInnerOuterPoint S.chain P.sideRadius S.chain.index k true)
      (Fin.last (2 * (2 * k + 1))).succ = _
    rw [heq, innerModelChainCuts_last]
    exact hout true

end SeedRetainedPair

end ContinuousFlexibility.Radial
