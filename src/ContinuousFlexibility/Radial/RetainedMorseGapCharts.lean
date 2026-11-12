import ContinuousFlexibility.Radial.RetainedMorseMiddleGap
import ContinuousFlexibility.Radial.InnerRadialActualPieces

/-!
# Genuine positive-gap columns on the retained physical chain

Strict derivative positivity is established from the actual three gap
types. Compactness chooses an auxiliary slope only to construct the
same physical Dirichlet and Poisson maps. Their final norm estimates
are supplied by the slope-independent Hardy inequalities.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements
open scoped ContDiff

def innerRadialGapChartOfPositiveDerivative (D : ReferenceData)
    (hD : RadialProfileGeometry D) {n : ℕ} (H : InnerRadialChainGeometry D n)
    (j : ℝ) (central piece : Fin (n + 1)) (haway : piece ≠ central) (hj : 0 < j)
    (hpositive : ∀ r ∈ Icc (H.left piece) (H.right piece), 0 < deriv D.w r) :
    InnerRadialGapChart D H j central piece :=
  Classical.choice (by
    have hl := radialCore_mem_of_profile_pos hD
      (H.weight_pos piece _ (left_mem_Icc.mpr (H.left_lt_right piece).le))
    have hr := radialCore_mem_of_profile_pos hD
      (H.weight_pos piece _ (right_mem_Icc.mpr (H.left_lt_right piece).le))
    have hlower : D.a < H.left piece := hl.1
    have hupper : H.right piece < D.b := hr.2
    have hapos : 0 < D.a := hD.1
    have hAmem : D.a < (D.a + H.left piece) / 2 := by
      linarith only [hlower]
    have hAl : (D.a + H.left piece) / 2 < H.left piece := by
      linarith only [hlower]
    have hhB : H.right piece < (H.right piece + D.b) / 2 := by
      linarith only [hupper]
    have hBmem : (H.right piece + D.b) / 2 < D.b := by
      linarith only [hupper]
    obtain ⟨s, hs, hslope⟩ := innerPositiveGap_exists_slope
      (H.left_pos piece) hD.2.2.1.1 (H.weight_pos piece) hpositive
    have hnonneg : ∀ r, 0 ≤ D.w r := by
      intro r
      by_cases ha : D.a < r
      · by_cases hb : r < D.b
        · exact (hD.2.2.2.2.1 r ⟨ha, hb⟩).le
        · exact (hD.2.2.1.2 r (Or.inr (le_of_not_gt hb))).ge
      · exact (hD.2.2.1.2 r (Or.inl (le_of_not_gt ha))).ge
    obtain ⟨p, hp, hb, heq⟩ := exists_innerGapPoissonColumns
      (A := (D.a + H.left piece) / 2) (l := H.left piece)
      (h := H.right piece) (B := (H.right piece + D.b) / 2)
      (hapos.trans hAmem) hAl (H.left_lt_right piece)
      hhB hD.2.2.1.1 hnonneg
      (fun r hr' => hD.2.2.2.2.1 r
        ⟨hAmem.trans hr'.1, hr'.2.trans hBmem⟩)
      (fun r hr' => hs.le.trans (hslope r hr')) j
    exact ⟨{
      away_center := haway
      frequency_pos := hj
      slope := s
      slope_pos := hs
      slope_lower := hslope
      columns := p
      columns_smooth := hp
      columns_boundary := hb
      columns_homogeneous := heq
    }⟩)

namespace SeedRetainedPair

variable {S : SelectedTailData} {K : SeedCentralCutoff} {q length T : ℝ}
  (P : SeedRetainedPair S K q length) {Γ : ConnectedReferenceGeometry}
  (hD : RadialProfileGeometry Γ.reference) (hw : Γ.reference.w = P.pair.profile)
  (hS : IsSelectedTail S) (G₀ : MorseChainGeometryWitness S.chain)
  (hfirst : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
  (hq : 0 < q) (hT : 0 < T)
  (hleft : Γ.centralLeft = exp K.left) (hright : Γ.centralRight = exp K.right)
  (hTL : Γ.centralLeft < centralRadius (-T)) (hTR : centralRadius T < Γ.centralRight)
  (k : ℕ) (hk : 0 < k)
  (hbridge : ∀ side r, r ∈ uIcc (S.cut side S.chain.index)
    (S.entry side S.chain.index) → 0 < deriv (S.family S.sigma).w r)
  (hmodel : EqOn Γ.reference.w (centralRadialProfile 1) (Ioo Γ.centralLeft Γ.centralRight))
  (hwindow : ∀ r, 0 < r → (r ≤ centralRadius (-T) ∨ centralRadius T ≤ r) →
    (3 / 4 : ℝ) ≤ r * deriv (centralRadialProfile 1) r / centralRadialProfile 1 r)

local notation "H" => P.retainedMorseInnerGeometry hD hw hS G₀ hfirst hq hT
  hleft hright hTL hTR k hk

include hbridge hmodel hwindow in
theorem retainedMorseGap_deriv_pos (g : Fin (2 * k + 2))
    {r : ℝ} (hr : r ∈ Icc ((H).left (innerModelChainGap g)) ((H).right (innerModelChainGap g))) :
    0 < deriv Γ.reference.w r := by
  have hrpos := ((H).left_pos (innerModelChainGap g)).trans_le hr.1
  have hwpos := (H).weight_pos (innerModelChainGap g) r hr
  rcases innerMorseInnerGap_cases hk g with ⟨side, rfl⟩ | ⟨side, rfl⟩ | ⟨side, p, rfl⟩
  · have he := P.retainedMorseInnerGeometry_terminal hD hw hS G₀ hfirst hq hT
      hleft hright hTL hTR k hk side
    rw [he.1, he.2] at hr
    exact retained_deriv_pos_of_logSlope hrpos hwpos innerMorseTailSlope_pos
      (P.reference_morse_outerCap_logSlope hw hS G₀ hfirst side
        (Nat.le_add_right _ _) side hr)
  · have he := P.retainedMorseInnerGeometry_middle hD hw hS G₀ hfirst hq hT
      hleft hright hTL hTR k hk side
    rw [he.1, he.2] at hr
    exact P.reference_morse_middle_deriv_pos hw hS G₀ hfirst hbridge
      hleft hright hT.le hTL hTR hmodel hwindow side hrpos hwpos hr
  · have he := P.retainedMorseInnerGeometry_tailGap hD hw hS G₀ hfirst hq hT
      hleft hright hTL hTR k hk side p
    rw [he.1, he.2] at hr
    have hm : S.chain.index ≤ innerMorseTailGapCell S.chain.index k side p := by
      cases side <;> simp only [innerMorseTailGapCell, Bool.false_eq_true, ite_false, ite_true] <;> omega
    exact retained_deriv_pos_of_logSlope hrpos hwpos innerMorseTailSlope_pos
      (P.reference_morse_tailGap_logSlope hw hS G₀ hfirst side hm hr)

def retainedMorseGapChart (j : ℝ) (hj : 0 < j) (g : Fin (2 * k + 2)) :
    InnerRadialGapChart Γ.reference H j (innerModelChainPiece (innerMorseInnerCenter k))
      (innerModelChainGap g) :=
  innerRadialGapChartOfPositiveDerivative Γ.reference hD H j
    (innerModelChainPiece (innerMorseInnerCenter k)) (innerModelChainGap g)
    (innerModelChainGap_ne_model g (innerMorseInnerCenter k)) hj
    (fun r hr => P.retainedMorseGap_deriv_pos hD hw hS G₀ hfirst hq hT
      hleft hright hTL hTR k hk hbridge hmodel hwindow g hr)

end SeedRetainedPair

end ContinuousFlexibility.Radial
