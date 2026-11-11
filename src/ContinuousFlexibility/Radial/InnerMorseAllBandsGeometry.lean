import ContinuousFlexibility.Radial.InnerMorseInnerCoercivity

/-!
# Actual inner geometry including the first frequency band

At K=0 the central cut model lies between two raw middle/head boundary
points. For K>0 the already constructed Morse-tail endpoints are used.
One positive gap constant is chosen for all K, including zero. No join
with index N-1 occurs in the first-band construction.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements

/-- A physical tail slot determines both the side and the retained-cell
position, including the empty tail of the first band. -/
theorem innerMorseInnerTailSlot_injective (K : ℕ) :
    Function.Injective (fun p : Bool × Fin K => innerMorseInnerTailSlot K p.1 p.2) := by
  rintro ⟨side, p⟩ ⟨side', q⟩ he
  change innerMorseInnerTailSlot K side p = innerMorseInnerTailSlot K side' q at he
  have hv := congrArg Fin.val he
  cases side <;> cases side'
  · change p.val = q.val at hv
    exact Prod.ext rfl (Fin.ext hv)
  · change p.val = K + 1 + q.val at hv
    omega
  · change K + 1 + p.val = q.val at hv
    omega
  · change K + 1 + p.val = K + 1 + q.val at hv
    have hpq : p.val = q.val := Nat.add_left_cancel hv
    exact Prod.ext rfl (Fin.ext hpq)

/-- The actual finite model array consists exactly of the central model
and the two tail arrays. No tail element exists when K is zero. -/
theorem innerMorseInnerModel_cases (K : ℕ) (p : Fin (2 * K + 1)) :
    p = innerMorseInnerCenter K ∨
      ∃ (side : Bool) (q : Fin K), p = innerMorseInnerTailSlot K side q := by
  by_cases hp : p.val = K
  · exact Or.inl (Fin.ext hp)
  · right
    by_cases hl : p.val < K
    · refine ⟨false, ⟨p.val, hl⟩, ?_⟩
      apply Fin.ext
      simp only [innerMorseInnerTailSlot, Bool.false_eq_true, ite_false]
    · have hq : p.val - K - 1 < K := by omega
      refine ⟨true, ⟨p.val - K - 1, hq⟩, ?_⟩
      apply Fin.ext
      simp only [innerMorseInnerTailSlot, ite_true]
      omega

section FirstBand

variable (D : ReferenceData) (hD : RadialProfileGeometry D) (center : Fin 2 → ℝ)
  (L R : ℝ) (hL : L ∈ radialCore D) (hR : R ∈ radialCore D)
  (hleft : L < center 0) (hc : center 0 < center 1) (hright : center 1 < R)

theorem innerCentralOnlyChainGeometry_gap_left (g : Fin 2) :
    (innerCentralOnlyChainGeometry D hD center L R hL hR hleft hc hright).left
      (innerModelChainGap g) = if 0 < g.val then center 1 else L := by
  change innerModelChainCuts (fun _ : Fin 1 => center) L R
    (innerModelChainGap g).castSucc = if 0 < g.val then center 1 else L
  have hg := innerModelChainCuts_gap_left (fun _ : Fin 1 => center) L R g
  by_cases hp : 0 < g.val <;>
    simpa only [hp, dite_true, dite_false, ite_true, ite_false] using hg

theorem innerCentralOnlyChainGeometry_gap_right (g : Fin 2) :
    (innerCentralOnlyChainGeometry D hD center L R hL hR hleft hc hright).right
      (innerModelChainGap g) = if g.val < 1 then center 0 else R := by
  change innerModelChainCuts (fun _ : Fin 1 => center) L R
    (innerModelChainGap g).succ = if g.val < 1 then center 0 else R
  have hg := innerModelChainCuts_gap_right (fun _ : Fin 1 => center) L R g
  by_cases hp : g.val < 1 <;>
    simpa only [hp, dite_true, dite_false, ite_true, ite_false] using hg

/-- The first-band constant follows from the two actual compact positive
head/connector intervals, before any frequency is selected. -/
theorem innerCentralOnlyChainGeometry_exists_gap_slope
    (hpositiveLeft : ∀ r ∈ Icc L (center 0), 0 < deriv D.w r)
    (hpositiveRight : ∀ r ∈ Icc (center 1) R, 0 < deriv D.w r) :
    ∃ c : ℝ, 0 < c ∧ ∀ g : Fin 2,
      ∀ r ∈ Icc
        ((innerCentralOnlyChainGeometry D hD center L R hL hR hleft hc hright).left
          (innerModelChainGap g))
        ((innerCentralOnlyChainGeometry D hD center L R hL hR hleft hc hright).right
          (innerModelChainGap g)), c ≤ r * deriv D.w r / D.w r := by
  have hcore : Icc L R ⊆ radialCore D := fun r hr =>
    ⟨hL.1.trans_le hr.1, hr.2.trans_lt hR.2⟩
  have hc1 : center 1 ∈ radialCore D := hcore ⟨(hleft.trans hc).le, hright.le⟩
  obtain ⟨a, ha, habound⟩ := innerPositiveGap_exists_slope (hD.1.trans hL.1) hD.2.2.1.1
    (fun r hr => hD.2.2.2.2.1 r (hcore ⟨hr.1, hr.2.trans (hc.trans hright).le⟩)) hpositiveLeft
  obtain ⟨b, hb, hbbound⟩ := innerPositiveGap_exists_slope (hD.1.trans hc1.1) hD.2.2.1.1
    (fun r hr => hD.2.2.2.2.1 r (hcore ⟨(hleft.trans hc).le.trans hr.1, hr.2⟩)) hpositiveRight
  refine ⟨min a b, lt_min ha hb, ?_⟩
  intro g r hr
  rw [innerCentralOnlyChainGeometry_gap_left, innerCentralOnlyChainGeometry_gap_right] at hr
  rcases (show g = 0 ∨ g = 1 by omega) with rfl | rfl
  · norm_num only [Fin.val_zero, ite_true, ite_false] at hr
    exact (min_le_left a b).trans (habound r hr)
  · norm_num only [Fin.val_one, ite_true, ite_false] at hr
    exact (min_le_right a b).trans (hbbound r hr)

end FirstBand

section AllBands

variable {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
  (h : MorseChainRealization T σ D C) {N : ℕ} (hN : T.index ≤ N)
  (center : Fin 2 → ℝ) (hc : center 0 < center 1)
  (hcl : innerMorseChainCut T false N 1 < center 0)
  (hcr : center 1 < innerMorseChainCut T true N 0)
  (L R : ℝ) (hL : L ∈ radialCore D) (hR : R ∈ radialCore D)
  (hleft : L < center 0) (hright : center 1 < R)

def innerMorseAllBandsChainGeometry : (K : ℕ) → InnerRadialChainGeometry D (2 * (2 * K + 1))
  | 0 => innerCentralOnlyChainGeometry D h.geometry center L R hL hR hleft hc hright
  | K + 1 => innerMorseInnerChainGeometry h hN (Nat.succ_pos K) center hc hcl hcr

theorem innerMorseAllBandsChainGeometry_zero :
    innerMorseAllBandsChainGeometry h hN center hc hcl hcr L R hL hR hleft hright 0 =
      innerCentralOnlyChainGeometry D h.geometry center L R hL hR hleft hc hright := rfl

theorem innerMorseAllBandsChainGeometry_of_pos {K : ℕ} (hK : 0 < K) :
    innerMorseAllBandsChainGeometry h hN center hc hcl hcr L R hL hR hleft hright K =
      innerMorseInnerChainGeometry h hN hK center hc hcl hcr := by
  cases K with
  | zero => omega
  | succ K => rfl

theorem innerMorseAllBandsChainGeometry_center (K : ℕ) :
    (innerMorseAllBandsChainGeometry h hN center hc hcl hcr L R hL hR hleft hright K).left
        (innerModelChainPiece (innerMorseInnerCenter K)) = center 0 ∧
      (innerMorseAllBandsChainGeometry h hN center hc hcl hcr L R hL hR hleft hright K).right
        (innerModelChainPiece (innerMorseInnerCenter K)) = center 1 := by
  cases K with
  | zero =>
    exact ⟨innerModelChainCuts_model_left (fun _ : Fin 1 => center) L R 0,
      innerModelChainCuts_model_right (fun _ : Fin 1 => center) L R 0⟩
  | succ K => exact innerMorseInnerChainGeometry_center h hN (Nat.succ_pos K) center hc hcl hcr

theorem innerMorseAllBandsChainGeometry_tail (K : ℕ) (side : Bool) (p : Fin K) :
    (innerMorseAllBandsChainGeometry h hN center hc hcl hcr L R hL hR hleft hright K).left
        (innerModelChainPiece (innerMorseInnerTailSlot K side p)) =
          innerMorseChainCut T side (innerMorseInnerTailIndex N K side p) 0 ∧
      (innerMorseAllBandsChainGeometry h hN center hc hcl hcr L R hL hR hleft hright K).right
        (innerModelChainPiece (innerMorseInnerTailSlot K side p)) =
          innerMorseChainCut T side (innerMorseInnerTailIndex N K side p) 1 := by
  cases K with
  | zero => exact Fin.elim0 p
  | succ K => exact innerMorseInnerChainGeometry_tail h hN (Nat.succ_pos K) center hc hcl hcr side p

/-- One geometric constant works for the first band and every later
band. All positive-region inputs are raw derivative signs on fixed
central/head intervals; the entire growing tail is derived from R05a. -/
theorem innerMorseAllBandsChainGeometry_exists_gap_slope (hindex : 10 ≤ T.index)
    (hpositiveMiddle : ∀ side r, r ∈ Icc (innerMorseMiddleGapLeft T N center side)
      (innerMorseMiddleGapRight T N center side) → 0 < deriv D.w r)
    (hpositiveLeft : ∀ r ∈ Icc L (center 0), 0 < deriv D.w r)
    (hpositiveRight : ∀ r ∈ Icc (center 1) R, 0 < deriv D.w r) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : ℕ, ∀ g : Fin (2 * K + 2),
      ∀ r ∈ Icc
        ((innerMorseAllBandsChainGeometry h hN center hc hcl hcr L R hL hR hleft hright K).left
          (innerModelChainGap g))
        ((innerMorseAllBandsChainGeometry h hN center hc hcl hcr L R hL hR hleft hright K).right
          (innerModelChainGap g)), c ≤ r * deriv D.w r / D.w r := by
  obtain ⟨a, ha, habound⟩ := innerMorseInnerChain_exists_uniform_gap_slope
    h hindex hN center hc hcl hcr hpositiveMiddle
  obtain ⟨b, hb, hbbound⟩ := innerCentralOnlyChainGeometry_exists_gap_slope D h.geometry
    center L R hL hR hleft hc hright hpositiveLeft hpositiveRight
  refine ⟨min a b, lt_min ha hb, ?_⟩
  intro K g r hr
  cases K with
  | zero => exact (min_le_right a b).trans (hbbound g r hr)
  | succ K => exact (min_le_left a b).trans (habound (K + 1) (Nat.succ_pos K) g r hr)

end AllBands

end ContinuousFlexibility.Radial
