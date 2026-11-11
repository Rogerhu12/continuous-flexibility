import ContinuousFlexibility.Radial.InnerMorseInnerGaps

/-!
# One positive-gap constant for every finite inner truncation

The tail and terminal-cap constant comes from the original realized
Morse equations. Only the two fixed central connectors use compactness,
applied to their actual strictly positive derivative. The constant is
chosen before K and j, and is valid on every closed gap of the actual
finite chain.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem innerMorseMiddleGap_order {T : MorseChainData} {N : ℕ} {center : Fin 2 → ℝ}
    (hcl : innerMorseChainCut T false N 1 < center 0)
    (hcr : center 1 < innerMorseChainCut T true N 0) (side : Bool) :
    innerMorseMiddleGapLeft T N center side < innerMorseMiddleGapRight T N center side := by
  cases side with
  | false => simpa only [innerMorseMiddleGapLeft, innerMorseMiddleGapRight,
      Bool.false_eq_true, ite_false] using hcl
  | true => simpa only [innerMorseMiddleGapLeft, innerMorseMiddleGapRight, ite_true] using hcr

theorem innerMorseMiddleGap_core {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    {N : ℕ} (hN : T.index ≤ N) {center : Fin 2 → ℝ}
    (hc : center 0 < center 1)
    (hcl : innerMorseChainCut T false N 1 < center 0)
    (hcr : center 1 < innerMorseChainCut T true N 0) (side : Bool) :
    Icc (innerMorseMiddleGapLeft T N center side) (innerMorseMiddleGapRight T N center side) ⊆
      radialCore D := by
  have hl := (innerMorseChainCut_geometry h false hN).2.2.2 1
  have hr := (innerMorseChainCut_geometry h true hN).2.2.2 0
  intro r hrg
  cases side with
  | false =>
    simp only [innerMorseMiddleGapLeft, innerMorseMiddleGapRight,
      Bool.false_eq_true, ite_false] at hrg
    exact ⟨hl.1.trans_le hrg.1, (hrg.2.trans_lt (hc.trans hcr)).trans hr.2⟩
  | true =>
    simp only [innerMorseMiddleGapLeft, innerMorseMiddleGapRight, ite_true] at hrg
    exact ⟨(hl.1.trans (hcl.trans hc)).trans_le hrg.1, hrg.2.trans_lt hr.2⟩

theorem innerMorseMiddleGap_exists_slope {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    {N : ℕ} (hN : T.index ≤ N) {center : Fin 2 → ℝ}
    (hc : center 0 < center 1)
    (hcl : innerMorseChainCut T false N 1 < center 0)
    (hcr : center 1 < innerMorseChainCut T true N 0) (side : Bool)
    (hpositive : ∀ r ∈ Icc (innerMorseMiddleGapLeft T N center side)
      (innerMorseMiddleGapRight T N center side), 0 < deriv D.w r) :
    ∃ c : ℝ, 0 < c ∧ ∀ r ∈ Icc (innerMorseMiddleGapLeft T N center side)
      (innerMorseMiddleGapRight T N center side), c ≤ r * deriv D.w r / D.w r := by
  have hcore := innerMorseMiddleGap_core h hN hc hcl hcr side
  have hab := innerMorseMiddleGap_order hcl hcr side
  have ha := h.geometry.1.trans (hcore (left_mem_Icc.mpr hab.le)).1
  exact innerPositiveGap_exists_slope ha h.geometry.2.2.1.1
    (fun r hr => h.geometry.2.2.2.2.1 r (hcore hr)) hpositive

/-- The geometric constant is selected before every truncation and
frequency. The only central analytic input is raw w'>0 on two fixed
closed connectors, not a coercivity or Poisson bound. -/
theorem innerMorseInnerChain_exists_uniform_gap_slope
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (hindex : 10 ≤ T.index)
    {N : ℕ} (hN : T.index ≤ N) (center : Fin 2 → ℝ)
    (hc : center 0 < center 1)
    (hcl : innerMorseChainCut T false N 1 < center 0)
    (hcr : center 1 < innerMorseChainCut T true N 0)
    (hpositive : ∀ side r, r ∈ Icc (innerMorseMiddleGapLeft T N center side)
      (innerMorseMiddleGapRight T N center side) → 0 < deriv D.w r) :
    ∃ c : ℝ, 0 < c ∧ ∀ (K : ℕ) (hK : 0 < K) (g : Fin (2 * K + 2)),
      ∀ r ∈ Icc
        ((innerMorseInnerChainGeometry h hN hK center hc hcl hcr).left (innerModelChainGap g))
        ((innerMorseInnerChainGeometry h hN hK center hc hcl hcr).right (innerModelChainGap g)),
      c ≤ r * deriv D.w r / D.w r := by
  obtain ⟨a, ha, haBound⟩ := innerMorseMiddleGap_exists_slope h hN hc hcl hcr false (hpositive false)
  obtain ⟨b, hb, hbBound⟩ := innerMorseMiddleGap_exists_slope h hN hc hcl hcr true (hpositive true)
  refine ⟨min innerMorseTailSlope (min a b),
    lt_min innerMorseTailSlope_pos (lt_min ha hb), ?_⟩
  intro K hK g r hr
  have hg := innerMorseInnerGap_cases hK g
  rcases hg with ⟨side, rfl⟩ | ⟨side, rfl⟩ | ⟨side, p, rfl⟩
  · have he := innerMorseInnerChainGeometry_terminal h hN hK center hc hcl hcr side
    rw [he.1, he.2] at hr
    exact (min_le_left _ _).trans (innerMorseChain_outerCap_logSlope h side hindex
      (hN.trans (Nat.le_add_right _ _)) side hr)
  · have he := innerMorseInnerChainGeometry_middle h hN hK center hc hcl hcr side
    rw [he.1, he.2] at hr
    cases side with
    | false => exact ((min_le_right _ _).trans (min_le_left a b)).trans (haBound r hr)
    | true => exact ((min_le_right _ _).trans (min_le_right a b)).trans (hbBound r hr)
  · have he := innerMorseInnerChainGeometry_tailGap h hN hK center hc hcl hcr side p
    rw [he.1, he.2] at hr
    have hm : T.index ≤ innerMorseTailGapCell N K side p := by
      cases side <;> simp only [innerMorseTailGapCell, Bool.false_eq_true, ite_false, ite_true] <;> omega
    exact (min_le_left _ _).trans (innerMorseTailGap_logSlope h side hindex hm r hr)

/-- Frequency coercivity on every actual finite-chain gap, with one
constant independent of both the number of models and the frequency. -/
theorem innerMorseInnerChain_exists_uniform_gap_coercivity
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (hindex : 10 ≤ T.index)
    {N : ℕ} (hN : T.index ≤ N) (center : Fin 2 → ℝ)
    (hc : center 0 < center 1)
    (hcl : innerMorseChainCut T false N 1 < center 0)
    (hcr : center 1 < innerMorseChainCut T true N 0)
    (hpositive : ∀ side r, r ∈ Icc (innerMorseMiddleGapLeft T N center side)
      (innerMorseMiddleGapRight T N center side) → 0 < deriv D.w r) :
    ∃ c : ℝ, 0 < c ∧ ∀ (K : ℕ) (hK : 0 < K) (g : Fin (2 * K + 2))
      (u : ℝ → ℝ), ContDiff ℝ ∞ u → ∀ j : ℝ,
      c * j ^ 2 * innerRadialGapMass D.w u
        ((innerMorseInnerChainGeometry h hN hK center hc hcl hcr).left (innerModelChainGap g))
        ((innerMorseInnerChainGeometry h hN hK center hc hcl hcr).right (innerModelChainGap g)) ≤
      innerRadialGapEnergy D.w u j
        ((innerMorseInnerChainGeometry h hN hK center hc hcl hcr).left (innerModelChainGap g))
        ((innerMorseInnerChainGeometry h hN hK center hc hcl hcr).right (innerModelChainGap g)) := by
  obtain ⟨s, hs, hbound⟩ := innerMorseInnerChain_exists_uniform_gap_slope
    h hindex hN center hc hcl hcr hpositive
  refine ⟨s / 12, div_pos hs (by norm_num), ?_⟩
  intro K hK g u hu j
  let G := innerMorseInnerChainGeometry h hN hK center hc hcl hcr
  exact innerRadialGap_coercive (G.left_lt_right (innerModelChainGap g)).le
    (G.left_pos (innerModelChainGap g)) h.geometry.2.2.1.1 hu
    (G.weight_pos (innerModelChainGap g)) (hbound K hK g) j

end ContinuousFlexibility.Radial
