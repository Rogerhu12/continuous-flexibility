import ContinuousFlexibility.Radial.MorseSecondModeDeepInequalities
import ContinuousFlexibility.Radial.MorseSecondModeLocalization

/-!
# The deep-tail hypotheses for actual second-mode Morse coordinates

The finite discard is common to both orientations. Inward enlargement
of the discarded prefix remains possible, which permits any previously
specified natural solution to be restricted to the resulting tail.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

def MorseSecondModeDeepBounds (T : MorseChainData) (D : ReferenceData) (N : ℕ) : Prop :=
  ∀ right : Bool, ∀ n, N ≤ n →
    0 < morseCellMass T D right n ∧
    0 < morseJoinResistance T D right n ∧
    12 * morseCellMass T D right n * morseCellResistance T D right n ≤ 1 / 32 ∧
    12 * morseJoinMass T D right n * morseJoinResistance T D right n ≤ 1 / 32 ∧
    ∀ m, N ≤ m → (m = n ∨ m = n + 1 ∨ n = m + 1) →
      32 ≤ 12 * morseCellMass T D right m * morseJoinResistance T D right n ∧
      morseJoinMass T D right n ≤ (1 / 16) * morseCellMass T D right m

theorem morseSecondMode_mass_inner_product {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) {N : ℕ} (hN : T.index ≤ N)
    (right : Bool) (n : ℕ) :
    tailMass (morseSecondModeTail D T N right) n *
        tailInnerResistance (morseSecondModeTail D T N right) n =
      morseCellMass T D right (N + n) * morseCellResistance T D right (N + n) := by
  rw [morseSecondMode_tailMass hreal hN, morseSecondMode_tailInnerResistance hreal hN]
  have hR := (morseSecondMode_endpoint_pos (morseSecondMode_profileGeometry hreal) right).ne'
  field_simp [hR]
        <;> ring

theorem morseSecondMode_gap_product {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) {N : ℕ} (hN : T.index ≤ N)
    (right : Bool) (n : ℕ) :
    tailGapMass (morseSecondModeTail D T N right) n *
        tailResistance (morseSecondModeTail D T N right) n =
      morseJoinMass T D right (if right then N + n else N + n + 1) *
        morseJoinResistance T D right (if right then N + n else N + n + 1) := by
  rw [morseSecondMode_tailGapMass hreal hN, morseSecondMode_tailResistance hreal hN]
  have hR := (morseSecondMode_endpoint_pos (morseSecondMode_profileGeometry hreal) right).ne'
  field_simp [hR]
        <;> ring

theorem morseSecondMode_mass_gap_product {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) {N : ℕ} (hN : T.index ≤ N)
    (right : Bool) (m n : ℕ) :
    tailMass (morseSecondModeTail D T N right) m *
        tailResistance (morseSecondModeTail D T N right) n =
      morseCellMass T D right (N + m) *
        morseJoinResistance T D right (if right then N + n else N + n + 1) := by
  rw [morseSecondMode_tailMass hreal hN, morseSecondMode_tailResistance hreal hN]
  have hR := (morseSecondMode_endpoint_pos (morseSecondMode_profileGeometry hreal) right).ne'
  field_simp [hR]
        <;> ring

theorem morseSecondMode_deepHypotheses {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) {N : ℕ} (hN : T.index < N)
    (hdeep : MorseSecondModeDeepBounds T D N) (right : Bool) :
    DeepTailHypotheses (morseSecondModeTail D T N right) := by
  have hentry := morseSecondMode_entrance_order hreal hN right
  refine ⟨hentry.1, hentry.2, by norm_num [morseSecondModeTail], ?_,
    by norm_num [morseSecondModeTail], by norm_num [morseSecondModeTail],
    by norm_num [morseSecondModeTail],
    (morseSecondMode_density_smooth hreal N right).contDiffOn,
    fun x hx => morseSecondMode_density_pos hreal hN right hx,
    morseSecondMode_node_tendsto hreal hN.le right, ?_⟩
  · cases right
    · right
      have hg := morseSecondMode_profileGeometry hreal
      have hpred : T.index ≤ N - 1 := by omega
      have hsucc : N - 1 + 1 = N := by omega
      have hM := (morseSecondMode_massEndpoints hreal false hN.le).2
      have hgap := morseSecondMode_gapOrder hreal hpred false
      simp only [Bool.false_eq_true, ↓reduceIte, hsucc] at hgap
      have hi : (morseSecondModeTail D T N false).entrance <
          (morseSecondModeTail D T N false).node 0 := by
        simp only [morseSecondModeTail, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact neg_lt_neg (log_lt_log (hg.1.trans hM.1) hgap)
      have hnum := hdeep false N le_rfl
      have hsame := hnum.2.2.2.2 N le_rfl (Or.inl rfl)
      have hR := hg.1.ne'
      have hprod : tailInitialGapMass (morseSecondModeTail D T N false) *
          tailInitialResistance (morseSecondModeTail D T N false) =
          morseJoinMass T D false N * morseJoinResistance T D false N := by
        rw [morseSecondMode_tailInitialGapMass hreal hN,
          morseSecondMode_tailInitialResistance hreal hN]
        field_simp [hR]
        <;> ring
      have hmprod : tailMass (morseSecondModeTail D T N false) 0 *
          tailInitialResistance (morseSecondModeTail D T N false) =
          morseCellMass T D false N * morseJoinResistance T D false N := by
        rw [morseSecondMode_tailMass hreal hN.le,
          morseSecondMode_tailInitialResistance hreal hN]
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        field_simp [hR]
        <;> ring
      refine ⟨hi, ?_, ?_, ?_⟩
      · change 12 * _ * _ ≤ (1 : ℝ) / 16
        rw [mul_assoc, hprod]
        nlinarith only [hnum.2.2.2.1]
      · change tailInitialGapMass (morseSecondModeTail D T N false) ≤
          (1 / 16) * tailMass (morseSecondModeTail D T N false) 0
        rw [morseSecondMode_tailInitialGapMass hreal hN,
          morseSecondMode_tailMass hreal hN.le]
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        have hh := mul_le_mul_of_nonneg_left hsame.2
          (show 0 ≤ (D.a ^ 8)⁻¹ by positivity)
        nlinarith only [hh]
      · change (32 : ℝ) ≤ 12 * _ * _
        rw [mul_assoc, hmprod]
        nlinarith only [hsame.1]
    · left
      simp only [morseSecondModeTail, ↓reduceIte, Nat.add_zero]
  · intro n
    have hnode := morseSecondMode_node_order hreal hN.le right n
    let e : ℕ := if right then N + n else N + n + 1
    have hn : N ≤ N + n := Nat.le_add_right N n
    have he : N ≤ e := by
      dsimp only [e]
      cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    have hm : N ≤ N + (n + 1) := Nat.le_add_right N (n + 1)
    have hnear : N + n = e ∨ N + n = e + 1 ∨ e = N + n + 1 := by
      cases right
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl rfl
    have hnear' : N + (n + 1) = e ∨ N + (n + 1) = e + 1 ∨ e = N + (n + 1) + 1 := by
      cases right
      · exact Or.inl (Nat.add_assoc N n 1).symm
      · exact Or.inr (Or.inl (Nat.add_assoc N n 1).symm)
    have hcur := hdeep right (N + n) hn
    have hedge := hdeep right e he
    have hp := hedge.2.2.2.2 (N + n) hn hnear
    have hp' := hedge.2.2.2.2 (N + (n + 1)) hm hnear'
    dsimp only [e] at hedge hp hp'
    refine ⟨hnode.1, hnode.2, ?_, ?_, ?_, ?_⟩
    · change 12 * _ * _ + 12 * _ * _ ≤ (1 : ℝ) / 16
      rw [mul_assoc, mul_assoc,
        morseSecondMode_mass_inner_product hreal hN.le,
        morseSecondMode_gap_product hreal hN.le]
      nlinarith only [hcur.2.2.1, hedge.2.2.2.1]
    · change (32 : ℝ) ≤ 12 * _ * _
      rw [mul_assoc, morseSecondMode_mass_gap_product hreal hN.le]
      nlinarith only [hp.1]
    · change (32 : ℝ) ≤ 12 * _ * _
      rw [mul_assoc, morseSecondMode_mass_gap_product hreal hN.le]
      nlinarith only [hp'.1]
    · have hR := morseSecondMode_endpoint_pos (morseSecondMode_profileGeometry hreal) right
      have hcoef : 0 ≤ ((if right then D.b else D.a) ^ 8)⁻¹ := by positivity
      have hν : tailGapMass (morseSecondModeTail D T N right) n ≤
          (1 / 16) * tailMass (morseSecondModeTail D T N right) n := by
        rw [morseSecondMode_tailGapMass hreal hN.le,
          morseSecondMode_tailMass hreal hN.le]
        have hh := mul_le_mul_of_nonneg_left hp.2 hcoef
        nlinarith only [hh]
      have hν' : tailGapMass (morseSecondModeTail D T N right) n ≤
          (1 / 16) * tailMass (morseSecondModeTail D T N right) (n + 1) := by
        rw [morseSecondMode_tailGapMass hreal hN.le,
          morseSecondMode_tailMass hreal hN.le]
        have hh := mul_le_mul_of_nonneg_left hp'.2 hcoef
        nlinarith only [hh]
      change tailGapMass (morseSecondModeTail D T N right) n ≤
        (1 / 16) * min (tailMass (morseSecondModeTail D T N right) n)
          (tailMass (morseSecondModeTail D T N right) (n + 1))
      rcases le_total (tailMass (morseSecondModeTail D T N right) n)
        (tailMass (morseSecondModeTail D T N right) (n + 1)) with h | h
      · rwa [min_eq_left h]
      · rwa [min_eq_right h]

/-- Every sufficiently deep retained entrance gives actual deep-tail
data. The cutoff may be enlarged to meet an independently fixed entry. -/
theorem morseSecondMode_exists_deepHypotheses {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C)
    (hmass : MorseMassResistanceBounds T σ D C)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) :
    ∃ N : ℕ, T.index < N ∧ ∀ M, N ≤ M → ∀ right : Bool,
      DeepTailHypotheses (morseSecondModeTail D T M right) := by
  obtain ⟨N, hN, hdeep⟩ := morseSecondMode_eventually_deep hreal hmass hσ
  refine ⟨N, hN, ?_⟩
  intro M hM right
  apply morseSecondMode_deepHypotheses hreal (hN.trans_le hM) _ right
  intro side n hn
  obtain ⟨hμ, hR, hI, hG, hpair⟩ := hdeep side n (hM.trans hn)
  refine ⟨hμ, hR, hI, hG, ?_⟩
  intro m hm hnear
  exact hpair m (hM.trans hm) hnear

end ContinuousFlexibility.Radial
