import ContinuousFlexibility.Radial.MorseSecondModeGeometry

/-!
# Actual cell labels in the signed logarithmic coordinate

The right edge is one physical block. A left edge crosses the cap of
the next block, so its cell label changes exactly at that cap entrance.
The initial left edge has the corresponding predecessor/current labels.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

theorem morseSecondMode_joinOrder {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) {n : ℕ} (hn : T.index ≤ n)
    (right : Bool) :
    (if right then T.radius right n (T.rightX right n)
      else T.radius right (n + 1) (T.rightX right (n + 1))) <
      morseSecondModeMassLeft T right (if right then n + 1 else n) := by
  obtain ⟨_, _, _, hjoins, _, _, _, _, _, _⟩ := h
  have hj := hjoins right n hn
  have ho := hj.1
  rw [hj.2.1, hj.2.2.1] at ho
  cases right <;> simpa only [morseSecondModeMassLeft, Bool.false_eq_true, ↓reduceIte] using ho

theorem morseSecondMode_rightEndpoint_mem {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (right : Bool) {n : ℕ}
    (hn : T.index ≤ n) :
    T.radius right n (T.rightX right n) ∈ radialCore D := by
  obtain ⟨_, _, hmodels, _, hinside, _, _, _, _, _⟩ := h
  exact hinside right n hn
    ⟨T.rightX right n, ⟨(hmodels right n hn).2.1.le, le_rfl⟩, rfl⟩

theorem morseSecondMode_cellAt_block {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (right : Bool) {n : ℕ}
    (hn : T.index ≤ n) (x : ℝ)
    (hx : tailPhysicalRadius right x ∈ morseChainBlock T right n) :
    TailPhysicalCellAt D right n x := by
  obtain ⟨_, _, _, _, _, _, _, _, hcover, _⟩ := h
  exact hcover right n hn _ hx

/-- The full localization clause follows from the actual block cover in
MorseChainRealization, with the necessary left cap index shift. -/
theorem morseSecondMode_physicalLocalization {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) {N : ℕ} (hN : T.index < N)
    (right : Bool) :
    TailPhysicalLocalization D (morseSecondModeTail D T N right) right N := by
  have hg := morseSecondMode_profileGeometry h
  cases right
  · change
      (∀ n, ∃ capStart : ℝ,
        (morseSecondModeTail D T N false).massEnd n < capStart ∧
        capStart < (morseSecondModeTail D T N false).node (n + 1) ∧
        ∀ x ∈ Ioo ((morseSecondModeTail D T N false).node n)
          ((morseSecondModeTail D T N false).node (n + 1)),
          TailPhysicalCellAt D false
            (if x < capStart then N + n else N + n + 1) x) ∧ _
    constructor
    · intro n
      let k := N + n
      have hk : T.index ≤ k := by dsimp [k]; omega
      have hk₁ : T.index ≤ k + 1 := by omega
      have hk₂ : T.index ≤ k + 2 := by omega
      let R₁ := T.radius false (k + 1) (T.rightX false (k + 1))
      have hR₁ : 0 < R₁ := hg.1.trans (morseSecondMode_rightEndpoint_mem h false hk₁).1
      have hL : 0 < morseSecondModeMassLeft T false k :=
        hg.1.trans (morseSecondMode_massEndpoints h false hk).1.1
      have hM : 0 < morseChainMassEnd T false k :=
        hg.1.trans (morseSecondMode_massEndpoints h false hk).2.1
      have hM₁ : 0 < morseChainMassEnd T false (k + 1) :=
        hg.1.trans (morseSecondMode_massEndpoints h false hk₁).2.1
      have hjoin : R₁ < morseSecondModeMassLeft T false k := morseSecondMode_joinOrder h hk false
      have hmodel := morseSecondMode_modelOrder h false hk
      have hmodel₁ := morseSecondMode_modelOrder h false hk₁
      have hjoin₁ : T.radius false (k + 2) (T.rightX false (k + 2)) <
          morseSecondModeMassLeft T false (k + 1) := by
        simpa only [Nat.add_assoc] using morseSecondMode_joinOrder h hk₁ false
      refine ⟨-log R₁, ?_, ?_, ?_⟩
      · change -log (morseSecondModeMassLeft T false k) < -log R₁
        exact neg_lt_neg (log_lt_log hR₁ hjoin)
      · change -log R₁ < -log (morseChainMassEnd T false (N + (n + 1)))
        have heq : N + (n + 1) = k + 1 := by dsimp [k]; omega
        rw [heq]
        exact neg_lt_neg (log_lt_log hM₁ hmodel₁.2)
      · intro x hx
        have heq : N + (n + 1) = k + 1 := by dsimp [k]; omega
        change -log (morseChainMassEnd T false k) < x ∧
          x < -log (morseChainMassEnd T false (N + (n + 1))) at hx
        rw [heq] at hx
        have hrhi : exp (-x) < morseChainMassEnd T false k := by
          have hxx : -x < log (morseChainMassEnd T false k) := by linarith only [hx.1]
          simpa only [exp_log hM] using exp_lt_exp.mpr hxx
        have hrlo : morseChainMassEnd T false (k + 1) < exp (-x) := by
          have hxx : log (morseChainMassEnd T false (k + 1)) < -x := by linarith only [hx.2]
          simpa only [exp_log hM₁] using exp_lt_exp.mpr hxx
        by_cases hxc : x < -log R₁
        · simp only [hxc, ↓reduceIte]
          apply morseSecondMode_cellAt_block h false hk x
          have hrR : R₁ < exp (-x) := by
            have hxx : log R₁ < -x := by linarith only [hxc]
            simpa only [exp_log hR₁] using exp_lt_exp.mpr hxx
          change exp (-x) ∈ uIcc (T.radius false k (T.rightX false k)) R₁
          exact ⟨(min_le_right _ _).trans hrR.le,
            (hrhi.trans hmodel.2).le.trans (le_max_left _ _)⟩
        · simp only [hxc, ↓reduceIte]
          apply morseSecondMode_cellAt_block h false hk₁ x
          have hrR : exp (-x) ≤ R₁ := by
            have hxx : -x ≤ log R₁ := by linarith only [le_of_not_gt hxc]
            simpa only [exp_log hR₁] using exp_le_exp.mpr hxx
          change exp (-x) ∈ uIcc R₁ (T.radius false (k + 1 + 1) (T.rightX false (k + 1 + 1)))
          have hrbottom : T.radius false (k + 1 + 1) (T.rightX false (k + 1 + 1)) < exp (-x) := by
            simpa only [Nat.add_assoc] using (hjoin₁.trans hmodel₁.1).trans hrlo
          exact ⟨(min_le_right _ _).trans hrbottom.le, hrR.trans (le_max_left _ _)⟩
    · right
      have hN₀ : 0 < N := by omega
      have hp : T.index ≤ N - 1 := by omega
      have heq : N - 1 + 1 = N := by omega
      let R₀ := T.radius false N (T.rightX false N)
      have hR₀ : 0 < R₀ := hg.1.trans (morseSecondMode_rightEndpoint_mem h false hN.le).1
      have hLp : 0 < morseSecondModeMassLeft T false (N - 1) :=
        hg.1.trans (morseSecondMode_massEndpoints h false hp).1.1
      have hM : 0 < morseChainMassEnd T false N :=
        hg.1.trans (morseSecondMode_massEndpoints h false hN.le).2.1
      have hjoin : R₀ < morseSecondModeMassLeft T false (N - 1) := by
        simpa only [heq] using morseSecondMode_joinOrder h hp false
      have hmodel := morseSecondMode_modelOrder h false hN.le
      have hmodelp := morseSecondMode_modelOrder h false hp
      have hjoinnext := morseSecondMode_joinOrder h hN.le false
      refine ⟨hN₀, -log R₀, ?_, ?_, ?_, ?_⟩
      · change -log (morseSecondModeMassLeft T false (N - 1)) < -log R₀
        exact neg_lt_neg (log_lt_log hR₀ hjoin)
      · change -log R₀ < -log (morseChainMassEnd T false (N + 0))
        simpa only [Nat.add_zero] using neg_lt_neg (log_lt_log hM hmodel.2)
      · intro x hx
        change -log (morseSecondModeMassLeft T false (N - 1)) ≤ x ∧ x < -log R₀ at hx
        apply morseSecondMode_cellAt_block h false hp x
        have hrlo : R₀ < exp (-x) := by
          have hxx : log R₀ < -x := by linarith only [hx.2]
          simpa only [exp_log hR₀] using exp_lt_exp.mpr hxx
        have hrhi : exp (-x) ≤ morseSecondModeMassLeft T false (N - 1) := by
          have hxx : -x ≤ log (morseSecondModeMassLeft T false (N - 1)) := by
            linarith only [hx.1]
          simpa only [exp_log hLp] using exp_le_exp.mpr hxx
        change exp (-x) ∈ uIcc
          (T.radius false (N - 1) (T.rightX false (N - 1)))
          (T.radius false (N - 1 + 1) (T.rightX false (N - 1 + 1)))
        rw [heq]
        exact ⟨(min_le_right _ _).trans hrlo.le,
          (hrhi.trans_lt (hmodelp.1.trans hmodelp.2)).le.trans (le_max_left _ _)⟩
      · intro x hx
        change -log R₀ ≤ x ∧ x < -log (morseChainMassEnd T false (N + 0)) at hx
        simp only [Nat.add_zero] at hx
        apply morseSecondMode_cellAt_block h false hN.le x
        have hrhi : exp (-x) ≤ R₀ := by
          have hxx : -x ≤ log R₀ := by linarith only [hx.1]
          simpa only [exp_log hR₀] using exp_le_exp.mpr hxx
        have hrlo : morseChainMassEnd T false N < exp (-x) := by
          have hxx : log (morseChainMassEnd T false N) < -x := by linarith only [hx.2]
          simpa only [exp_log hM] using exp_lt_exp.mpr hxx
        change exp (-x) ∈ uIcc R₀ (T.radius false (N + 1) (T.rightX false (N + 1)))
        exact ⟨(min_le_right _ _).trans ((hjoinnext.trans hmodel.1).trans hrlo).le,
          hrhi.trans (le_max_left _ _)⟩
  · change (morseSecondModeTail D T N true).entrance =
      (morseSecondModeTail D T N true).node 0 ∧ _
    constructor
    · simp only [morseSecondModeTail, ↓reduceIte, Nat.add_zero]
    · intro n x hx
      have hk : T.index ≤ N + n := by omega
      have hk' : T.index ≤ N + (n + 1) := by omega
      have hL : 0 < morseSecondModeMassLeft T true (N + n) :=
        hg.1.trans (morseSecondMode_massEndpoints h true hk).1.1
      have hL' : 0 < morseSecondModeMassLeft T true (N + (n + 1)) :=
        hg.1.trans (morseSecondMode_massEndpoints h true hk').1.1
      change log (morseSecondModeMassLeft T true (N + n)) < x ∧
        x < log (morseSecondModeMassLeft T true (N + (n + 1))) at hx
      have hrlo : morseSecondModeMassLeft T true (N + n) < exp x := by
        simpa only [exp_log hL] using exp_lt_exp.mpr hx.1
      have hrhi : exp x < morseSecondModeMassLeft T true (N + (n + 1)) := by
        simpa only [exp_log hL'] using exp_lt_exp.mpr hx.2
      apply morseSecondMode_cellAt_block h true hk x
      change exp x ∈ uIcc (morseSecondModeMassLeft T true (N + n))
        (morseSecondModeMassLeft T true (N + n + 1))
      have heq : N + (n + 1) = N + n + 1 := by omega
      rw [heq] at hrhi
      exact ⟨(min_le_left _ _).trans hrlo.le, hrhi.le.trans (le_max_right _ _)⟩

end ContinuousFlexibility.Radial
