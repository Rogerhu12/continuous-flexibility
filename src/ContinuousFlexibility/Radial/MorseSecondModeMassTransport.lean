module

public import ContinuousFlexibility.Radial.MorseSecondModeCoordinates

/-!
# Physical mass and resistance of the actual second-mode tail

The exact substitution formulas are applied to the Morse mass intervals
and to the resistance interval following each mass interval in outward order.
On the left this is the original J_(n+1), including its positive connector.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

theorem morseSecondMode_profileGeometry {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) : RadialProfileGeometry D := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hacc⟩ := h
  exact hacc.1

/-- Both endpoints of a Morse mass interval lie in the actual radial core. -/
theorem morseSecondMode_massEndpoints {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (right : Bool) {n : ℕ}
    (hn : T.index ≤ n) :
    morseSecondModeMassLeft T right n ∈ radialCore D ∧
      morseChainMassEnd T right n ∈ radialCore D := by
  obtain ⟨_, hgeom, hmodels, _, hinside, _, _, _, _, _⟩ := h
  have hG := hgeom right n hn
  have hL : T.leftX right n ∈ Icc (T.leftX right n) (T.rightX right n) :=
    ⟨le_rfl, (hmodels right n hn).2.1.le⟩
  have hM : morseChainRightTurn T n ∈ Icc (T.leftX right n) (T.rightX right n) :=
    ⟨hG.2.2.2.1.le, hG.2.2.2.2.1.le⟩
  exact ⟨hinside right n hn ⟨_, hL, rfl⟩, hinside right n hn ⟨_, hM, rfl⟩⟩

theorem morseSecondMode_endpoint_pos {D : ReferenceData}
    (h : RadialProfileGeometry D) (right : Bool) :
    0 < (if right then D.b else D.a) := by
  cases right
  · exact h.1
  · exact h.1.trans h.2.1

/-- The physical mass interval and its normalized logarithmic image have
exactly the expected mass. -/
theorem morseSecondMode_tailMass {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) {N : ℕ} (hN : T.index ≤ N)
    (right : Bool) (n : ℕ) :
    tailMass (morseSecondModeTail D T N right) n =
      ((if right then D.b else D.a) ^ 8)⁻¹ *
        morseCellMass T D right (N + n) := by
  have hg := morseSecondMode_profileGeometry h
  obtain ⟨hL, hM⟩ := morseSecondMode_massEndpoints h right
    (hN.trans (Nat.le_add_right N n))
  have hsub := morseSecondMode_outward_mass right hg.2.2.1.1.continuous
    (morseSecondMode_endpoint_pos hg right).ne'
    (hg.1.trans hL.1) (hg.1.trans hM.1)
  simpa only [tailMass, morseSecondModeTail, morseCellMass, morseSecondModeMassLeft]
    using hsub

/-- The same change of variables computes the inner resistance exactly. -/
theorem morseSecondMode_tailInnerResistance {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) {N : ℕ} (hN : T.index ≤ N)
    (right : Bool) (n : ℕ) :
    tailInnerResistance (morseSecondModeTail D T N right) n =
      (if right then D.b else D.a) ^ 8 *
        morseCellResistance T D right (N + n) := by
  have hg := morseSecondMode_profileGeometry h
  obtain ⟨hL, hM⟩ := morseSecondMode_massEndpoints h right
    (hN.trans (Nat.le_add_right N n))
  have hw₀ : ∀ r ∈ uIcc (morseSecondModeMassLeft T right (N + n))
      (morseChainMassEnd T right (N + n)), D.w r ≠ 0 := by
    intro r hr
    exact (hg.2.2.2.2.1 r (ordConnected_Ioo.uIcc_subset hL hM hr)).ne'
  have hsub := morseSecondMode_outward_resistance right hg.2.2.1.1.continuous
    (morseSecondMode_endpoint_pos hg right).ne'
    (hg.1.trans hL.1) (hg.1.trans hM.1) hw₀
  simpa only [tailInnerResistance, morseSecondModeTail,
    morseCellResistance, morseSecondModeMassLeft] using hsub

/-- The outward resistance edge belongs to index n on the right and n+1
on the left. Its other endpoint is the indicated physical mass entrance. -/
theorem morseSecondMode_resistanceEnd {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) {n : ℕ} (hn : T.index ≤ n)
    (right : Bool) :
    morseChainResistanceEnd T right (if right then n else n + 1) =
      morseSecondModeMassLeft T right (if right then n + 1 else n) := by
  obtain ⟨_, _, _, hjoins, _, _, _, _, _, _⟩ := h
  have hjoin := (hjoins right n hn).2.2.1
  cases right
  · have hi : T.index < n + 1 := lt_of_le_of_lt hn (Nat.lt_succ_self n)
    simpa only [morseChainResistanceEnd, morseSecondModeMassLeft,
      Bool.false_eq_true, ↓reduceIte, hi, Nat.add_sub_cancel] using hjoin
  · simpa only [morseChainResistanceEnd, morseSecondModeMassLeft, ↓reduceIte]
      using hjoin

/-- The endpoints of the original resistance edge are both interior. -/
theorem morseSecondMode_gapEndpoints {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) {n : ℕ} (hn : T.index ≤ n)
    (right : Bool) :
    morseChainMassEnd T right (if right then n else n + 1) ∈ radialCore D ∧
      morseChainResistanceEnd T right (if right then n else n + 1) ∈ radialCore D := by
  have hi₁ : T.index ≤ (if right then n else n + 1) := by
    cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hi₂ : T.index ≤ (if right then n + 1 else n) := by
    cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  refine ⟨(morseSecondMode_massEndpoints h right hi₁).2, ?_⟩
  rw [morseSecondMode_resistanceEnd h hn right]
  exact (morseSecondMode_massEndpoints h right hi₂).1

theorem morseSecondMode_tailGapMass {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) {N : ℕ} (hN : T.index ≤ N)
    (right : Bool) (n : ℕ) :
    tailGapMass (morseSecondModeTail D T N right) n =
      ((if right then D.b else D.a) ^ 8)⁻¹ *
        morseJoinMass T D right (if right then N + n else N + n + 1) := by
  have hg := morseSecondMode_profileGeometry h
  have hi : T.index ≤ N + n := hN.trans (Nat.le_add_right N n)
  obtain ⟨hM, hE⟩ := morseSecondMode_gapEndpoints h hi right
  have hsub := morseSecondMode_outward_mass right hg.2.2.1.1.continuous
    (morseSecondMode_endpoint_pos hg right).ne'
    (hg.1.trans hM.1) (hg.1.trans hE.1)
  have hend := morseSecondMode_resistanceEnd h hi right
  cases right <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_assoc] at hend hsub ⊢
  · simpa only [tailGapMass, morseSecondModeTail, Bool.false_eq_true, ↓reduceIte,
      morseJoinMass, hend, Nat.add_assoc] using hsub
  · simpa only [tailGapMass, morseSecondModeTail, ↓reduceIte,
      morseJoinMass, hend, Nat.add_assoc] using hsub

theorem morseSecondMode_tailResistance {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) {N : ℕ} (hN : T.index ≤ N)
    (right : Bool) (n : ℕ) :
    tailResistance (morseSecondModeTail D T N right) n =
      (if right then D.b else D.a) ^ 8 *
        morseJoinResistance T D right (if right then N + n else N + n + 1) := by
  have hg := morseSecondMode_profileGeometry h
  have hi : T.index ≤ N + n := hN.trans (Nat.le_add_right N n)
  obtain ⟨hM, hE⟩ := morseSecondMode_gapEndpoints h hi right
  have hw₀ : ∀ r ∈ uIcc
      (morseChainMassEnd T right (if right then N + n else N + n + 1))
      (morseChainResistanceEnd T right (if right then N + n else N + n + 1)),
      D.w r ≠ 0 := by
    intro r hr
    exact (hg.2.2.2.2.1 r (ordConnected_Ioo.uIcc_subset hM hE hr)).ne'
  have hsub := morseSecondMode_outward_resistance right hg.2.2.1.1.continuous
    (morseSecondMode_endpoint_pos hg right).ne'
    (hg.1.trans hM.1) (hg.1.trans hE.1) hw₀
  have hend := morseSecondMode_resistanceEnd h hi right
  cases right <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_assoc] at hend hsub ⊢
  · simpa only [tailResistance, morseSecondModeTail, Bool.false_eq_true, ↓reduceIte,
      morseJoinResistance, hend, Nat.add_assoc] using hsub
  · simpa only [tailResistance, morseSecondModeTail, ↓reduceIte,
      morseJoinResistance, hend, Nat.add_assoc] using hsub

/-- The left entrance is the beginning of the full initial resistance
edge, so its mass is the original mass of J_N. -/
theorem morseSecondMode_tailInitialGapMass {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) {N : ℕ} (hN : T.index < N) :
    tailInitialGapMass (morseSecondModeTail D T N false) =
      (D.a ^ 8)⁻¹ * morseJoinMass T D false N := by
  have hpred : T.index ≤ N - 1 := by omega
  have hsucc : N - 1 + 1 = N := by omega
  have hgap := morseSecondMode_tailGapMass h hpred false 0
  simpa only [tailInitialGapMass, tailGapMass, morseSecondModeTail,
    Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.zero_add, hsucc] using hgap

theorem morseSecondMode_tailInitialResistance {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) {N : ℕ} (hN : T.index < N) :
    tailInitialResistance (morseSecondModeTail D T N false) =
      D.a ^ 8 * morseJoinResistance T D false N := by
  have hpred : T.index ≤ N - 1 := by omega
  have hsucc : N - 1 + 1 = N := by omega
  have hgap := morseSecondMode_tailResistance h hpred false 0
  simpa only [tailInitialResistance, tailResistance, morseSecondModeTail,
    Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.zero_add, hsucc] using hgap

end ContinuousFlexibility.Radial
