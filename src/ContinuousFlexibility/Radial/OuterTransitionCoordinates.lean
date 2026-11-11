import ContinuousFlexibility.Radial.OuterUnifiedCore
import ContinuousFlexibility.Radial.OuterDeepGeometry
import ContinuousFlexibility.Radial.OuterWholeMeasure

/-!
# Actual transition endpoints in the outward radial coordinate

The same geometrical core is used by the radial energy estimate and
the whole outer Green operator. The coordinate reflection changes only
its orientation, including the initial middle cut.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

def morseTransitionPhysicalEntry (M : MorseChainData) (entry : ℝ)
    (right : Bool) (n : ℕ) : ℝ :=
  if right then morseTransitionCoreLeft M entry right n
    else morseTransitionCoreRight M entry right n

def morseTransitionOutwardLeft (M : MorseChainData) (entry : ℝ)
    (right : Bool) (n : ℕ) : ℝ :=
  if right then morseTransitionCoreLeft M entry right n
    else -morseTransitionCoreRight M entry right n

def morseTransitionOutwardRight (M : MorseChainData) (entry : ℝ)
    (right : Bool) (n : ℕ) : ℝ :=
  if right then morseTransitionCoreRight M entry right n
    else -morseTransitionCoreLeft M entry right n

theorem morseTransitionOutwardLeft_eq (M : MorseChainData) (entry : ℝ)
    (right : Bool) (n : ℕ) :
    morseTransitionOutwardLeft M entry right n =
      outerOutwardRadius right (morseTransitionPhysicalEntry M entry right n) := by
  cases right <;> rfl

theorem morseTransitionOutwardRight_eq (M : MorseChainData) (entry : ℝ)
    (right : Bool) (n : ℕ) :
    morseTransitionOutwardRight M entry right n =
      outerOutwardRadius right (morseOuterDeepEntrance M right n) := by
  by_cases hi : n = M.index
  · subst n
    cases right <;> simp [morseTransitionOutwardRight, morseTransitionCoreLeft,
      morseTransitionCoreRight, morseInitialCoreLeft, morseInitialCoreRight,
      morseInitialSupportLeft, morseInitialSupportRight, morseOuterDeepEntrance,
      outerOutwardRadius]
  · cases right <;> simp [morseTransitionOutwardRight, morseTransitionCoreLeft,
      morseTransitionCoreRight, morseOuterCoreLeft, morseOuterFullCoreRight,
      morseOuterDeepEntrance, outerOutwardRadius, hi]

theorem morseTransitionPhysicalEntry_mem_core
    {M : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization M σ D C) {entry : ℝ}
    (he : entry ∈ morseInitialMiddle M) (right : Bool) (n : ℕ) (hn : M.index ≤ n) :
    morseTransitionPhysicalEntry M entry right n ∈ radialCore D := by
  have hi := morseTransitionCore_interval h he right n hn
  cases right
  · exact hi.2 (right_mem_Icc.mpr hi.1.le)
  · exact hi.2 (left_mem_Icc.mpr hi.1.le)

theorem morseTransitionOutward_interval
    {M : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization M σ D C) {entry : ℝ}
    (he : entry ∈ morseInitialMiddle M) (right : Bool) (n : ℕ) (hn : M.index ≤ n) :
    morseTransitionOutwardLeft M entry right n <
      morseTransitionOutwardRight M entry right n ∧
      morseTransitionOutwardRight M entry right n <
        outerOutwardRadius right (tailPhysicalEndpoint D right) := by
  have hi := morseTransitionCore_interval h he right n hn
  constructor
  · cases right
    · exact neg_lt_neg hi.1
    · exact hi.1
  · rw [morseTransitionOutwardRight_eq]
    exact outerWhole_interval (morseOuterDeepEntrance_mem_core h right n hn)

/-- Reflection identifies the closed outward core with the same radial interval. -/
theorem outerOutwardRadius_mem_core_interval (right : Bool) (l r x : ℝ) :
    outerOutwardRadius right x ∈ Icc l r ↔
      x ∈ Icc (if right then l else -r) (if right then r else -l) := by
  cases right
  · change (l ≤ -x ∧ -x ≤ r) ↔ (-r ≤ x ∧ x ≤ -l)
    constructor <;> intro hx <;> constructor <;> linarith only [hx.1, hx.2]
  · rfl

/-- The actual deep entrance is at or beyond the left endpoint of the
first mass in increasing physical radius, in both orientations. -/
theorem morseOuterDeepEntrance_mass_left_le
    {M : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization M σ D C) (right : Bool) (n : ℕ) (hn : M.index ≤ n) :
    M.radius right (n + 1) (M.leftX right (n + 1)) ≤
      morseOuterDeepEntrance M right n := by
  cases right with
  | true =>
      change M.radius true (n + 1) (M.leftX true (n + 1)) ≤ M.joinRight true n
      simpa only [ite_true] using ((h.join_data true n hn).2.2.1).symm.le
  | false =>
      have hm := morseRealized_mass_geometry h false (n + 1) (hn.trans (Nat.le_succ n))
      have hj := h.join_data false n hn
      have hjord : M.radius false (n + 1) (M.rightX false (n + 1)) <
          M.radius false n (M.leftX false n) := by
        simpa only [hj.2.1, hj.2.2.1, Bool.false_eq_true, ite_false] using hj.1
      exact (hm.2.2.2.1.trans (hm.2.2.2.2.trans hjord)).le

end ContinuousFlexibility.Radial
