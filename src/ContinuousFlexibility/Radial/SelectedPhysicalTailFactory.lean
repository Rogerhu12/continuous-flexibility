module

public import ContinuousFlexibility.Radial.SelectedOuterDeepSplit
public import ContinuousFlexibility.Radial.OuterPhysicalTailBasis

/-!
# The actual selected deep split in the physical tail factory

The R07 and physical factories describe the same logarithmic tail. Their
only syntactic difference is the natural-number versus real exponent in
the gauge density. Thus the complete physical basis is constructed from
the deep hypotheses already proved for the selected profile.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

theorem r07PhysicalDensity_eq_outerMassLogDensity (D : ReferenceData)
    (right : Bool) (j : ℕ) :
    r07PhysicalDensity D right j =
      outerMassLogDensity D j (tailPhysicalEndpoint D right) right := by
  funext x
  unfold r07PhysicalDensity outerMassLogDensity tailPhysicalEndpoint
  rw [show 2 * (j : ℝ) ^ 2 = ((2 * j ^ 2 : ℕ) : ℝ) by simp, rpow_natCast]

theorem r07DeepTailData_eq_morsePhysicalDeepTail (M : MorseChainData)
    (D : ReferenceData) (right : Bool) (j start : ℕ) (η K : ℝ) :
    r07DeepTailData M D right j start η K =
      morsePhysicalDeepTail M D right j start
        (if right then r07MassNodeRadius M right start
          else morseChainResistanceEnd M right start) η K := by
  unfold r07DeepTailData morsePhysicalDeepTail
  rw [r07PhysicalDensity_eq_outerMassLogDensity] <;> rfl

theorem SelectedOuterDeepSplitData.physicalFactory
    {S : SelectedTailData} {n j start : ℕ} {η K : ℝ} {right : Bool}
    (h : SelectedOuterDeepSplitData S n j start η K right) :
    DeepTailHypotheses (morsePhysicalDeepTail S.chain (S.family S.sigma) right j start
        (selectedOuterDeepEntrance S right start) η K) ∧
      TailPhysicalRelation (S.family S.sigma)
        (morsePhysicalDeepTail S.chain (S.family S.sigma) right j start
          (selectedOuterDeepEntrance S right start) η K) right j start := by
  simpa only [r07DeepTailData_eq_morsePhysicalDeepTail, selectedOuterDeepEntrance] using
    And.intro h.hypotheses h.physical

/-- The actual normalized natural and Dirichlet states at the auxiliary
split are outputs of the recurrence and gauge construction. -/
theorem SelectedOuterDeepSplitData.exists_physicalBasis
    {S : SelectedTailData} {n j start : ℕ} {η K : ℝ} {right : Bool}
    (hS : IsSelectedTail S) (h : SelectedOuterDeepSplitData S n j start η K right)
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K) :
    Nonempty (MorsePhysicalTailBasis S.chain (S.family S.sigma) right j start
      (selectedOuterDeepEntrance S right start) η K) := by
  have hreal : MorseChainRealization S.chain S.sigma (S.family S.sigma) S.constants :=
    (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hD := r07_realization_geometry hreal
  exact exists_morsePhysicalTailBasis hD right j start
    (hD.1.trans h.entrance_core.1) h.physicalFactory.1 hη hK

end ContinuousFlexibility.Radial
