import ContinuousFlexibility.Analysis.N01cWholeSpeedPowerBounds
import ContinuousFlexibility.Analysis.N01cCoefficientBaseSelection
import ContinuousFlexibility.Analysis.N01cEndpointPowerRestriction
import ContinuousFlexibility.Analysis.N01cBoundsRestriction

/-!
# A stable common raw estimate for the actual whole speed

The material and optical inputs construct one endpoint-controlled field.
Its spatial interpolation loss is selected before any output or parameter
order. Every subsequent larger base and smaller radius keeps that loss.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

abbrev WholeCharacteristicSpeedPowerControl
    (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base loss : ℕ) (ε : ℝ) :=
  EndpointPowerControl (pairGrading (stateGrading S) realGrading) (C.referenceState, 0)
    base loss (stateNeighborhood S C base ε)
    (fun m => Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
    (fun m q => min (q.1 - C.left m) (C.right m - q.1))
    (fun m _ => T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ))
    (fun m _ => T.E0 (T.sample (C.cell m)))
    (fun _ z => minusCharacteristicSpeed (originalCoefficients D S C z))

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Blueprint

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

theorem n01_exists_commonWholeSpeed_powerControl
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hB : N01PartB D S C base ε)
    (hG : N01PrimitiveGeometry D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) :
    ∃ base₀ : ℕ, ∃ ε₀ : ℝ, ∃ lossRaw : ℕ,
      base ≤ base₀ ∧ 0 < ε₀ ∧ ε₀ ≤ min ε (1 / 2) ∧
        Nonempty (WholeCharacteristicSpeedPowerControl D T S C base₀ lossRaw ε₀) := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  obtain ⟨εo, hεo, ho⟩ :=
    n01_exists_stateOpticalRoot_endpoint_powerBounds hS hT hA hE hG.1 hG.2.2
  let ε₀ : ℝ := min ε (min (1 / 2) εo)
  have hε₀ : 0 < ε₀ := lt_min hε (lt_min (by norm_num) hεo)
  have hε₀ε : ε₀ ≤ ε := min_le_left _ _
  have hε₀2 : ε₀ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε₀o : ε₀ ≤ εo := (min_le_right _ _).trans (min_le_right _ _)
  let P : ℕ → ℕ → Prop := fun b loss =>
    Nonempty (WholeCharacteristicSpeedPowerControl D T S C b loss ε₀)
  obtain ⟨b, lossRaw, hb, hP⟩ :=
    exists_base_ge_of_spatialPower_continuation
      (pairGrading (stateGrading S) realGrading) (jointStateGrading_monotone S)
      (jointStateGrading_hasInterpolation hS) base 4 P
      (fun b loss hb hI => by
        have hB₀ : N01PartB D S C b ε₀ := n01PartB_mono hB hb hε₀ε
        have hroot := ho ε₀ hε₀ hε₀o b loss
        let G := Classical.choice hroot.1
        exact ⟨wholeCharacteristicSpeed_powerControl
          hS hT hA hε₀ (hε₀2.trans (by norm_num)) hB₀ hE
          hG.1 hG.2.1 hI G hroot.2⟩)
  exact ⟨b, ε₀, lossRaw, hb, hε₀, le_min hε₀ε hε₀2, hP⟩

/-- The single raw loss survives every later neighbourhood restriction. -/
theorem n01_exists_stable_commonWholeSpeed_powerControl
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hB : N01PartB D S C base ε)
    (hG : N01PrimitiveGeometry D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) :
    ∃ base₀ : ℕ, ∃ ε₀ : ℝ, ∃ lossRaw : ℕ,
      base ≤ base₀ ∧ 0 < ε₀ ∧ ε₀ ≤ min ε (1 / 2) ∧
      ∀ base' : ℕ, base₀ ≤ base' → ∀ ε' : ℝ, 0 < ε' → ε' ≤ ε₀ →
        Nonempty (WholeCharacteristicSpeedPowerControl D T S C base' lossRaw ε') := by
  obtain ⟨base₀, ε₀, lossRaw, hb, he, heε, ⟨W⟩⟩ :=
    n01_exists_commonWholeSpeed_powerControl hS hT hA hε hB hG hE
  refine ⟨base₀, ε₀, lossRaw, hb, he, heε, ?_⟩
  intro base' hb' ε' _ he'
  exact ⟨W.n01c_restrict (isOpen_stateNeighborhood S C base' ε')
    (stateNeighborhood_subset hb' he') (jointStateGrading_monotone S) hb'⟩

end ContinuousFlexibility.Blueprint
