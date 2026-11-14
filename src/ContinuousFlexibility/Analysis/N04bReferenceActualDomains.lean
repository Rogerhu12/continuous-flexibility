module

public import ContinuousFlexibility.Analysis.N04bReferenceActualTravel
public import ContinuousFlexibility.Analysis.N04bReferencePieces
public import ContinuousFlexibility.Analysis.N04bCurrentPartition

/-!
# Reference domains of the actual moving atlas

The actual reference travel chart is radial optical travel. Its strict
monotonicity identifies the two moving-half definitions with the intervals
split at the unique optical midpoint. The positive pieces retain exactly
their existing subdivision intervals and the same typed index.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem n04b_referenceTravel_mem_half_iff
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C)
    (m : ℕ) (side : Bool) {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    opticalTravel D.w (C.left m) r ∈ n04bTravelHalfInterval (C.travel m) side ↔
      r ∈ Ioo (n04bNegativeLeft C (n04bReferenceTravelCut hD hC) (m, side))
        (n04bNegativeRight C (n04bReferenceTravelCut hD hC) (m, side)) := by
  have hm := n04b_referenceTravel_strictMonoOn hD hC m
  have hc := n04bReferenceTravelCut_spec hD hC m
  have hcclosed : n04bReferenceTravelCut hD hC m ∈ Icc (C.left m) (C.right m) :=
    ⟨hc.1.1.le, hc.1.2.le⟩
  have hrclosed : r ∈ Icc (C.left m) (C.right m) := ⟨hr.1.le, hr.2.le⟩
  have hab := (hC.1 m).2.1
  have hleft : opticalTravel D.w (C.left m) (C.left m) = 0 :=
    intervalIntegral.integral_same
  have hright := n04b_referenceTravel_right hC m
  have hpos : 0 < opticalTravel D.w (C.left m) r := by
    simpa only [hleft] using hm (left_mem_Icc.mpr hab.le) hrclosed hr.1
  have htop : opticalTravel D.w (C.left m) r < C.travel m := by
    simpa only [hright] using hm hrclosed (right_mem_Icc.mpr hab.le) hr.2
  cases side with
  | false =>
    change (0 < opticalTravel D.w (C.left m) r ∧
        opticalTravel D.w (C.left m) r < C.travel m / 2) ↔
      (C.left m < r ∧ r < n04bReferenceTravelCut hD hC m)
    constructor
    · intro h
      refine ⟨hr.1, ?_⟩
      by_contra hn
      have hle := hm.monotoneOn hcclosed hrclosed (le_of_not_gt hn)
      rw [hc.2] at hle
      exact (not_lt_of_ge hle) h.2
    · intro h
      refine ⟨hpos, ?_⟩
      simpa only [hc.2] using hm hrclosed hcclosed h.2
  | true =>
    change (C.travel m / 2 < opticalTravel D.w (C.left m) r ∧
        opticalTravel D.w (C.left m) r < C.travel m) ↔
      (n04bReferenceTravelCut hD hC m < r ∧ r < C.right m)
    constructor
    · intro h
      refine ⟨?_, hr.2⟩
      by_contra hn
      have hle := hm.monotoneOn hrclosed hcclosed (le_of_not_gt hn)
      rw [hc.2] at hle
      exact (not_lt_of_ge hle) h.1
    · intro h
      refine ⟨?_, htop⟩
      simpa only [hc.2] using hm hcclosed hrclosed h.1

/-- The actual reference half-domain is the optical-cut radial interval. -/
theorem n04b_reference_negative_domain
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {base : ℕ} {ε : ℝ}
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C)
    (href : referenceStateConditions D S C)
    (hfield : N04bFieldRegularity D S C L base ε) (m : ℕ) (side : Bool) :
    n04bTravelHalfDomain (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
        (n04bActualTravelChart S C L (C.referenceState, 0) m) (C.travel m) side =
      Ioo (n04bNegativeLeft C (n04bReferenceTravelCut hD hC) (m, side))
        (n04bNegativeRight C (n04bReferenceTravelCut hD hC) (m, side)) ×ˢ univ := by
  ext p
  constructor
  · intro hp
    have hm := mem_n04bTravelDomain.mp hp
    have he := n04b_reference_actualTravelChart href hfield m
      ⟨hm.1.1.1.le, hm.1.1.2.le⟩ p.2
    have ht : opticalTravel D.w (C.left m) p.1 ∈
        n04bTravelHalfInterval (C.travel m) side := by
      simpa only [he] using hm.2
    exact ⟨(n04b_referenceTravel_mem_half_iff hD hC m side hm.1.1).mp ht, mem_univ _⟩
  · intro hp
    have hr : p.1 ∈ Ioo (C.left m) (C.right m) :=
      n04b_negativeHalf_subset
        (fun n => (n04bReferenceTravelCut_spec hD hC n).1) (m, side) hp.1
    apply mem_n04bTravelDomain.mpr
    refine ⟨⟨hr, mem_univ _⟩, ?_⟩
    rw [n04b_reference_actualTravelChart href hfield m ⟨hr.1.le, hr.2.le⟩ p.2]
    exact (n04b_referenceTravel_mem_half_iff hD hC m side hr).mpr hp.1

/-- The same typed index identifies the actual reference physical domain
with its stored radial endpoints, for both negative and positive pieces. -/
theorem n04b_reference_typed_domain
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {base : ℕ} {ε : ℝ}
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C)
    (href : referenceStateConditions D S C)
    (hfield : N04bFieldRegularity D S C L base ε) (i : N04PieceIndex D) :
    n04bTypedPhysicalDomain C (n04bActualTravelChart S C L (C.referenceState, 0)) i =
      Ioo (n04bReferenceTypedLeft C (n04bReferenceTravelCut hD hC) i)
        (n04bReferenceTypedRight C (n04bReferenceTravelCut hD hC) i) ×ˢ univ := by
  cases i with
  | inl i => exact n04b_reference_negative_domain hD hC href hfield i.1 i.2
  | inr i => rfl

end ContinuousFlexibility.Analysis
