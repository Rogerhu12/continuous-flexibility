module

public import ContinuousFlexibility.Analysis.N04bRootTravelCharts
public import ContinuousFlexibility.Analysis.N04bTravelHalfClosure

/-!
# Root travel coordinates on the actual closed half intervals

The same root powers and one orientation involution used in the interior
give the genuine closed-strip bijections. The root zero and middle cut are
included; no endpoint inverse value is supplied as a new assumption.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

theorem n04b_rootCoordinate_mapsTo_closed {T : ℝ} (hT : 0 < T) :
    MapsTo n04bRootCoordinate (Icc (0 : ℝ) (T / 2))
      (Icc (0 : ℝ) (n04bRootCutRadius T)) := by
  intro s hs
  have hb : 0 ≤ 3 * s / 2 :=
    div_nonneg (mul_nonneg (by norm_num) hs.1) (by norm_num)
  change 0 ≤ (3 * s / 2) ^ (2 / 3 : ℝ) ∧
    (3 * s / 2) ^ (2 / 3 : ℝ) ≤ (3 * T / 4) ^ (2 / 3 : ℝ)
  exact ⟨Real.rpow_nonneg hb _,
    Real.rpow_le_rpow hb (by linarith [hs.2]) (by norm_num)⟩

theorem n04b_rootTravel_mapsTo_closed {T : ℝ} (hT : 0 < T) :
    MapsTo n04bRootTravel (Icc (0 : ℝ) (n04bRootCutRadius T))
      (Icc (0 : ℝ) (T / 2)) := by
  intro r hr
  refine ⟨mul_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3)
    (Real.rpow_nonneg hr.1 _), ?_⟩
  have hp := Real.rpow_le_rpow hr.1 hr.2 (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hle : n04bRootTravel r ≤ n04bRootTravel (n04bRootCutRadius T) :=
    mul_le_mul_of_nonneg_left hp (by norm_num)
  rwa [n04b_rootTravel_cut hT] at hle

theorem n04bTravelOrientation_mem_closed_iff (T : ℝ) (side : Bool) (s : ℝ) :
    s ∈ n04bClosedTravelHalfInterval T side ↔
      n04bTravelOrientation T side s ∈ Icc (0 : ℝ) (T / 2) := by
  cases side with
  | false => rfl
  | true =>
    change (T / 2 ≤ s ∧ s ≤ T) ↔ (0 ≤ T - s ∧ T - s ≤ T / 2)
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Both actual oriented scalar maps are inverse on their closed intervals. -/
theorem n04b_rootHalf_closed_chart_data {T : ℝ} (hT : 0 < T) (side : Bool) :
    MapsTo (n04bRootHalfCoordinate T side) (n04bClosedTravelHalfInterval T side)
        (Icc (0 : ℝ) (n04bRootCutRadius T)) ∧
      MapsTo (n04bRootHalfTravel T side) (Icc (0 : ℝ) (n04bRootCutRadius T))
        (n04bClosedTravelHalfInterval T side) ∧
      (∀ s ∈ n04bClosedTravelHalfInterval T side,
        n04bRootHalfTravel T side (n04bRootHalfCoordinate T side s) = s) ∧
      (∀ r ∈ Icc (0 : ℝ) (n04bRootCutRadius T),
        n04bRootHalfCoordinate T side (n04bRootHalfTravel T side r) = r) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    exact n04b_rootCoordinate_mapsTo_closed hT
      ((n04bTravelOrientation_mem_closed_iff T side s).mp hs)
  · intro r hr
    apply (n04bTravelOrientation_mem_closed_iff T side _).mpr
    change n04bTravelOrientation T side
      (n04bTravelOrientation T side (n04bRootTravel r)) ∈ Icc (0 : ℝ) (T / 2)
    rw [n04bTravelOrientation_involutive]
    exact n04b_rootTravel_mapsTo_closed hT hr
  · intro s hs
    have hs0 : 0 ≤ n04bTravelOrientation T side s :=
      ((n04bTravelOrientation_mem_closed_iff T side s).mp hs).1
    change n04bTravelOrientation T side
      (n04bRootTravel (n04bRootCoordinate (n04bTravelOrientation T side s))) = s
    rw [n04b_rootTravel_rootCoordinate hs0, n04bTravelOrientation_involutive]
  · intro r hr
    change n04bRootCoordinate (n04bTravelOrientation T side
      (n04bTravelOrientation T side (n04bRootTravel r))) = r
    rw [n04bTravelOrientation_involutive, n04b_rootCoordinate_rootTravel hr.1]

theorem n04b_rootStrip_closed_chart_data {T : ℝ} (hT : 0 < T) (side : Bool) :
    MapsTo (n04bRootStripChart T side)
        (n04bClosedTravelHalfInterval T side ×ˢ (univ : Set ℝ))
        (Icc (0 : ℝ) (n04bRootCutRadius T) ×ˢ univ) ∧
      MapsTo (n04bRootStripInverse T side)
        (Icc (0 : ℝ) (n04bRootCutRadius T) ×ˢ (univ : Set ℝ))
        (n04bClosedTravelHalfInterval T side ×ˢ univ) ∧
      (∀ q ∈ n04bClosedTravelHalfInterval T side ×ˢ (univ : Set ℝ),
        n04bRootStripInverse T side (n04bRootStripChart T side q) = q) ∧
      (∀ p ∈ Icc (0 : ℝ) (n04bRootCutRadius T) ×ˢ (univ : Set ℝ),
        n04bRootStripChart T side (n04bRootStripInverse T side p) = p) := by
  obtain ⟨hc, ht, htc, hct⟩ := n04b_rootHalf_closed_chart_data hT side
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq
    exact ⟨hc hq.1, mem_univ _⟩
  · intro p hp
    exact ⟨ht hp.1, mem_univ _⟩
  · intro q hq
    exact Prod.ext (htc q.1 hq.1) rfl
  · intro p hp
    exact Prod.ext (hct p.1 hp.1) rfl

theorem n04b_rootStrip_closed_bijOn {T : ℝ} (hT : 0 < T) (side : Bool) :
    BijOn (n04bRootStripChart T side)
      (n04bClosedTravelHalfInterval T side ×ˢ (univ : Set ℝ))
      (Icc (0 : ℝ) (n04bRootCutRadius T) ×ˢ univ) := by
  obtain ⟨hc, ht, htc, hct⟩ := n04b_rootStrip_closed_chart_data hT side
  refine ⟨hc, ?_, ?_⟩
  · intro p hp q hq he
    calc
      p = n04bRootStripInverse T side (n04bRootStripChart T side p) := (htc p hp).symm
      _ = n04bRootStripInverse T side (n04bRootStripChart T side q) :=
        congrArg (n04bRootStripInverse T side) he
      _ = q := htc q hq
  · intro q hq
    exact ⟨n04bRootStripInverse T side q, ht hq, hct q hq⟩

end ContinuousFlexibility.Analysis
