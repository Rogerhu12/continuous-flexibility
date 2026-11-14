module

public import ContinuousFlexibility.Analysis.N04bRootCutPowers
public import ContinuousFlexibility.Analysis.N04bMovingDomains

/-!
# The actual root coordinate on either travel half

The root coordinate (3s/2)^(2/3) and the already defined root travel
(2/3)ξ^(3/2) are genuine inverses on their positive intervals.
One involution treats the two travel orientations uniformly.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

/-- The forward root coordinate, inverse to the actual root travel. -/
def n04bRootCoordinate (s : ℝ) : ℝ := (3 * s / 2) ^ (2 / 3 : ℝ)

theorem n04b_rootTravel_rootCoordinate {s : ℝ} (hs : 0 ≤ s) :
    n04bRootTravel (n04bRootCoordinate s) = s := by
  have hb : 0 ≤ 3 * s / 2 := by positivity
  unfold n04bRootTravel n04bRootCoordinate
  rw [← Real.rpow_mul hb]
  norm_num <;> ring

theorem n04b_rootCoordinate_rootTravel {r : ℝ} (hr : 0 ≤ r) :
    n04bRootCoordinate (n04bRootTravel r) = r := by
  unfold n04bRootCoordinate n04bRootTravel
  rw [show 3 * ((2 / 3 : ℝ) * r ^ (3 / 2 : ℝ)) / 2 =
    r ^ (3 / 2 : ℝ) by ring]
  rw [← Real.rpow_mul hr]
  norm_num

theorem n04b_rootCoordinate_middle (T : ℝ) :
    n04bRootCoordinate (T / 2) = n04bRootCutRadius T := by
  unfold n04bRootCoordinate n04bRootCutRadius
  congr 1 <;> ring

theorem n04b_rootCoordinate_mapsTo {T : ℝ} (hT : 0 < T) :
    MapsTo n04bRootCoordinate (Ioo (0 : ℝ) (T / 2))
      (Ioo (0 : ℝ) (n04bRootCutRadius T)) := by
  intro s hs
  have hb : 0 < 3 * s / 2 := by linarith [hs.1]
  change 0 < (3 * s / 2) ^ (2 / 3 : ℝ) ∧
    (3 * s / 2) ^ (2 / 3 : ℝ) < (3 * T / 4) ^ (2 / 3 : ℝ)
  exact ⟨Real.rpow_pos_of_pos hb _,
    Real.rpow_lt_rpow hb.le (by linarith [hs.2]) (by norm_num)⟩

theorem n04b_rootTravel_mapsTo {T : ℝ} (hT : 0 < T) :
    MapsTo n04bRootTravel (Ioo (0 : ℝ) (n04bRootCutRadius T))
      (Ioo (0 : ℝ) (T / 2)) := by
  intro r hr
  refine ⟨?_, ?_⟩
  · exact mul_pos (by norm_num : (0 : ℝ) < 2 / 3)
      (Real.rpow_pos_of_pos hr.1 _)
  · have hpow := Real.rpow_lt_rpow hr.1.le hr.2
      (by norm_num : (0 : ℝ) < 3 / 2)
    have hlt : n04bRootTravel r < n04bRootTravel (n04bRootCutRadius T) :=
      mul_lt_mul_of_pos_left hpow (by norm_num)
    rw [n04b_rootTravel_cut hT] at hlt
    exact hlt

/-- Left travel is unchanged; right travel is measured from T. -/
def n04bTravelOrientation (T : ℝ) (side : Bool) (s : ℝ) : ℝ :=
  if side then T - s else s

theorem n04bTravelOrientation_involutive (T : ℝ) (side : Bool) (s : ℝ) :
    n04bTravelOrientation T side (n04bTravelOrientation T side s) = s := by
  cases side <;> simp [n04bTravelOrientation] <;> ring

theorem n04bTravelOrientation_mem_iff (T : ℝ) (side : Bool) (s : ℝ) :
    s ∈ n04bTravelHalfInterval T side ↔
      n04bTravelOrientation T side s ∈ Ioo (0 : ℝ) (T / 2) := by
  cases side with
  | false => rfl
  | true =>
    change (T / 2 < s ∧ s < T) ↔ (0 < T - s ∧ T - s < T / 2)
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem n04bTravelOrientation_mem_half
    {T s : ℝ} (side : Bool) (hs : s ∈ Ioo (0 : ℝ) (T / 2)) :
    n04bTravelOrientation T side s ∈ n04bTravelHalfInterval T side := by
  apply (n04bTravelOrientation_mem_iff T side _).mpr
  simpa only [n04bTravelOrientation_involutive] using hs

def n04bRootHalfCoordinate (T : ℝ) (side : Bool) (s : ℝ) : ℝ :=
  n04bRootCoordinate (n04bTravelOrientation T side s)

def n04bRootHalfTravel (T : ℝ) (side : Bool) (r : ℝ) : ℝ :=
  n04bTravelOrientation T side (n04bRootTravel r)

/-- Both oriented root maps carry the actual open intervals into each
other and satisfy both inverse identities there. -/
theorem n04b_rootHalf_chart_data {T : ℝ} (hT : 0 < T) (side : Bool) :
    MapsTo (n04bRootHalfCoordinate T side) (n04bTravelHalfInterval T side)
        (Ioo (0 : ℝ) (n04bRootCutRadius T)) ∧
      MapsTo (n04bRootHalfTravel T side) (Ioo (0 : ℝ) (n04bRootCutRadius T))
        (n04bTravelHalfInterval T side) ∧
      (∀ s ∈ n04bTravelHalfInterval T side,
        n04bRootHalfTravel T side (n04bRootHalfCoordinate T side s) = s) ∧
      (∀ r ∈ Ioo (0 : ℝ) (n04bRootCutRadius T),
        n04bRootHalfCoordinate T side (n04bRootHalfTravel T side r) = r) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    exact n04b_rootCoordinate_mapsTo hT
      ((n04bTravelOrientation_mem_iff T side s).mp hs)
  · intro r hr
    exact n04bTravelOrientation_mem_half side (n04b_rootTravel_mapsTo hT hr)
  · intro s hs
    have hs0 : 0 ≤ n04bTravelOrientation T side s :=
      ((n04bTravelOrientation_mem_iff T side s).mp hs).1.le
    change n04bTravelOrientation T side
      (n04bRootTravel (n04bRootCoordinate (n04bTravelOrientation T side s))) = s
    rw [n04b_rootTravel_rootCoordinate hs0, n04bTravelOrientation_involutive]
  · intro r hr
    change n04bRootCoordinate (n04bTravelOrientation T side
      (n04bTravelOrientation T side (n04bRootTravel r))) = r
    rw [n04bTravelOrientation_involutive, n04b_rootCoordinate_rootTravel hr.1.le]

theorem n04b_rootHalfCoordinate_bijOn {T : ℝ} (hT : 0 < T) (side : Bool) :
    BijOn (n04bRootHalfCoordinate T side) (n04bTravelHalfInterval T side)
      (Ioo (0 : ℝ) (n04bRootCutRadius T)) := by
  obtain ⟨hc, ht, htc, hct⟩ := n04b_rootHalf_chart_data hT side
  refine ⟨hc, ?_, ?_⟩
  · intro s hs t ht he
    exact (htc s hs).symm.trans
      ((congrArg (n04bRootHalfTravel T side) he).trans (htc t ht))
  · intro r hr
    exact ⟨n04bRootHalfTravel T side r, ht hr, hct r hr⟩

theorem n04b_rootHalfTravel_bijOn {T : ℝ} (hT : 0 < T) (side : Bool) :
    BijOn (n04bRootHalfTravel T side) (Ioo (0 : ℝ) (n04bRootCutRadius T))
      (n04bTravelHalfInterval T side) := by
  obtain ⟨hc, ht, htc, hct⟩ := n04b_rootHalf_chart_data hT side
  refine ⟨ht, ?_, ?_⟩
  · intro r hr q hq he
    exact (hct r hr).symm.trans
      ((congrArg (n04bRootHalfCoordinate T side) he).trans (hct q hq))
  · intro s hs
    exact ⟨n04bRootHalfCoordinate T side s, hc hs, htc s hs⟩

end ContinuousFlexibility.Analysis
