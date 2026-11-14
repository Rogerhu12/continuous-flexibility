module

public import ContinuousFlexibility.Analysis.N04bRootLiteralMaps
public import ContinuousFlexibility.Analysis.N04bRootTravelClosed
public import ContinuousFlexibility.Analysis.N04bRootTravelDifferential

/-!
# Root-radius bounds identify the actual moving half

The coordinate bound is applied to the literal travel chart. It yields
membership of the genuine moving half, rather than of a preassigned
radial rectangle. The closure can meet only its own physical root.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

theorem n04b_mem_travelHalf_of_rootCoordinate_mem
    {Ω : Set PolarPoint} {F : PolarPoint → PolarPoint} {T : ℝ}
    (hT : 0 < T) (side : Bool)
    (hF : MapsTo F Ω (Ioo (0 : ℝ) T ×ˢ univ))
    {p : PolarPoint} (hp : p ∈ Ω)
    (hRoot : (n04bRootPhysicalChart F T side p).1 ∈
      Ioo (0 : ℝ) (n04bRootCutRadius T)) :
    p ∈ n04bTravelHalfDomain Ω F T side := by
  have hs0 : 0 ≤ n04bTravelOrientation T side (F p).1 := by
    cases side with
    | false => exact (hF hp).1.1.le
    | true => exact (sub_pos.mpr (hF hp).1.2).le
  have hTravel := n04b_rootTravel_mapsTo hT hRoot
  change n04bRootTravel (n04bRootCoordinate
    (n04bTravelOrientation T side (F p).1)) ∈ Ioo (0 : ℝ) (T / 2) at hTravel
  rw [n04b_rootTravel_rootCoordinate hs0] at hTravel
  exact mem_n04bTravelDomain.mpr
    ⟨hp, (n04bTravelOrientation_mem_iff T side (F p).1).mpr hTravel⟩

theorem n04bRootAffine_first_pos_of_interior
    {a b : ℝ} (side : Bool) {p : PolarPoint}
    (hp : p ∈ Ioo a b ×ˢ (univ : Set ℝ)) :
    0 < (n04bRootAffine (if side then b else a) side p).1 := by
  cases side with
  | false => exact sub_pos.mpr hp.1.1
  | true => exact sub_pos.mpr hp.1.2

/-- Positive closed root radii, including the cut, correspond to points
strictly inside the full travel strip. -/
theorem n04b_rootStripInverse_mem_full_of_pos
    {T : ℝ} (hT : 0 < T) (side : Bool) {q : PolarPoint}
    (hq : q.1 ∈ Ioc (0 : ℝ) (n04bRootCutRadius T)) :
    n04bRootStripInverse T side q ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ) := by
  have ht := n04b_rootTravel_mapsTo_closed hT ⟨hq.1.le, hq.2⟩
  have htpos : 0 < n04bRootTravel q.1 :=
    mul_pos (by norm_num : (0 : ℝ) < 2 / 3) (Real.rpow_pos_of_pos hq.1 _)
  cases side with
  | false =>
    exact ⟨⟨htpos, by change n04bRootTravel q.1 < T; linarith [ht.2]⟩, mem_univ _⟩
  | true =>
    exact ⟨⟨by change 0 < T - n04bRootTravel q.1; linarith [ht.2],
      by change T - n04bRootTravel q.1 < T; linarith⟩, mem_univ _⟩

theorem n04b_closedTravelHalf_root_or_interior
    {F : PolarPoint → PolarPoint} {a b T : ℝ}
    (hT : 0 < T) (side : Bool)
    (hLeft : ∀ θ, (F (a, θ)).1 = 0)
    (hRight : ∀ θ, (F (b, θ)).1 = T)
    {p : PolarPoint}
    (hp : p ∈ n04bTravelDomain (Icc a b ×ˢ univ) F
      (n04bClosedTravelHalfInterval T side)) :
    p.1 = (if side then b else a) ∨ p ∈ Ioo a b ×ˢ (univ : Set ℝ) := by
  obtain ⟨hpc, ht⟩ := mem_n04bTravelDomain.mp hp
  cases side with
  | false =>
    by_cases ha : p.1 = a
    · exact Or.inl ha
    have hb : p.1 ≠ b := by
      intro he
      have hpoint : p = (b, p.2) := Prod.ext he rfl
      have hbound : (F p).1 ≤ T / 2 := ht.2
      rw [hpoint, hRight] at hbound
      linarith
    exact Or.inr ⟨⟨lt_of_le_of_ne hpc.1.1 (fun he => ha he.symm),
      lt_of_le_of_ne hpc.1.2 hb⟩, mem_univ _⟩
  | true =>
    by_cases hb : p.1 = b
    · exact Or.inl hb
    have ha : p.1 ≠ a := by
      intro he
      have hpoint : p = (a, p.2) := Prod.ext he rfl
      have hbound : T / 2 ≤ (F p).1 := ht.1
      rw [hpoint, hLeft] at hbound
      linarith
    exact Or.inr ⟨⟨lt_of_le_of_ne hpc.1.1 (fun he => ha he.symm),
      lt_of_le_of_ne hpc.1.2 hb⟩, mem_univ _⟩

end ContinuousFlexibility.Analysis
