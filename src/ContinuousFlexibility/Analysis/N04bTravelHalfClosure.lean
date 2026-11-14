module

public import ContinuousFlexibility.Analysis.N04bClosedTravelInverse

/-!
# Exact closures of the actual moving travel halves

A closed travel inverse is constructed on the closed physical strip.
Its continuity follows from the actual lifted period. Approaching a
closed target substrip through its open interior and applying that
inverse proves the reverse closure inclusion. Thus no radial graph
assumption and no preassigned half-domain closure is needed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

/-- Closure commutes with restriction to any nondegenerate travel
subinterval whose endpoints lie in the full closed travel interval. -/
theorem n04b_closure_travelSubstrip
    {F : PolarPoint → PolarPoint} {a b T P c d : ℝ}
    (hP : P ≠ 0)
    (hF : ContinuousOn F (Icc a b ×ˢ univ))
    (hInterior : BijOn F (Ioo a b ×ˢ univ) (Ioo (0 : ℝ) T ×ˢ univ))
    (hClosed : BijOn F (Icc a b ×ˢ univ) (Icc (0 : ℝ) T ×ˢ univ))
    (hPeriod : ∀ r ∈ Icc a b, ∀ θ,
      (F (r, θ + P)).2 = (F (r, θ)).2 + P)
    (hcd : c < d) (hc : 0 ≤ c) (hd : d ≤ T) :
    closure (n04bTravelDomain (Ioo a b ×ˢ univ) F (Ioo c d)) =
      n04bTravelDomain (Icc a b ×ˢ univ) F (Icc c d) := by
  let G := Function.invFunOn F (Icc a b ×ˢ (univ : Set ℝ))
  have hGF : LeftInvOn G F (Icc a b ×ˢ univ) :=
    hClosed.injOn.leftInvOn_invFunOn
  have hFG : RightInvOn G F (Icc (0 : ℝ) T ×ˢ univ) :=
    hClosed.surjOn.rightInvOn_invFunOn
  have hGc : ContinuousOn G (Icc (0 : ℝ) T ×ˢ univ) :=
    n04b_closedTravelInverse_continuous hP hF hClosed hPeriod
  have hOpenSub : Ioo c d ×ˢ (univ : Set ℝ) ⊆
      Ioo (0 : ℝ) T ×ˢ univ := by
    intro q hq
    exact ⟨⟨lt_of_le_of_lt hc hq.1.1, lt_of_lt_of_le hq.1.2 hd⟩, mem_univ _⟩
  have hOpenClosed : Ioo c d ×ˢ (univ : Set ℝ) ⊆
      Icc (0 : ℝ) T ×ˢ univ := by
    intro q hq
    have h := hOpenSub hq
    exact ⟨⟨h.1.1.le, h.1.2.le⟩, mem_univ _⟩
  have hGHalf : MapsTo G (Ioo c d ×ˢ univ)
      (n04bTravelDomain (Ioo a b ×ˢ univ) F (Ioo c d)) := by
    intro q hq
    obtain ⟨p, hp, hpq⟩ := hInterior.surjOn (hOpenSub hq)
    have hpc : p ∈ Icc a b ×ˢ (univ : Set ℝ) :=
      ⟨⟨hp.1.1.le, hp.1.2.le⟩, mem_univ _⟩
    have he : G q = p := by
      rw [← hpq]
      exact hGF hpc
    apply mem_n04bTravelDomain.mpr
    refine ⟨?_, ?_⟩
    · rw [he]
      exact hp
    · rw [hFG (hOpenClosed hq)]
      exact hq.1
  have hDclosed : IsClosed (n04bTravelDomain (Icc a b ×ˢ univ) F (Icc c d)) :=
    hF.preimage_isClosed_of_isClosed (isClosed_Icc.prod isClosed_univ)
      (isClosed_Icc.prod isClosed_univ)
  apply Subset.antisymm
  · apply closure_minimal ?_ hDclosed
    intro p hp
    obtain ⟨hp, ht⟩ := mem_n04bTravelDomain.mp hp
    exact mem_n04bTravelDomain.mpr
      ⟨⟨⟨hp.1.1.le, hp.1.2.le⟩, mem_univ _⟩, ht.1.le, ht.2.le⟩
  · intro p hp
    obtain ⟨hp, ht⟩ := mem_n04bTravelDomain.mp hp
    have hTarget : F p ∈ closure (Ioo c d ×ˢ (univ : Set ℝ)) := by
      rw [closure_prod_eq, closure_Ioo hcd.ne, closure_univ]
      exact ⟨ht, mem_univ _⟩
    have hCont : ContinuousWithinAt G (Ioo c d ×ˢ univ) (F p) :=
      (hGc (F p) (hClosed.mapsTo hp)).mono hOpenClosed
    have hMem := hCont.mem_closure hTarget hGHalf
    rwa [hGF hp] at hMem

/-- Both closed half intervals are treated by the same side parameter
as the actual open half-domains. -/
def n04bClosedTravelHalfInterval (T : ℝ) : Bool → Set ℝ
  | false => Icc 0 (T / 2)
  | true => Icc (T / 2) T

theorem n04b_closedTravelHalfInterval_subset {T : ℝ}
    (hT : 0 < T) (side : Bool) :
    n04bClosedTravelHalfInterval T side ⊆ Icc (0 : ℝ) T := by
  intro s hs
  cases side with
  | false =>
    change 0 ≤ s ∧ s ≤ T / 2 at hs
    exact ⟨hs.1, by linarith [hs.2]⟩
  | true =>
    change T / 2 ≤ s ∧ s ≤ T at hs
    exact ⟨by linarith [hs.1], hs.2⟩

theorem n04b_closure_travelHalfInterval {T : ℝ}
    (hT : 0 < T) (side : Bool) :
    closure (n04bTravelHalfInterval T side) =
      n04bClosedTravelHalfInterval T side := by
  cases side with
  | false => exact closure_Ioo (by linarith : (0 : ℝ) ≠ T / 2)
  | true => exact closure_Ioo (by linarith : T / 2 ≠ T)

theorem n04b_closedTravelHalf_bijOn
    {F : PolarPoint → PolarPoint} {a b T : ℝ}
    (hT : 0 < T)
    (hClosed : BijOn F (Icc a b ×ˢ univ) (Icc (0 : ℝ) T ×ˢ univ))
    (side : Bool) :
    BijOn F
      (n04bTravelDomain (Icc a b ×ˢ univ) F (n04bClosedTravelHalfInterval T side))
      (n04bClosedTravelHalfInterval T side ×ˢ univ) :=
  hClosed.subset_right
    (Set.prod_mono (n04b_closedTravelHalfInterval_subset hT side) (Subset.rfl))

/-- The closure is exactly the closed physical strip with travel time in
the appropriate closed half, including the physical root and moving cut. -/
theorem n04b_closure_travelHalf
    {F : PolarPoint → PolarPoint} {a b T P : ℝ}
    (hT : 0 < T) (hP : P ≠ 0)
    (hF : ContinuousOn F (Icc a b ×ˢ univ))
    (hInterior : BijOn F (Ioo a b ×ˢ univ) (Ioo (0 : ℝ) T ×ˢ univ))
    (hClosed : BijOn F (Icc a b ×ˢ univ) (Icc (0 : ℝ) T ×ˢ univ))
    (hPeriod : ∀ r ∈ Icc a b, ∀ θ,
      (F (r, θ + P)).2 = (F (r, θ)).2 + P)
    (side : Bool) :
    closure (n04bTravelHalfDomain (Ioo a b ×ˢ univ) F T side) =
      n04bTravelDomain (Icc a b ×ˢ univ) F (n04bClosedTravelHalfInterval T side) := by
  cases side with
  | false =>
    exact n04b_closure_travelSubstrip hP hF hInterior hClosed hPeriod
      (by linarith : (0 : ℝ) < T / 2) le_rfl (by linarith)
  | true =>
    exact n04b_closure_travelSubstrip hP hF hInterior hClosed hPeriod
      (by linarith : T / 2 < T) (by linarith) le_rfl

theorem n04b_bijOn_closure_travelHalf
    {F : PolarPoint → PolarPoint} {a b T P : ℝ}
    (hT : 0 < T) (hP : P ≠ 0)
    (hF : ContinuousOn F (Icc a b ×ˢ univ))
    (hInterior : BijOn F (Ioo a b ×ˢ univ) (Ioo (0 : ℝ) T ×ˢ univ))
    (hClosed : BijOn F (Icc a b ×ˢ univ) (Icc (0 : ℝ) T ×ˢ univ))
    (hPeriod : ∀ r ∈ Icc a b, ∀ θ,
      (F (r, θ + P)).2 = (F (r, θ)).2 + P)
    (side : Bool) :
    BijOn F (closure (n04bTravelHalfDomain (Ioo a b ×ˢ univ) F T side))
      (n04bClosedTravelHalfInterval T side ×ˢ univ) := by
  rw [n04b_closure_travelHalf hT hP hF hInterior hClosed hPeriod side]
  exact n04b_closedTravelHalf_bijOn hT hClosed side

end ContinuousFlexibility.Analysis
