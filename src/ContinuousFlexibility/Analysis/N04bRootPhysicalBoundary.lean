import ContinuousFlexibility.Analysis.N04bRootTravelClosed
import ContinuousFlexibility.Analysis.N04bNegativePairGeometry

/-!
# Boundary maps of the constructed physical root charts

The actual closed travel inverse, composed with the explicit root travel,
provides both inverse identities on the proved moving-half closure.
Inside the root strip, and at its positive cut radius, it agrees with the
already constructed physical travel inverse. At root zero its image is
the actual physical endpoint circle.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

/-- The actual maps satisfy all four closed chart identities on the
closure computed from the moving travel domain. -/
theorem n04b_rootPhysical_closure_chart_data
    {F : PolarPoint → PolarPoint} {a b T P : ℝ}
    (hT : 0 < T) (hP : P ≠ 0)
    (hF : ContinuousOn F (Icc a b ×ˢ univ))
    (hInterior : BijOn F (Ioo a b ×ˢ univ) (Ioo (0 : ℝ) T ×ˢ univ))
    (hClosed : BijOn F (Icc a b ×ˢ univ) (Icc (0 : ℝ) T ×ˢ univ))
    (hPeriod : ∀ r ∈ Icc a b, ∀ θ,
      (F (r, θ + P)).2 = (F (r, θ)).2 + P)
    (side : Bool) :
    MapsTo (n04bRootPhysicalChart F T side)
        (closure (n04bTravelHalfDomain (Ioo a b ×ˢ univ) F T side))
        (Icc (0 : ℝ) (n04bRootCutRadius T) ×ˢ univ) ∧
      MapsTo
        (n04bRootPhysicalInverse (Function.invFunOn F (Icc a b ×ˢ univ)) T side)
        (Icc (0 : ℝ) (n04bRootCutRadius T) ×ˢ univ)
        (closure (n04bTravelHalfDomain (Ioo a b ×ˢ univ) F T side)) ∧
      (∀ p ∈ closure (n04bTravelHalfDomain (Ioo a b ×ˢ univ) F T side),
        n04bRootPhysicalInverse (Function.invFunOn F (Icc a b ×ˢ univ)) T side
          (n04bRootPhysicalChart F T side p) = p) ∧
      (∀ q ∈ Icc (0 : ℝ) (n04bRootCutRadius T) ×ˢ (univ : Set ℝ),
        n04bRootPhysicalChart F T side
          (n04bRootPhysicalInverse (Function.invFunOn F (Icc a b ×ˢ univ)) T side q) = q) := by
  rw [n04b_closure_travelHalf hT hP hF hInterior hClosed hPeriod side]
  let G := Function.invFunOn F (Icc a b ×ˢ (univ : Set ℝ))
  have hGF : LeftInvOn G F (Icc a b ×ˢ univ) :=
    hClosed.injOn.leftInvOn_invFunOn
  have hFG : RightInvOn G F (Icc (0 : ℝ) T ×ˢ univ) :=
    hClosed.surjOn.rightInvOn_invFunOn
  have hHalf := n04b_closedTravelHalf_bijOn hT hClosed side
  have hGHalf : MapsTo G (n04bClosedTravelHalfInterval T side ×ˢ univ)
      (n04bTravelDomain (Icc a b ×ˢ univ) F (n04bClosedTravelHalfInterval T side)) := by
    intro q hq
    have hqFull : q ∈ Icc (0 : ℝ) T ×ˢ (univ : Set ℝ) :=
      ⟨n04b_closedTravelHalfInterval_subset hT side hq.1, mem_univ _⟩
    apply mem_n04bTravelDomain.mpr
    refine ⟨hClosed.surjOn.mapsTo_invFunOn hqFull, ?_⟩
    rw [hFG hqFull]
    exact hq.1
  obtain ⟨hc, hi, hic, hci⟩ := n04b_rootStrip_closed_chart_data hT side
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    exact hc (hHalf.mapsTo hp)
  · intro q hq
    exact hGHalf (hi hq)
  · intro p hp
    change G (n04bRootStripInverse T side (n04bRootStripChart T side (F p))) = p
    rw [hic (F p) (hHalf.mapsTo hp)]
    exact hGF (mem_n04bTravelDomain.mp hp).1
  · intro q hq
    have hqHalf := hi hq
    have hqFull : n04bRootStripInverse T side q ∈
        Icc (0 : ℝ) T ×ˢ (univ : Set ℝ) :=
      ⟨n04b_closedTravelHalfInterval_subset hT side hqHalf.1, mem_univ _⟩
    change n04bRootStripChart T side (F (G (n04bRootStripInverse T side q))) = q
    rw [hFG hqFull]
    exact hci q hq

theorem n04b_closedRootPhysicalInverse_eq_interior
    {F X : PolarPoint → PolarPoint} {a b T : ℝ}
    (hT : 0 < T)
    (hClosed : BijOn F (Icc a b ×ˢ univ) (Icc (0 : ℝ) T ×ˢ univ))
    (hX : MapsTo X (Ioo (0 : ℝ) T ×ˢ univ) (Ioo a b ×ˢ univ))
    (hFX : RightInvOn X F (Ioo (0 : ℝ) T ×ˢ univ))
    (side : Bool) :
    EqOn
      (n04bRootPhysicalInverse (Function.invFunOn F (Icc a b ×ˢ univ)) T side)
      (n04bRootPhysicalInverse X T side)
      (Ioo (0 : ℝ) (n04bRootCutRadius T) ×ˢ univ) := by
  intro q hq
  have ht := (n04b_rootStrip_chart_data hT side).2.1 hq
  have htFull : n04bRootStripInverse T side q ∈
      Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ) :=
    ⟨n04b_travelHalfInterval_subset hT side ht.1, mem_univ _⟩
  exact n04b_closedTravelInverse_eq_interior hClosed hX hFX htFull

/-- The positive boundary radius is the genuine moving cut of the
existing physical travel inverse. -/
theorem n04b_closedRootPhysicalInverse_at_cut
    {F X : PolarPoint → PolarPoint} {a b T : ℝ}
    (hT : 0 < T)
    (hClosed : BijOn F (Icc a b ×ˢ univ) (Icc (0 : ℝ) T ×ˢ univ))
    (hX : MapsTo X (Ioo (0 : ℝ) T ×ˢ univ) (Ioo a b ×ˢ univ))
    (hFX : RightInvOn X F (Ioo (0 : ℝ) T ×ˢ univ))
    (side : Bool) (θ : ℝ) :
    n04bRootPhysicalInverse (Function.invFunOn F (Icc a b ×ˢ univ))
      T side (n04bRootCutRadius T, θ) = X (T / 2, θ) := by
  rw [n04b_rootPhysicalInverse_at_cut _ hT side θ]
  exact n04b_closedTravelInverse_eq_interior hClosed hX hFX
    ⟨⟨half_pos hT, half_lt_self hT⟩, mem_univ _⟩

/-- The zero boundary image is deduced from its actual forward boundary
circle lift. The same theorem treats the left and right orientations. -/
theorem n04b_closedRootPhysicalInverse_zero_image
    {F : PolarPoint → PolarPoint} {h : ℝ → ℝ} {a b T r : ℝ}
    (side : Bool)
    (hClosed : BijOn F (Icc a b ×ˢ univ) (Icc (0 : ℝ) T ×ˢ univ))
    (hr : r ∈ Icc a b)
    (hEndpoint : ∀ θ, F (r, θ) = (if side then T else 0, h θ))
    (hh : Function.Bijective h) :
    n04bRootPhysicalInverse (Function.invFunOn F (Icc a b ×ˢ univ)) T side ''
        ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) =
      ({r} : Set ℝ) ×ˢ univ := by
  rw [n04bRootPhysicalInverse_zero_image]
  exact n04b_closedTravelInverse_image_endpoint hClosed hr hEndpoint hh

end ContinuousFlexibility.Analysis
