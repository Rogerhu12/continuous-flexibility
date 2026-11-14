module

public import ContinuousFlexibility.Analysis.N04bRootTravelIntervals

/-!
# Actual root charts on moving travel half-domains

The scalar root-coordinate bijection is applied to the first travel
coordinate. Composing with a genuine travel chart and its specified inverse
gives actual forward and inverse maps on each moving physical half.

Both orientations use one Bool parameter. The global inverse formula agrees
with the signed travel pullback already used by the root-height transmission
lemmas, so its common cut is the actual point X(T/2, θ).
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

def n04bRootStripChart (T : ℝ) (side : Bool) (q : PolarPoint) : PolarPoint :=
  (n04bRootHalfCoordinate T side q.1, q.2)

def n04bRootStripInverse (T : ℝ) (side : Bool) (p : PolarPoint) : PolarPoint :=
  (n04bRootHalfTravel T side p.1, p.2)

/-- The actual two-dimensional root maps are inverse on their open strips. -/
theorem n04b_rootStrip_chart_data {T : ℝ} (hT : 0 < T) (side : Bool) :
    MapsTo (n04bRootStripChart T side)
        (n04bTravelHalfInterval T side ×ˢ (univ : Set ℝ))
        (Ioo (0 : ℝ) (n04bRootCutRadius T) ×ˢ (univ : Set ℝ)) ∧
      MapsTo (n04bRootStripInverse T side)
        (Ioo (0 : ℝ) (n04bRootCutRadius T) ×ˢ (univ : Set ℝ))
        (n04bTravelHalfInterval T side ×ˢ (univ : Set ℝ)) ∧
      (∀ q ∈ n04bTravelHalfInterval T side ×ˢ (univ : Set ℝ),
        n04bRootStripInverse T side (n04bRootStripChart T side q) = q) ∧
      (∀ p ∈ Ioo (0 : ℝ) (n04bRootCutRadius T) ×ˢ (univ : Set ℝ),
        n04bRootStripChart T side (n04bRootStripInverse T side p) = p) := by
  obtain ⟨hc, ht, htc, hct⟩ := n04b_rootHalf_chart_data hT side
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq
    exact ⟨hc hq.1, mem_univ _⟩
  · intro p hp
    exact ⟨ht hp.1, mem_univ _⟩
  · intro q hq
    exact Prod.ext (htc q.1 hq.1) rfl
  · intro p hp
    exact Prod.ext (hct p.1 hp.1) rfl

theorem n04b_rootStrip_bijOn {T : ℝ} (hT : 0 < T) (side : Bool) :
    BijOn (n04bRootStripChart T side)
      (n04bTravelHalfInterval T side ×ˢ (univ : Set ℝ))
      (Ioo (0 : ℝ) (n04bRootCutRadius T) ×ˢ (univ : Set ℝ)) := by
  obtain ⟨hc, ht, htc, hct⟩ := n04b_rootStrip_chart_data hT side
  exact n04b_bijOn_of_travel_inverse hc ht htc hct

/-- This is the same actual inverse coordinate used in the root-height
and canonical-cut transmission lemmas, for both signs. -/
theorem n04bRootStripInverse_eq_signedTravel (T : ℝ) (side : Bool) :
    n04bRootStripInverse T side =
      n04bSignedTravel T (if side then -1 else 1) n04bRootTravel := by
  funext p
  cases side <;> apply Prod.ext <;>
    simp [n04bRootStripInverse, n04bRootHalfTravel,
      n04bTravelOrientation, n04bSignedTravel] <;> ring

def n04bRootPhysicalChart (F : PolarPoint → PolarPoint)
    (T : ℝ) (side : Bool) (p : PolarPoint) : PolarPoint :=
  n04bRootStripChart T side (F p)

def n04bRootPhysicalInverse (X : PolarPoint → PolarPoint)
    (T : ℝ) (side : Bool) (p : PolarPoint) : PolarPoint :=
  X (n04bRootStripInverse T side p)

theorem n04bRootPhysicalInverse_eq_signedTravel
    (X : PolarPoint → PolarPoint) (T : ℝ) (side : Bool) :
    n04bRootPhysicalInverse X T side =
      (fun p => X (n04bSignedTravel T (if side then -1 else 1) n04bRootTravel p)) := by
  funext p
  exact congrArg X (congrFun (n04bRootStripInverse_eq_signedTravel T side) p)

/-- A genuine travel chart and its actual inverse induce root charts on
the actual moving halves, with both inverse identities proved there. -/
theorem n04b_rootPhysical_chart_data
    {Ω : Set PolarPoint} {F X : PolarPoint → PolarPoint} {T : ℝ}
    (hT : 0 < T)
    (hF : MapsTo F Ω (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)))
    (hX : MapsTo X (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)) Ω)
    (hXF : ∀ p ∈ Ω, X (F p) = p)
    (hFX : ∀ q ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ), F (X q) = q)
    (side : Bool) :
    MapsTo (n04bRootPhysicalChart F T side) (n04bTravelHalfDomain Ω F T side)
        (Ioo (0 : ℝ) (n04bRootCutRadius T) ×ˢ (univ : Set ℝ)) ∧
      MapsTo (n04bRootPhysicalInverse X T side)
        (Ioo (0 : ℝ) (n04bRootCutRadius T) ×ˢ (univ : Set ℝ))
        (n04bTravelHalfDomain Ω F T side) ∧
      (∀ p ∈ n04bTravelHalfDomain Ω F T side,
        n04bRootPhysicalInverse X T side (n04bRootPhysicalChart F T side p) = p) ∧
      (∀ q ∈ Ioo (0 : ℝ) (n04bRootCutRadius T) ×ˢ (univ : Set ℝ),
        n04bRootPhysicalChart F T side (n04bRootPhysicalInverse X T side q) = q) := by
  have hbij := n04b_bijOn_of_travel_inverse hF hX hXF hFX
  have hhalf := (n04b_bijOn_travelHalf hT hbij side).mapsTo
  have hXhalf := n04b_inverse_mapsTo_travelHalf hT hX hFX side
  obtain ⟨hc, hi, hic, hci⟩ := n04b_rootStrip_chart_data hT side
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    exact hc (hhalf hp)
  · intro q hq
    exact hXhalf (hi hq)
  · intro p hp
    have hpΩ : p ∈ Ω := (mem_n04bTravelDomain.mp hp).1
    change X (n04bRootStripInverse T side (n04bRootStripChart T side (F p))) = p
    rw [hic (F p) (hhalf hp)]
    exact hXF p hpΩ
  · intro q hq
    have hqhalf := hi hq
    have hqfull : n04bRootStripInverse T side q ∈
        Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ) :=
      ⟨n04b_travelHalfInterval_subset hT side hqhalf.1, hqhalf.2⟩
    change n04bRootStripChart T side (F (X (n04bRootStripInverse T side q))) = q
    rw [hFX _ hqfull]
    exact hci q hq

theorem n04b_rootPhysical_bijOn
    {Ω : Set PolarPoint} {F X : PolarPoint → PolarPoint} {T : ℝ}
    (hT : 0 < T)
    (hF : MapsTo F Ω (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)))
    (hX : MapsTo X (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)) Ω)
    (hXF : ∀ p ∈ Ω, X (F p) = p)
    (hFX : ∀ q ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ), F (X q) = q)
    (side : Bool) :
    BijOn (n04bRootPhysicalChart F T side) (n04bTravelHalfDomain Ω F T side)
      (Ioo (0 : ℝ) (n04bRootCutRadius T) ×ˢ (univ : Set ℝ)) := by
  obtain ⟨hc, hi, hic, hci⟩ := n04b_rootPhysical_chart_data hT hF hX hXF hFX side
  exact n04b_bijOn_of_travel_inverse hc hi hic hci

/-- The common positive root radius maps to the genuine moving cut. -/
theorem n04b_rootPhysicalInverse_at_cut
    (X : PolarPoint → PolarPoint) {T : ℝ} (hT : 0 < T)
    (side : Bool) (θ : ℝ) :
    n04bRootPhysicalInverse X T side (n04bRootCutRadius T, θ) = X (T / 2, θ) := by
  rw [n04bRootPhysicalInverse_eq_signedTravel X T side]
  simp only [n04bSignedTravel, n04b_rootTravel_cut hT,
    sub_self, mul_zero, add_zero]

end ContinuousFlexibility.Analysis
