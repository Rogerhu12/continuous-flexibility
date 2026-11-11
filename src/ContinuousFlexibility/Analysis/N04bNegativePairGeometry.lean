import ContinuousFlexibility.Analysis.N04bRootTravelCharts
import ContinuousFlexibility.Analysis.N04bCutCurve
import ContinuousFlexibility.Statements.Nonlinear

/-!
# Current cut geometry of a constructed negative pair

The two stored physical pieces are actual travel halves, and their stored
inverses agree with the root inverses on the closed canonical strips. Their middle traces, disjointness,
coverage and endpoint-circle images then give the six current-cut fields.
All geometric conclusions come from a genuine travel bijection.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04bRootStripInverse_zero_image (T : ℝ) (side : Bool) :
    n04bRootStripInverse T side '' ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) =
      ({if side then T else 0} ×ˢ (univ : Set ℝ)) := by
  have hz (θ : ℝ) :
      n04bRootStripInverse T side (0, θ) = (if side then T else 0, θ) := by
    cases side <;> norm_num [n04bRootStripInverse, n04bRootHalfTravel,
      n04bTravelOrientation, n04bRootTravel]
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp0 : p.1 = 0 := mem_singleton_iff.mp hp.1
    have he : p = (0, p.2) := Prod.ext hp0 rfl
    rw [he, hz]
    exact ⟨mem_singleton _, mem_univ _⟩
  · intro hq
    refine ⟨(0, q.2), ⟨mem_singleton _, mem_univ _⟩, ?_⟩
    rw [hz]
    exact Prod.ext (mem_singleton_iff.mp hq.1).symm rfl

/-- Root zero is the original left or right travel endpoint, uniformly
in the orientation parameter. -/
theorem n04bRootPhysicalInverse_zero_image
    (X : PolarPoint → PolarPoint) (T : ℝ) (side : Bool) :
    n04bRootPhysicalInverse X T side '' ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) =
      X '' ({if side then T else 0} ×ˢ (univ : Set ℝ)) := by
  simpa only [n04bRootPhysicalInverse, image_image, Function.comp_def] using
    congrArg (fun E : Set PolarPoint => X '' E)
      (n04bRootStripInverse_zero_image T side)

/-- The stored cut is exactly the moving middle-travel inverse curve. -/
theorem n04b_canonicalCutPoint_of_constructedRoot
    {S : PhysicalSpacesData} (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (piece : Bool → ℕ)
    (X : PolarPoint → PolarPoint) {T : ℝ} (hT : 0 < T)
    (hPair : K.cutPair m = (piece false, piece true))
    (hRadius : K.cutRadius m = n04bRootCutRadius T)
    (hInverse : ∀ side : Bool,
      EqOn (K.inverseChart z (piece side)) (n04bRootPhysicalInverse X T side)
        (Icc (0 : ℝ) (n04bRootCutRadius T) ×ˢ (univ : Set ℝ))) :
    canonicalCutPoint S K z m = fun θ : ℝ => X (T / 2, θ) := by
  funext θ
  simp only [canonicalCutPoint, hPair, hRadius]
  exact (hInverse false ⟨⟨(n04bRootCutRadius_pos hT).le, le_rfl⟩, mem_univ θ⟩).trans
    (n04b_rootPhysicalInverse_at_cut X hT false θ)

/-- Genuine strip-bijection and endpoint-image data assemble the exact
six-field current-cut contract for the actual constructor record. -/
theorem n04b_currentCutPair_of_constructedRoot
    {S : PhysicalSpacesData} (C : NonlinearGeometryData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (piece : Bool → ℕ)
    {F X : PolarPoint → PolarPoint} {T : ℝ} (hT : 0 < T)
    (hF : BijOn F (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
      (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)))
    (hX : MapsTo X (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ))
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)))
    (hFX : ∀ q ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ), F (X q) = q)
    (hEndpoints : ∀ side : Bool,
      X '' ({if side then T else 0} ×ˢ (univ : Set ℝ)) =
        ({if side then C.right m else C.left m} ×ˢ (univ : Set ℝ)))
    (hPair : K.cutPair m = (piece false, piece true))
    (hRadius : K.cutRadius m = n04bRootCutRadius T)
    (hDomains : ∀ side : Bool, physicalPieceOpen S K z (piece side) =
      n04bTravelHalfDomain (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) F T side)
    (hInverse : ∀ side : Bool,
      EqOn (K.inverseChart z (piece side)) (n04bRootPhysicalInverse X T side)
        (Icc (0 : ℝ) (n04bRootCutRadius T) ×ˢ (univ : Set ℝ))) :
    CanonicalCurrentCutPair S C K z m := by
  have hmid : T / 2 ∈ Ioo (0 : ℝ) T := ⟨half_pos hT, half_lt_self hT⟩
  have hcut := n04b_canonicalCutPoint_of_constructedRoot
    K z m piece X hT hPair hRadius hInverse
  have hchosen :
      n04bTravelCutPoint (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) F (T / 2) =
        (fun θ : ℝ => X (T / 2, θ)) :=
    funext (n04b_travelCutPoint_eq_of_inverse hF hX hFX hmid)
  have hcover := n04b_travelHalves_union_rangeCutPoint hT hF
  rw [hchosen] at hcover
  have hrange : Set.range (fun θ : ℝ => X (T / 2, θ)) ⊆
      Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) := by
    rintro p ⟨θ, rfl⟩
    exact hX ⟨hmid, mem_univ θ⟩
  have hend (side : Bool) :
      K.inverseChart z (piece side) '' ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) =
        ({if side then C.right m else C.left m} ×ˢ (univ : Set ℝ)) := by
    have he : EqOn (K.inverseChart z (piece side)) (n04bRootPhysicalInverse X T side)
        ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) := by
      intro p hp
      apply hInverse side
      have hp0 : p.1 = 0 := mem_singleton_iff.mp hp.1
      exact ⟨by rw [hp0]; exact ⟨le_rfl, (n04bRootCutRadius_pos hT).le⟩, hp.2⟩
    exact he.image_eq.trans
      ((n04bRootPhysicalInverse_zero_image X T side).trans (hEndpoints side))
  have htrace (θ : ℝ) :
      K.inverseChart z (piece true) (n04bRootCutRadius T, θ) = X (T / 2, θ) :=
    (hInverse true ⟨⟨(n04bRootCutRadius_pos hT).le, le_rfl⟩, mem_univ θ⟩).trans
      (n04b_rootPhysicalInverse_at_cut X hT true θ)
  unfold CanonicalCurrentCutPair
  simp only [hPair, hRadius, hDomains false, hDomains true, hcut]
  exact ⟨htrace, hrange, (n04b_travelHalves_split hF.mapsTo).1, hcover,
    by simpa using hend false, by simpa using hend true⟩

/-- The constructor's genuine cut is planar null whenever its travel
inverse is smooth. This is ready for the actual-domain partition proof. -/
theorem n04b_canonicalCutPoint_null_of_constructedRoot
    {S : PhysicalSpacesData} (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (piece : Bool → ℕ)
    {X : PolarPoint → PolarPoint} {T : ℝ} (hT : 0 < T)
    (hPair : K.cutPair m = (piece false, piece true))
    (hRadius : K.cutRadius m = n04bRootCutRadius T)
    (hInverse : ∀ side : Bool,
      EqOn (K.inverseChart z (piece side)) (n04bRootPhysicalInverse X T side)
        (Icc (0 : ℝ) (n04bRootCutRadius T) ×ˢ (univ : Set ℝ)))
    (hX : ContDiffOn ℝ ∞ X (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ))) :
    volume (Set.range (canonicalCutPoint S K z m)) = 0 := by
  rw [n04b_canonicalCutPoint_of_constructedRoot
    K z m piece X hT hPair hRadius hInverse]
  exact n04b_volume_range_travelSlice hX ⟨half_pos hT, half_lt_self hT⟩

end ContinuousFlexibility.Analysis
