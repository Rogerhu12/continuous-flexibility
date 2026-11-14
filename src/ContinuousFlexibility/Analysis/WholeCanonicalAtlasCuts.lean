module

public import ContinuousFlexibility.Analysis.WholeCanonicalAtlasData

/-!
# The retained cuts of the whole-component atlas

The new enumeration changes neither physical negative half nor cut
curve. Reindex the existing cut geometry and transmission identities
through that one enumeration, keeping the same inverse and height.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff
open ContinuousFlexibility.Statements

variable {D : ReferenceData} {S : PhysicalSpacesData}
  (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
  (e : ℕ ≃ N04WholePieceIndex D)
  (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
  (F G : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
  (Q : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
  (N : Set ℝ) {base : ℕ} {ε : ℝ}

theorem n04WholeCanonicalAtlasData_cutGeometry
    (hcut : CanonicalCutGeometry S C K base ε) :
    CanonicalCutGeometry S C
      (n04WholeCanonicalAtlasData C L K e cell F G Q N) base ε := by
  constructor
  · intro m
    have h := hcut.1 m
    simpa only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
      n04WholeCutPair, Equiv.apply_symm_apply, n04WholePiecePositive,
      Bool.false_eq_true, ite_false, ite_true, h.1, h.2.1] using h
  · intro z hz hs m
    let W := n04WholeCanonicalAtlasData C L K e cell F G Q N
    have hcurve : canonicalCutPoint S W z m = canonicalCutPoint S K z m := by
      funext θ
      simp only [canonicalCutPoint, W, n04WholeCanonicalAtlasData,
        n04bWithInteriorDivision, n04WholeCutPair, Equiv.apply_symm_apply,
        Bool.false_eq_true, ite_false, ite_true]
    change CanonicalCurrentCutPair S C W z m
    dsimp only [CanonicalCurrentCutPair]
    rw [hcurve]
    simpa only [CanonicalCurrentCutPair, physicalPieceOpen, W,
      n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
      n04WholeCutPair, Equiv.apply_symm_apply,
      Bool.false_eq_true, ite_false, ite_true] using hcut.2 z hz hs m

theorem n04WholeCanonicalAtlasData_transmission
    (htrans : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ u : PolarPoint → ℝ, ContDiff ℝ ∞ u → ∀ m θ,
        let Wl := canonicalHeight S K z (K.cutPair m).1 u
        let Wr := canonicalHeight S K z (K.cutPair m).2 u
        Wr (K.cutRadius m, θ) = Wl (K.cutRadius m, θ) ∧
          radialPartial Wr (K.cutRadius m, θ) =
            -radialPartial Wl (K.cutRadius m, θ) -
              Wl (K.cutRadius m, θ) / (2 * K.cutRadius m))
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (u : PolarPoint → ℝ) (hu : ContDiff ℝ ∞ u)
    (m : ℕ) (θ : ℝ) :
    let W := n04WholeCanonicalAtlasData C L K e cell F G Q N
    let Wl := canonicalHeight S W z (W.cutPair m).1 u
    let Wr := canonicalHeight S W z (W.cutPair m).2 u
    Wr (W.cutRadius m, θ) = Wl (W.cutRadius m, θ) ∧
      radialPartial Wr (W.cutRadius m, θ) =
        -radialPartial Wl (W.cutRadius m, θ) -
          Wl (W.cutRadius m, θ) / (2 * W.cutRadius m) := by
  let W := n04WholeCanonicalAtlasData C L K e cell F G Q N
  have hheight (side : Bool) :
      canonicalHeight S W z (if side then (W.cutPair m).2 else (W.cutPair m).1) u =
        canonicalHeight S K z (if side then (K.cutPair m).2 else (K.cutPair m).1) u := by
    funext p
    cases side <;> simp only [canonicalHeight, W, n04WholeCanonicalAtlasData,
      n04bWithInteriorDivision, n04WholeCutPair, Equiv.apply_symm_apply,
      Bool.false_eq_true, ite_false, ite_true]
  have hleft : canonicalHeight S W z (W.cutPair m).1 u =
      canonicalHeight S K z (K.cutPair m).1 u := hheight false
  have hright : canonicalHeight S W z (W.cutPair m).2 u =
      canonicalHeight S K z (K.cutPair m).2 u := hheight true
  change
    canonicalHeight S W z (W.cutPair m).2 u (W.cutRadius m, θ) =
        canonicalHeight S W z (W.cutPair m).1 u (W.cutRadius m, θ) ∧
      radialPartial (canonicalHeight S W z (W.cutPair m).2 u) (W.cutRadius m, θ) =
        -radialPartial (canonicalHeight S W z (W.cutPair m).1 u) (W.cutRadius m, θ) -
          canonicalHeight S W z (W.cutPair m).1 u (W.cutRadius m, θ) /
            (2 * W.cutRadius m)
  rw [hleft, hright]
  exact htrans z hz hs u hu m θ

end ContinuousFlexibility.Analysis
