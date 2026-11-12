import ContinuousFlexibility.Analysis.WholeCanonicalAtlasData

/-!
# The retained cuts of the whole-component atlas

The new enumeration changes neither physical negative half nor cut
curve. Reindex the existing cut geometry and transmission identities
through that one enumeration, keeping the same inverse and height.
-/

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
    have h := hcut.2 z hz hs m
    dsimp only [CanonicalCurrentCutPair, canonicalCutPoint] at h ⊢
    simpa only [physicalPieceOpen, n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
      n04WholeCutPair, Equiv.apply_symm_apply,
      Bool.false_eq_true, ite_false, ite_true] using h

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
  have h := htrans z hz hs u hu m θ
  dsimp only [canonicalHeight] at h ⊢
  simpa only [n04WholeCanonicalAtlasData, n04bWithInteriorDivision,
    n04WholeCutPair, Equiv.apply_symm_apply, Bool.false_eq_true, ite_false, ite_true] using h

end ContinuousFlexibility.Analysis
