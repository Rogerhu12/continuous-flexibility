module

public import ContinuousFlexibility.Analysis.RetainedPositiveComponentClassification
public import ContinuousFlexibility.Analysis.RetainedMorsePositiveGapEndpointX
public import ContinuousFlexibility.Analysis.PositiveComponentMaterialCell

/-!
# Actual retained positive endpoints and their own midpoint

The tail components have the proved one-step material-index oscillation.
The two central exceptions are finitely many actual components, so their
two endpoint differences have one finite maximum. This gives a single
endpoint-to-midpoint coordinate bound on the same retained reference.
Neither a whole-component cell nor a new component numbering is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem retainedReference_positive_endpoint_midpointX_bound
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {E : PhysicalSpacesData} {C : NonlinearGeometryData E}
    (hC : controlGeometryConditions Γ.reference E C)
    {T : MaterialData} (hT : IsMaterialData Γ.reference T) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w))
        (side : Bool),
        |endpointX 1 (Statements.endpointDistance Γ.reference (n04PositiveEndpoint i side)) -
          endpointX 1 (Statements.endpointDistance Γ.reference (n04PositiveMidpoint i))| ≤ L := by
  classical
  let I := N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w)
  let U : Set I := {i | ¬ ∃ side : Bool, ∃ n : ℕ, S.chain.index ≤ n ∧
    n04PositiveLeft i = P.sideRadius side * n06MorsePositiveLeft S.chain side n ∧
    n04PositiveRight i = P.sideRadius side * n06MorsePositiveRight S.chain side n}
  have hfinite : U.Finite :=
    (retainedReference_positive_gap_exceptions_finite
      P hS hband hq hΓ hw hcoordinates hC).1
  let X : ℝ → ℝ := fun r => endpointX 1 (Statements.endpointDistance Γ.reference r)
  let F : I → ℝ := fun i =>
    |X (n04PositiveLeft i) - X (n04PositiveMidpoint i)| +
      |X (n04PositiveRight i) - X (n04PositiveMidpoint i)|
  obtain ⟨B, hB⟩ := (hfinite.image F).bddAbove
  obtain ⟨L, hL, htail⟩ :=
    retainedReference_positive_gap_endpointX_oscillation P hS hband hcoordinates hT
  refine ⟨max L (max B 0), hL.trans (le_max_left _ _), ?_⟩
  intro i side
  by_cases hi : i ∈ U
  · have hFi : F i ≤ B := hB ⟨i, hi, rfl⟩
    have hside : |X (n04PositiveEndpoint i side) - X (n04PositiveMidpoint i)| ≤ F i := by
      cases side
      · exact le_add_of_nonneg_right (abs_nonneg _)
      · exact le_add_of_nonneg_left (abs_nonneg _)
    exact hside.trans (hFi.trans ((le_max_left B 0).trans (le_max_right _ _)))
  · have hg : ∃ tail : Bool, ∃ n : ℕ, S.chain.index ≤ n ∧
        n04PositiveLeft i = P.sideRadius tail * n06MorsePositiveLeft S.chain tail n ∧
        n04PositiveRight i = P.sideRadius tail * n06MorsePositiveRight S.chain tail n := by
      by_contra hne
      exact hi hne
    obtain ⟨tail, n, hn, hl, hr⟩ := hg
    let l := n06MorsePositiveLeft S.chain tail n
    let r := n06MorsePositiveRight S.chain tail n
    have hgeom := n06_morsePositive_gap_geometry
      (hS.2.2.2.1 S.sigma hS.2.2.1).1 tail hn
    have hlr : l < r := hgeom.2.1.trans (hgeom.2.2.1.trans hgeom.2.2.2.1)
    have he : n04PositiveEndpoint i side =
        P.sideRadius tail * (if side then r else l) := by
      cases side
      · exact hl
      · exact hr
    have hm : n04PositiveMidpoint i = P.sideRadius tail * ((l + r) / 2) := by
      change (n04PositiveLeft i + n04PositiveRight i) / 2 = _
      rw [hl, hr]
      ring
    have hend : (if side then r else l) ∈ Icc l r := by
      cases side
      · exact ⟨le_rfl, hlr.le⟩
      · exact ⟨hlr.le, le_rfl⟩
    have hmid : (l + r) / 2 ∈ Icc l r := by
      constructor <;> linarith only [hlr]
    have h := htail tail n hn (if side then r else l) ((l + r) / 2) hend hmid
    rw [← he, ← hm] at h
    exact h.trans (le_max_left _ _)

end ContinuousFlexibility.Radial
