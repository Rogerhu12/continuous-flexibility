module

public import ContinuousFlexibility.Analysis.N05ReferenceInterface
public import ContinuousFlexibility.Analysis.N06FiniteReferenceColumns
public import ContinuousFlexibility.Analysis.N05ReferenceSWindow
public import ContinuousFlexibility.Radial.InnerUniformSuppression
public import ContinuousFlexibility.Radial.MorseTransitionBands

/-!
# Compact support meets finitely many controlled reference pieces

The controlled reference coordinates compare each physical point with an
actual profile cell through the endpoint-exponent window, and have finitely
many pieces at each cell index. The window bounds the coefficient exponent of
the piece by that of the cell, and the profile's own compact finiteness
therefore proves the atlas finiteness needed by the three actual reference
source columns.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

theorem n06_controlledReferencePieces_finite_on_compact
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S}
    (hD : IsAccumulatingProfile D)
    (hK : N05ControlledReferenceCoordinates D S C K)
    {J : Set ℝ} (hJ : IsCompact J) (hJD : J ⊆ radialCore D) :
    {m : ℕ | (Ioo (K.physicalLeft m) (K.physicalRight m) ∩ J).Nonempty}.Finite := by
  classical
  obtain ⟨Cd, hCd⟩ := hD
  obtain ⟨_, B, hB, hcell, hnumber, _⟩ := hK
  obtain ⟨Cq, hCq, hreverse⟩ := n05_radialQ_swindow_reverse_bound hB.le
  have hfinite : {j : ℕ | (D.cells j ∩ J).Nonempty}.Finite :=
    hCd.2.2.2.2.2.1 J hJ hJD
  let I : Finset ℕ := hfinite.toFinset
  let N : ℕ := I.sup D.cellIndex
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    (Radial.inner_radialQ_tendsto.eventually_gt_atTop (Cq * (radialQ N + 1)))
  have hfib : (⋃ n ∈ (Finset.range (M + 1) : Set ℕ),
      {m : ℕ | D.cellIndex (K.cell m) = n}).Finite :=
    (Finset.finite_toSet (Finset.range (M + 1))).biUnion
      (fun n _ => (hnumber n).1)
  apply hfib.subset
  intro m hm
  obtain ⟨r, hr, hrJ⟩ := hm
  obtain ⟨j, hrj, hcompare⟩ := hcell m r hr
  have hj : j ∈ I := hfinite.mem_toFinset.mpr ⟨r, hrj, hrJ⟩
  have hjN : D.cellIndex j ≤ N := Finset.le_sup (f := D.cellIndex) hj
  have hQj : radialQ (D.cellIndex j) ≤ radialQ N :=
    Radial.radialQ_strictMono.monotone hjN
  have hQm : radialQ (D.cellIndex (K.cell m)) ≤ Cq * (radialQ N + 1) :=
    (hreverse _ _ hcompare).trans
      (mul_le_mul_of_nonneg_left (by linarith only [hQj]) hCq.le)
  have hmM : D.cellIndex (K.cell m) ≤ M := by
    by_contra hlt
    exact (not_lt.mpr hQm) (hM _ (le_of_lt (not_le.mp hlt)))
  exact mem_iUnion.mpr ⟨D.cellIndex (K.cell m), mem_iUnion.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hmM), rfl⟩⟩

end ContinuousFlexibility.Statements
