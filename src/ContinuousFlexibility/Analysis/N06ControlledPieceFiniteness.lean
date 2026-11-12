import ContinuousFlexibility.Analysis.N05ReferenceInterface
import ContinuousFlexibility.Analysis.N06FiniteReferenceColumns

/-!
# Compact support meets finitely many controlled reference pieces

The original controlled reference coordinates compare each physical point
with an actual profile cell, and have finitely many pieces at each cell
index. The profile's own compact finiteness therefore proves the atlas
finiteness needed by the three actual reference source columns.
-/

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
  obtain ⟨_, B, _, hcell, hnumber, _⟩ := hK
  have hfinite : {j : ℕ | (D.cells j ∩ J).Nonempty}.Finite :=
    hCd.2.2.2.2.2.1 J hJ hJD
  let I : Finset ℕ := hfinite.toFinset
  let N : ℕ := I.sup D.cellIndex
  let M : ℕ := ⌈(N : ℝ) + B⌉₊
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
  have hcast : (D.cellIndex (K.cell m) : ℝ) ≤ (N : ℝ) + B := by
    have hc := (abs_le.mp hcompare).1
    have hn : (D.cellIndex j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hjN
    linarith
  have hmM : D.cellIndex (K.cell m) ≤ M := by
    have hceil : (N : ℝ) + B ≤ (M : ℝ) := Nat.le_ceil _
    exact_mod_cast hcast.trans hceil
  exact mem_iUnion.mpr ⟨D.cellIndex (K.cell m), mem_iUnion.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hmM), rfl⟩⟩

end ContinuousFlexibility.Statements
