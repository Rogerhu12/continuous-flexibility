module

public import ContinuousFlexibility.Analysis.N05SeedOpticalLowerAssembly
public import ContinuousFlexibility.Analysis.N05OpticalNegativeGeometry

/-!
# The actual carrier optical certificate for the retained seed

The certificate is proved from the retained construction. The transport
variant also covers finite grouping of cells with unchanged indices and
unchanged physical profile. Its input is the actual cell-point identity,
not a lower-bound hypothesis.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Radial

/-- Pointwise same-index cell transport preserves the optical certificate.
In particular, cells may be grouped without identifying their literal sets
with the seed's original cells. -/
theorem n05_actualCarrierOpticalLower_of_seed_cell_transport
    {q : ℝ} (P : SeedReferenceConstruction q) (hq : 0 < q)
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (ha : D.a = P.reference.a) (hb : D.b = P.reference.b)
    (hw : D.w = P.reference.w)
    (hcells : ∀ j r, r ∈ D.cells j →
      ∃ i, r ∈ P.reference.cells i ∧ P.reference.cellIndex i = D.cellIndex j)
    (hC : controlGeometryConditions D S C) :
    N05ActualCarrierOpticalLower D C := by
  obtain ⟨B, hB, hbound⟩ := P.n05_actual_cell_optical_lower hq
  refine ⟨B, 12, hB, by norm_num, fun m j hcarrier => ?_⟩
  have hcompD : NegativeRadialComponent D (C.left m) (C.right m) :=
    ⟨(hC.1 m).1, (hC.1 m).2.1, (hC.1 m).2.2,
      (hC.2.1 m).1, (hC.2.1 m).2.1, hC.2.2.2.1 m⟩
  have hcompP : NegativeRadialComponent P.reference (C.left m) (C.right m) := by
    simpa only [NegativeRadialComponent, ha, hb, hw] using hcompD
  have hmid : (C.left m + C.right m) / 2 ∈ Ioo (C.left m) (C.right m) := by
    constructor <;> linarith only [hcompD.2.1]
  obtain ⟨i, hmi, hi⟩ := hcells j _ (hcarrier hmid)
  intro r hr
  have hpoint := hbound (C.left m) (C.right m) i hcompP
    ⟨(C.left m + C.right m) / 2, hmid, hmi⟩ r hr
  simpa only [hi, hw] using hpoint

/-- Every actual control enumeration of the retained seed has the derived
whole-component lower bound for every one of its physical carriers. -/
theorem n05_actualCarrierOpticalLower_of_seed
    {q : ℝ} (P : SeedReferenceConstruction q) (hq : 0 < q)
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions P.reference S C) :
    N05ActualCarrierOpticalLower P.reference C :=
  n05_actualCarrierOpticalLower_of_seed_cell_transport P hq rfl rfl rfl
    (fun j r hr => ⟨j, hr, rfl⟩) hC

end ContinuousFlexibility.Statements
