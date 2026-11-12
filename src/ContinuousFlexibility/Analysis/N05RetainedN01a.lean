import ContinuousFlexibility.Analysis.N05SeedNegativeEnumerationBounds
import ContinuousFlexibility.Analysis.N05RetainedN01Primitive
import ContinuousFlexibility.Analysis.N01aControlGeometryAssembly
import ContinuousFlexibility.Analysis.N01aMaterialContext
import ContinuousFlexibility.Analysis.N01aOpticalProfile
import ContinuousFlexibility.Analysis.N01aReferenceHeight
import ContinuousFlexibility.Analysis.SpacesConclusion
import ContinuousFlexibility.Analysis.TameCalculusTheorem

/-!
# N01 Part A on the same retained seed reference

This draft uses the unchanged N01a interfaces at commit 3318875.  The
reference, its cells and their indices are not replaced or regrouped.
The controls retain the actual whole-component hosts returned by their
construction.  The only extra seed input is its original index formula.
-/

noncomputable section

namespace ContinuousFlexibility.Radial.SeedReferenceConstruction

open Set Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

variable {q : ℝ} (P : SeedReferenceConstruction q)

/-- The frozen Part A, the explicit negative-component enumeration, and
actual carrier containment all hold for one and the same seed reference.
The physical spaces are constructed by the already proved W02 assembly. -/
theorem exists_n05RetainedN01a (hq : 0 < q)
    (hD : IsRadialReference P.reference)
    (hraw : (P.selected.family P.selected.sigma).cellIndex =
      morseTwoTailAt P.selected.chain.index (fun _ k => P.selected.chain.index + k)) :
    ∃ T : MaterialData, ∃ S : PhysicalSpacesData, ∃ C : NonlinearGeometryData S,
      IsMaterialData P.reference T ∧ IsPhysicalSpaces P.reference T S ∧
      N01PartA P.reference T S C ∧
      (∀ m, (C.left m, C.right m) = (P.n05NegativeEnumeration hq m).val) ∧
      (∀ m, Ioo (C.left m) (C.right m) ⊆ P.reference.cells (C.cell m)) ∧
      (∀ r : ℝ, 1 ≤ T.E0 r) ∧ N01PrimitiveGeometry P.reference T S C := by
  classical
  obtain ⟨sample, hT, hsample, _⟩ := exists_n01a_affineMaterialData hD.1
  let T : MaterialData := affineMaterialData P.reference sample
  obtain ⟨S, hS⟩ := (spaces_W02_statement ContinuousFlexibility.Analysis.h01Statement)
    P.reference T hD.1 hT
  let e : ℕ ≃ N01aNegativeComponent P.reference := P.n05NegativeEnumeration hq
  obtain ⟨host, χ, hhost, hχ, hderiv, hjets⟩ :=
    exists_n01a_opticalControls_of_radialReference hD
      (l := fun J : N01aNegativeComponent P.reference => J.left)
      (h := fun J : N01aNegativeComponent P.reference => J.right)
      (fun J : N01aNegativeComponent P.reference => J.property)
  obtain ⟨x, hx⟩ := exists_referenceState_of_heightMember hS hD.2.2.2.1
    (n01a_reference_heightMember hD sample)
  let χe : ℕ → ℝ → ℝ := fun m => χ (e m)
  let C : NonlinearGeometryData S :=
    { n01aGeometryOfControls S e χe x with cell := fun m => host (e m) }
  have hcontrol : controlGeometryConditions P.reference S C :=
    n01aGeometryOfControls_controlGeometry hD.1.choose_spec.1 hD.2.2.1 e χe x
      (fun m => hχ (e m)) (fun m => hderiv (e m))
  obtain ⟨L, hL, hindex⟩ := P.n05NegativeComponentAt_carrier_index_bound hq hraw
  have hlabel (m : ℕ) :
      |(P.reference.cellIndex (C.cell m) : ℝ) - P.reference.cellIndex m| ≤ L := by
    apply hindex m (host (e m))
    simpa only [e, n05NegativeEnumeration_apply, N01aNegativeComponent.left,
      N01aNegativeComponent.right] using hhost (e m)
  have hpartA : N01PartA P.reference T S C := by
    refine ⟨hD, ?_, hcontrol, ⟨L, hL, hlabel⟩, ?_⟩
    · simpa only [referenceStateConditions, C, n01aGeometryOfControls] using hx
    · intro s
      obtain ⟨B, hB, hb⟩ := hjets s
      obtain ⟨A, hA, ha⟩ := n05Retained_affine_coefficient_power hD.1 hsample B hB.le
      refine ⟨A, hA, fun m r _ => ?_⟩
      exact (hb (e m) r).trans (ha (host (e m)))
  refine ⟨T, S, C, hT, hS, hpartA, ?_, ?_, ?_, ?_⟩
  · intro m
    exact Prod.eta _
  · intro m
    exact hhost (e m)
  · exact n05Retained_affine_E0_one P.reference sample
  · exact P.n05Retained_primitiveGeometry hq hD hsample C hcontrol
      (fun m => hhost (e m))

end ContinuousFlexibility.Radial.SeedReferenceConstruction
