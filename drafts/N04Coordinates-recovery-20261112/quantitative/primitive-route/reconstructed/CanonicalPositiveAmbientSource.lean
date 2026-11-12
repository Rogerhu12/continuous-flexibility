import ContinuousFlexibility.Analysis.WholePositiveEndpointFields
import ContinuousFlexibility.Analysis.TaylorReferenceIdentity
import ContinuousFlexibility.Analysis.OneSidedWholeComponentTransport

/-!
# The actual certified source at an ambient positive endpoint

Every negative root lies strictly inside the reference annulus. A
certified source at an ambient endpoint therefore has no negative
neighbor and is exactly the identity/one source, for every state.
Its actual radial Taylor representative is consequently the identity.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology

theorem n04PositiveEndpointSource_eq_none_of_ambient
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions D S C)
    {i : N04PositiveComponent D.a D.b (deriv D.w)} {side : Bool}
    (j : N04PositiveEndpointSource C i side)
    (hroot : n04PositiveEndpoint i side = (if side then D.b else D.a)) :
    j.val = none := by
  rcases j with ⟨o, ho⟩
  cases o with
  | none => rfl
  | some m =>
      exfalso
      change n04PositiveEndpoint i side = (if side then C.left m else C.right m) at ho
      have he := ho.symm.trans hroot
      cases side
      · change C.right m = D.a at he
        exact ((hC.1 m).1.trans (hC.1 m).2.1).ne' he
      · change C.left m = D.b at he
        exact ((hC.1 m).2.1.trans (hC.1 m).2.2).ne he

theorem n04PositiveSource_ambient_fields
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions D S C)
    {i : N04PositiveComponent D.a D.b (deriv D.w)} {side : Bool}
    (j : N04PositiveEndpointSource C i side)
    (hroot : n04PositiveEndpoint i side = (if side then D.b else D.a))
    (K : CanonicalData S) (z : AnnularState S × ℝ) :
    n04PositiveSourceMap j K z = (id : PolarPoint → PolarPoint) ∧
      n04PositiveSourceHeight j K z = (fun _ => (1 : ℝ)) := by
  have hj := n04PositiveEndpointSource_eq_none_of_ambient hC j hroot
  constructor <;> simp only [n04PositiveSourceMap, n04PositiveSourceHeight, hj]

theorem n04PositiveSource_ambient_radial_representative
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions D S C)
    {i : N04PositiveComponent D.a D.b (deriv D.w)}
    (j : ∀ side, N04PositiveEndpointSource C i side) (side : Bool)
    (hroot : n04PositiveEndpoint i side = (if side then D.b else D.a))
    (K : CanonicalData S) (z : AnnularState S × ℝ) (n : ℕ) :
    oneSidedEndpointRepresentative (n + 1) (n04PositiveLeft i) (n04PositiveRight i)
      (fun t p => (n04PositiveSourceMap (j t) K z p).1) side =
        (Prod.fst : PolarPoint → ℝ) := by
  have hmap := (n04PositiveSource_ambient_fields hC (j side) hroot K z).1
  change oneSidedBoundaryTaylorRepresentative (n + 1)
    (if side then n04PositiveRight i else n04PositiveLeft i)
    (fun p => (n04PositiveSourceMap (j side) K z p).1) = _
  rw [hmap]
  exact oneSidedBoundaryTaylorRepresentative_eq_fst (fun _ => Filter.EventuallyEq.rfl) n

end ContinuousFlexibility.Analysis
