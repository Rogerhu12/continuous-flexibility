import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentSplit
import ContinuousFlexibility.Analysis.N04RealizationRootBoundaryPoint

/-!
# Values of the actual positive inverse-angle atom

These identities use the stored atlas, its specified endpoint sources and
the genuine reference cylinder.  The reference atom vanishes everywhere.
Transport matching fixes the current endpoint atom to the inverse of the
original N01 root label, whereas the middle germ fixes it to zero on the
normalization buffer.  Thus the separation between these two prescribed
values is measured in the same canonical radial coordinate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff Topology

/-- The finite reference matching includes the actual scalar endpoint
values; no bound for the interpolation width is used. -/
theorem n04PositiveGeometry_reference_endpoint_value
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    (Y H : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (hreference : N04PositiveReferenceFamily (W.A X.e₀) X.src 4 Y H)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool) :
    Y i (n04PositiveEndpoint i side) = if side then 1 else 0 := by
  have hj := congrArg
    (fun A : PolarPoint [×0]→L[ℝ] ℝ => A Fin.elim0)
    ((hreference i).2.1 side 0 0 (by omega))
  have hvalue : Y i (n04PositiveEndpoint i side) =
      n04PositiveReferenceSourceCoordinate (X.src i side) (W.A X.e₀)
        (n04PositiveEndpoint i side, 0) := by
    simpa only [iteratedFDeriv_zero_apply] using hj
  have hdata := n04Coordinates_actual_positive_reference_source_data
    W.hT W.hS W.through03 W.field X.e₀ (X.src i side)
  exact hvalue.trans hdata.2.2.2.2.2.2.2.2.1

/-- The actual relative endpoint map is the inverse of the original
label on the adjacent negative component.  One Boolean argument handles
both endpoints, with the opposite endpoint of the negative component. -/
theorem n04PositiveGeometry_source_endpoint_value
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
    (side : Bool) (m : ℕ) (hsource : (X.src i side).val = some m)
    {z : AnnularState W.S × ℝ} (hz : z ∈ stateNeighborhood W.S W.C W.base W.ε)
    (hs : stateSector W.S z.1) (θ : ℝ) :
    n04PositiveSourceMap (X.src i side) (W.A X.e₀) z
        (n04PositiveEndpoint i side, θ) =
      (n04PositiveEndpoint i side,
        Function.invFun (n01RootLabel W.S W.C z m (!side)) θ) := by
  have hend : n04PositiveEndpoint i side =
      (if side then W.C.left m else W.C.right m) := by
    have h := (X.src i side).property
    simpa only [hsource] using h
  have hend' : n04PositiveEndpoint i side =
      (if !side then W.C.right m else W.C.left m) := by
    rw [hend]
    cases side <;> rfl
  let k : ℕ := X.e₀.symm (.inl (m, !side))
  have hk : (if side then ((W.A X.e₀).cutPair m).1 else
      ((W.A X.e₀).cutPair m).2) = k := by
    cases side <;> rfl
  have hi : X.e₀ k = .inl (m, !side) := X.e₀.apply_symm_apply _
  simp only [n04PositiveSourceMap, hsource]
  rw [hk, hend']
  exact n04Realization_actualRoot_currentPoint_eq
    W.hT W.hS W.through03 W.field X.e₀ hz hs k m (!side) hi θ

namespace N04RealizationGauge

variable (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
  (m : ℕ) (i : N04PositiveComponent G.W.D.a G.W.D.b (deriv G.W.D.w))
  (hi : G.e m = .inr i)

include hi

/-- On a positive piece the canonical unit coordinate is already the
canonical coordinate, since its endpoints are exactly zero and one. -/
theorem n04PositiveGeometry_inverseAngle_formula
    (z : AnnularState (G.S η) × ℝ) (p : PolarPoint) :
    atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η) z m .inverseAngleDefect p =
      (G.τ z i (Function.invFun (G.Y i) p.1, p.2)).2 - p.2 := by
  have hf := n04WholeReferenceGaugeAtlasData_positive_fields
    G.W.C G.W.L (G.W.A G.X.e₀) G.e G.X.cell
    (fun j => positiveReferenceCylinderChart (G.Y j))
    (fun j => positiveReferenceCylinderInverse (G.Y j))
    (fun j p => G.H j p.1) G.τ G.σ G.Q G.N z m i hi
  have hl : (G.V η).left m = 0 := hf.1
  have hr : (G.V η).right m = 1 := hf.2.1
  have hI : (G.V η).inverseChart z m =
      wholePositiveReferenceGaugeInverse (G.τ z i) (positiveReferenceCylinderInverse (G.Y i)) :=
    hf.2.2.2.2.2.2.2.2.1
  change ((G.V η).inverseChart z m
    ((G.V η).left m + ((G.V η).right m - (G.V η).left m) * p.1, p.2)).2 - p.2 = _
  rw [hl, hr, sub_zero, one_mul, zero_add, hI]
  rfl

/-- Evaluation at a reference radial image cancels the genuine reference
inverse, on the entire real line. -/
theorem n04PositiveGeometry_inverseAngle_at_reference_image
    (hreference : N04PositiveReferenceFamily (G.W.A G.X.e₀) G.X.src 4 G.Y G.H)
    (z : AnnularState (G.S η) × ℝ) (r θ : ℝ) :
    atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η) z m .inverseAngleDefect
        (G.Y i r, θ) = (G.τ z i (r, θ)).2 - θ := by
  rw [G.n04PositiveGeometry_inverseAngle_formula η m i hi]
  have hInv : Function.invFun (G.Y i) (G.Y i r) = r :=
    congrArg Prod.fst ((hreference i).1.left_inverse (r, θ))
  rw [hInv]

/-- The reference inverse preserves the angle for every auxiliary
column and every positive canonical point, including both boundaries. -/
theorem n04PositiveGeometry_inverseAngle_reference_zero
    (href : G.τ (G.W.C.referenceState, 0) i = id) (p : PolarPoint) :
    G.atomRef η .inverseAngleDefect m p = 0 := by
  have ht : (G.τ (G.W.C.referenceState, 0) i
      (Function.invFun (G.Y i) p.1, p.2)).2 = p.2 :=
    congrArg (fun F : PolarPoint → PolarPoint =>
      (F (Function.invFun (G.Y i) p.1, p.2)).2) href
  exact (G.n04PositiveGeometry_inverseAngle_formula η m i hi (G.ref η) p).trans
    (sub_eq_zero.mpr ht)

/-- Matching prescribes zero angular defect at every physical radius
where the transport has its middle identity germ. -/
theorem n04PositiveGeometry_inverseAngle_middle_zero
    (hreference : N04PositiveReferenceFamily (G.W.A G.X.e₀) G.X.src 4 G.Y G.H)
    {z : AnnularState (G.S η) × ℝ} {c d lower upper : ℝ}
    (hmatch : WholePositiveTransportMatching 3
      (fun side => n04PositiveSourceMap (G.X.src i side) (G.W.A G.X.e₀) z)
      (fun side => n04PositiveSourceHeight (G.X.src i side) (G.W.A G.X.e₀) z)
      (G.τ z i) (G.σ z i) (G.Q z i) (n04PositiveLeft i) (n04PositiveRight i)
      c d lower upper)
    (r : ℝ) (hr : r ∈ Icc c d) (θ : ℝ) :
    atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η) z m .inverseAngleDefect
        (G.Y i r, θ) = 0 := by
  rw [G.n04PositiveGeometry_inverseAngle_at_reference_image η m i hi hreference]
  rw [(hmatch.geometry.middle_germ r hr θ).eq_of_nhds]
  exact sub_self _

/-- The endpoint atom of the stored positive atlas is fixed by its
source label, independent of all choices inside the interpolation collar. -/
theorem n04PositiveGeometry_inverseAngle_endpoint
    (hreference : N04PositiveReferenceFamily (G.W.A G.X.e₀) G.X.src 4 G.Y G.H)
    {z : AnnularState (G.S η) × ℝ}
    (hz : z ∈ stateNeighborhood G.W.S G.W.C G.W.base G.W.ε)
    (hs : stateSector G.W.S z.1) {c d lower upper : ℝ}
    (hmatch : WholePositiveTransportMatching 3
      (fun side => n04PositiveSourceMap (G.X.src i side) (G.W.A G.X.e₀) z)
      (fun side => n04PositiveSourceHeight (G.X.src i side) (G.W.A G.X.e₀) z)
      (G.τ z i) (G.σ z i) (G.Q z i) (n04PositiveLeft i) (n04PositiveRight i)
      c d lower upper)
    (side : Bool) (k : ℕ) (hsource : (G.X.src i side).val = some k) (θ : ℝ) :
    atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η) z m .inverseAngleDefect
        (if side then 1 else 0, θ) =
      Function.invFun (n01RootLabel G.W.S G.W.C z k (!side)) θ - θ := by
  rw [← n04PositiveGeometry_reference_endpoint_value G.W G.X G.Y G.H hreference i side,
    G.n04PositiveGeometry_inverseAngle_at_reference_image η m i hi hreference]
  have hj := congrArg
    (fun A : PolarPoint [×0]→L[ℝ] PolarPoint => A Fin.elim0)
    (hmatch.coordinate_jets side 0 (by omega) θ)
  have ht : G.τ z i (n04PositiveEndpoint i side, θ) =
      n04PositiveSourceMap (G.X.src i side) (G.W.A G.X.e₀) z
        (n04PositiveEndpoint i side, θ) := by
    simpa only [iteratedFDeriv_zero_apply, n04PositiveEndpoint] using hj
  rw [ht, n04PositiveGeometry_source_endpoint_value G.W G.X i side k hsource hz hs θ]

/-- Whole matching supplies actual spatial smoothness across both
canonical endpoint circles, sufficient for a closed-interval MVT. -/
theorem n04PositiveGeometry_inverseAngle_contDiff
    (hreference : N04PositiveReferenceFamily (G.W.A G.X.e₀) G.X.src 4 G.Y G.H)
    {z : AnnularState (G.S η) × ℝ} {c d lower upper : ℝ}
    (hmatch : WholePositiveTransportMatching 3
      (fun side => n04PositiveSourceMap (G.X.src i side) (G.W.A G.X.e₀) z)
      (fun side => n04PositiveSourceHeight (G.X.src i side) (G.W.A G.X.e₀) z)
      (G.τ z i) (G.σ z i) (G.Q z i) (n04PositiveLeft i) (n04PositiveRight i)
      c d lower upper) :
    ContDiff ℝ ∞
      (atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η) z m .inverseAngleDefect) := by
  have he : atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η) z m .inverseAngleDefect =
      (fun p => (G.τ z i (positiveReferenceCylinderInverse (G.Y i) p)).2 - p.2) := by
    funext p
    exact G.n04PositiveGeometry_inverseAngle_formula η m i hi z p
  rw [he]
  exact (hmatch.geometry.smooth.comp (hreference i).1.inverse_smooth).snd.sub contDiff_snd

end N04RealizationGauge

end ContinuousFlexibility.Analysis
