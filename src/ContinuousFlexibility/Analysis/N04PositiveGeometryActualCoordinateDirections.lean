import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledGauge
import ContinuousFlexibility.Analysis.N04PositiveGeometryGaugeDirections
import ContinuousFlexibility.Analysis.N04PositiveGeometryTransportSamplePrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryReferencePullbackCosts

/-!
# The four actual coordinate components

The relative inverse is followed by the fixed reference chart; the
relative transport is evaluated at its fixed reference inverse. Their
unit-coordinate normalizations are exactly the atoms of the stored
whole atlas, including the angular defects and the inverse radial width.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

def n04PositiveGeometry_coordinateAtom (inverse angle : Bool) : Atom :=
  if inverse then (if angle then .inverseAngleDefect else .inverseRadial)
    else (if angle then .chartAngleDefect else .chartRadial)

theorem n04PositiveGeometry_coordinateAtom_isGeometry (inverse angle : Bool) :
    atomIsGeometry (n04PositiveGeometry_coordinateAtom inverse angle) := by
  cases inverse <;> cases angle <;> trivial

def n04PositiveGeometry_controlledReferenceComponent
    {W : N04RealizationStart} {X : N04RealizationChoice W} {order : ℕ}
    (F : N04PositiveGeometryControlledFamily W X order)
    (Y : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (inverse angle : Bool) (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
    (z : AnnularState W.S × ℝ) (p : PolarPoint) : ℝ :=
  if inverse then
    if angle then (wholePositiveReferenceGaugeInverse
      (F.toN04PositiveGeometryControlData.τ z i) (positiveReferenceCylinderInverse (Y i)) p).2
    else (wholePositiveReferenceGaugeInverse
      (F.toN04PositiveGeometryControlData.τ z i) (positiveReferenceCylinderInverse (Y i)) p).1
  else if angle then (wholePositiveReferenceGaugeChart (positiveReferenceCylinderChart (Y i))
    (F.toN04PositiveGeometryControlData.σ z i) p).2
  else (wholePositiveReferenceGaugeChart (positiveReferenceCylinderChart (Y i))
    (F.toN04PositiveGeometryControlData.σ z i) p).1

def n04PositiveGeometry_controlledCoordinate
    {W : N04RealizationStart} {X : N04RealizationChoice W} {order : ℕ}
    (F : N04PositiveGeometryControlledFamily W X order)
    (Y : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (inverse angle : Bool) (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
    (z : AnnularState W.S × ℝ) (q : PolarPoint) : ℝ :=
  if inverse then
    if angle then n04PositiveGeometry_controlledReferenceComponent F Y true true i z q - q.2
    else (n04PositiveGeometry_controlledReferenceComponent F Y true false i z q -
      n04PositiveLeft i) / (n04PositiveRight i - n04PositiveLeft i)
  else if angle then n04PositiveGeometry_controlledReferenceComponent F Y false true i z
    (n04PositiveLeft i + (n04PositiveRight i - n04PositiveLeft i) * q.1, q.2) - q.2
  else n04PositiveGeometry_controlledReferenceComponent F Y false false i z
    (n04PositiveLeft i + (n04PositiveRight i - n04PositiveLeft i) * q.1, q.2)

def n04PositiveGeometry_controlledReferenceComponent_joint
    {W : N04RealizationStart} {X : N04RealizationChoice W} {order : ℕ}
    (F : N04PositiveGeometryControlledFamily W X order)
    (Y H₀ : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (href : N04PositiveReferenceFamily (W.A X.e₀) X.src 4 Y H₀)
    {base : ℕ} {ε : ℝ} (inverse angle : Bool)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
    (JT : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun z : (StateDirections W.S × ℝ) × PolarPoint =>
        F.toN04PositiveGeometryControlData.τ (liftSectorParameter W.S W.C z.1) i z.2))
    (JS : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun z : (StateDirections W.S × ℝ) × PolarPoint =>
        F.toN04PositiveGeometryControlData.σ (liftSectorParameter W.S W.C z.1) i z.2)) :
    SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun z : (StateDirections W.S × ℝ) × PolarPoint =>
        n04PositiveGeometry_controlledReferenceComponent F Y inverse angle i
          (liftSectorParameter W.S W.C z.1) z.2) := by
  letI : LocallyConvexSpace ℝ (StateDirections W.S × ℝ) :=
    (sectorPairGrading_withSeminorms W.S).toLocallyConvexSpace
  have hU := sectorNeighborhood_isOpen W.S base ε ε
  let L : PolarPoint →L[ℝ] ℝ := if angle then
    ContinuousLinearMap.snd ℝ ℝ ℝ else ContinuousLinearMap.fst ℝ ℝ ℝ
  cases inverse with
  | false =>
      cases angle with
      | false =>
          exact (JS.comp_contDiff isOpen_univ
            ((n04PositiveGeometry_reference_scalar_geometry (href i).1).1.comp
              contDiff_fst).contDiffOn (fun _ _ => mem_univ _)).congrOn (fun _ _ => rfl)
      | true =>
          exact (smoothDirections_postcompCLM JS (ContinuousLinearMap.snd ℝ ℝ ℝ)).congrOn
            (fun _ _ => rfl)
  | true =>
      let P : ((StateDirections W.S × ℝ) × PolarPoint) →L[ℝ] PolarPoint :=
        ContinuousLinearMap.snd ℝ (StateDirections W.S × ℝ) PolarPoint
      let JP := (smoothDirectionsLinear P).restrict (hU.prod isOpen_univ) (subset_univ _)
      let Jχ := JP.comp_contDiff isOpen_univ (href i).1.inverse_smooth.contDiffOn
        (fun _ _ => mem_univ _)
      let JL := smoothDirections_postcompCLM JT L
      exact (n04PositiveGeometry_movingPointDirections JL Jχ).congrOn (fun _ _ => by
        cases angle <;> rfl)

def n04PositiveGeometry_controlledCoordinate_joint
    {W : N04RealizationStart} {X : N04RealizationChoice W} {order : ℕ}
    (F : N04PositiveGeometryControlledFamily W X order)
    (Y : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    {base : ℕ} {ε : ℝ} (inverse angle : Bool)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
    (J : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun z : (StateDirections W.S × ℝ) × PolarPoint =>
        n04PositiveGeometry_controlledReferenceComponent F Y inverse angle i
          (liftSectorParameter W.S W.C z.1) z.2)) :
    SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ unitStrip)
      (fun z : (StateDirections W.S × ℝ) × PolarPoint =>
        n04PositiveGeometry_controlledCoordinate F Y inverse angle i
          (liftSectorParameter W.S W.C z.1) z.2) := by
  have hU := sectorNeighborhood_isOpen W.S base ε ε
  have hV : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  let L : ((StateDirections W.S × ℝ) × PolarPoint) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ (StateDirections W.S × ℝ) PolarPoint)
  let Jθ : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ unitStrip)
      (fun z : (StateDirections W.S × ℝ) × PolarPoint => z.2.2) :=
    (smoothDirectionsLinearOn L (hU.prod hV)).congrOn (fun _ _ => rfl)
  cases inverse with
  | false =>
      let JP := n04PositiveGeometry_unitPullbackDirections J hU
        (n04PositiveLeft i) (n04PositiveRight i)
      cases angle with
      | false => exact JP
      | true =>
          exact (smoothDirectionsProd JP Jθ).comp_contDiff isOpen_univ
            (contDiff_fst.sub contDiff_snd).contDiffOn (fun _ _ => mem_univ _)
  | true =>
      let JP := J.restrict (hU.prod hV) (fun z hz => ⟨hz.1, mem_univ z.2⟩)
      cases angle with
      | false =>
          exact JP.comp_contDiff isOpen_univ
            ((contDiff_id.sub contDiff_const).div_const
              (n04PositiveRight i - n04PositiveLeft i)).contDiffOn (fun _ _ => mem_univ _)
      | true =>
          exact (smoothDirectionsProd JP Jθ).comp_contDiff isOpen_univ
            (contDiff_fst.sub contDiff_snd).contDiffOn (fun _ _ => mem_univ _)

theorem n04PositiveGeometry_controlledGauge_coordinate_fields
    {W : N04RealizationStart} {X : N04RealizationChoice W}
    (F : N04PositiveGeometryControlledFamily W X 3)
    (e : ℕ ≃ N04WholePieceIndex W.D)
    (Y H₀ : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (η : (W.S.height (3 / 4 : ℝ)).Space) (m : ℕ)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (hi : e m = .inr i) :
    ((F.gauge e Y H₀).V η).cell m = X.cell i ∧
      ∀ inverse angle : Bool, ∀ z : StateDirections W.S × ℝ,
        (F.gauge e Y H₀).atomFamily η (n04PositiveGeometry_coordinateAtom inverse angle) z m =
          fun q => n04PositiveGeometry_controlledCoordinate F Y inverse angle i
            (liftSectorParameter W.S W.C z) q := by
  let G := F.gauge e Y H₀
  have fields (z : AnnularState W.S × ℝ) :=
    n04WholeReferenceGaugeAtlasData_positive_fields W.C W.L (W.A X.e₀) e X.cell
      (fun j => positiveReferenceCylinderChart (Y j))
      (fun j => positiveReferenceCylinderInverse (Y j)) (fun j p => H₀ j p.1)
      F.toN04PositiveGeometryControlData.τ F.toN04PositiveGeometryControlData.σ
      F.toN04PositiveGeometryControlData.Q F.buffer.region z m i hi
  refine ⟨(fields (W.C.referenceState, 0)).2.2.2.2.2.1, fun inverse angle z => ?_⟩
  let state := liftSectorParameter W.S W.C z
  have hl : (G.V η).left m = 0 := (fields state).1
  have hr : (G.V η).right m = 1 := (fields state).2.1
  have hpl : (G.V η).physicalLeft m = n04PositiveLeft i := (fields state).2.2.1
  have hpr : (G.V η).physicalRight m = n04PositiveRight i := (fields state).2.2.2.1
  have hF : (G.V η).chart state m =
      wholePositiveReferenceGaugeChart (positiveReferenceCylinderChart (Y i))
        (F.toN04PositiveGeometryControlData.σ state i) := (fields state).2.2.2.2.2.2.2.1
  have hI : (G.V η).inverseChart state m =
      wholePositiveReferenceGaugeInverse (F.toN04PositiveGeometryControlData.τ state i)
        (positiveReferenceCylinderInverse (Y i)) := (fields state).2.2.2.2.2.2.2.2.1
  funext q
  change atom W.D W.U (G.S η) (G.C η) (G.L η) (G.V η) state m
    (n04PositiveGeometry_coordinateAtom inverse angle) q = _
  cases inverse with
  | false =>
      cases angle with
      | false =>
          change (((G.V η).chart state m
            ((G.V η).physicalLeft m +
              ((G.V η).physicalRight m - (G.V η).physicalLeft m) * q.1, q.2)).1 -
                (G.V η).left m) / ((G.V η).right m - (G.V η).left m) = _
          rw [hpl, hpr, hl, hr, sub_zero, sub_zero, div_one, hF]
          rfl
      | true =>
          change ((G.V η).chart state m
            ((G.V η).physicalLeft m +
              ((G.V η).physicalRight m - (G.V η).physicalLeft m) * q.1, q.2)).2 - q.2 = _
          rw [hpl, hpr, hF]
          rfl
  | true =>
      cases angle with
      | false =>
          change (((G.V η).inverseChart state m
            ((G.V η).left m + ((G.V η).right m - (G.V η).left m) * q.1, q.2)).1 -
              (G.V η).physicalLeft m) / ((G.V η).physicalRight m - (G.V η).physicalLeft m) = _
          rw [hl, hr, sub_zero, one_mul, zero_add, hpl, hpr, hI]
          rfl
      | true =>
          change ((G.V η).inverseChart state m
            ((G.V η).left m + ((G.V η).right m - (G.V η).left m) * q.1, q.2)).2 - q.2 = _
          rw [hl, hr, sub_zero, one_mul, zero_add, hI]
          rfl

end ContinuousFlexibility.Analysis
