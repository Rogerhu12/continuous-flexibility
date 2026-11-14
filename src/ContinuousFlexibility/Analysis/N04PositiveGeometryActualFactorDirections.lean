import ContinuousFlexibility.Analysis.N04PositiveGeometrySourceTraceUniform
import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsTransportDirections
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledRadialFormula

/-!
# Genuine factors of the stored positive coordinate change

The low order is chosen once from the actual source traces. On every
smaller sector the angular lift, its inverse, both radial factors and
both transports are produced together. The coefficient towers are the
same towers used by the finite radial kernel.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

structure N04PositiveGeometryFactorData
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n) (base : ℕ) (ε : ℝ)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) where
  angle : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
    (fun z : (StateDirections W.S × ℝ) × PolarPoint =>
      G.toN04PositiveGeometryControlData.angle (liftSectorParameter W.S W.C z.1) i z.2)
  angleInverse : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
    (fun z : (StateDirections W.S × ℝ) × PolarPoint =>
      parameterizedCircleInverse
        (G.toN04PositiveGeometryControlData.angle (liftSectorParameter W.S W.C z.1) i) z.2)
  radial : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
    (fun z : (StateDirections W.S × ℝ) × PolarPoint =>
      G.toN04PositiveGeometryControlData.radial (liftSectorParameter W.S W.C z.1) i z.2)
  radialInverse : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
    (fun z : (StateDirections W.S × ℝ) × PolarPoint =>
      G.toN04PositiveGeometryControlData.radialInverse (liftSectorParameter W.S W.C z.1) i z.2)
  coefficients : ∀ side (j : Fin (n + 1)),
    SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun z : (StateDirections W.S × ℝ) × ℝ =>
        G.toN04PositiveGeometryControlData.coefficients
          (liftSectorParameter W.S W.C z.1) i side (j + 1) z.2)
  transport : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
    (fun z : (StateDirections W.S × ℝ) × PolarPoint =>
      G.toN04PositiveGeometryControlData.τ (liftSectorParameter W.S W.C z.1) i z.2)
  inverseTransport : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
    (fun z : (StateDirections W.S × ℝ) × PolarPoint =>
      G.toN04PositiveGeometryControlData.σ (liftSectorParameter W.S W.C z.1) i z.2)

theorem n04PositiveGeometry_actualFactorData_nonempty
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n) (hn : n ≤ 3)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1) (hGb : G.base ≤ base) (hGε : ε ≤ G.ε)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε)
    (hctx : ∀ m side,
      N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m side) :
    ∃ low : ℕ, base ≤ low ∧ ∀ larger : ℕ, low ≤ larger →
      ∀ η : ℝ, η ≤ ε → η ≤ 1 / 2 →
      ∀ i, Nonempty (N04PositiveGeometryFactorData G larger η i) := by
  letI : LocallyConvexSpace ℝ (StateDirections W.S × ℝ) :=
    (sectorPairGrading_withSeminorms W.S).toLocallyConvexSpace
  let uniformData := n04PositiveGeometry_sourceAngleTrace_uniform_prefix
    W X hb hε hεW hεone hflow
  refine ⟨uniformData.choose, uniformData.choose_spec.1, ?_⟩
  intro larger hlarge η hη hηhalf i
  let U := sectorNeighborhood W.S larger η η
  have hU : IsOpen U := sectorNeighborhood_isOpen W.S larger η η
  have hc : Convex ℝ U := sectorNeighborhood_convex W.S larger η η
  have hbase : base ≤ larger := uniformData.choose_spec.1.trans hlarge
  have hsub : U ⊆ sectorNeighborhood W.S base ε ε :=
    sectorNeighborhood_mono W.S hbase hη hη
  have hsubProd : U ×ˢ (univ : Set ℝ) ⊆ sectorNeighborhood W.S base ε ε ×ˢ univ :=
    fun y hy => ⟨hsub hy.1, hy.2⟩
  have hzG (x : StateDirections W.S × ℝ) (hx : x ∈ U) :
      liftSectorParameter W.S W.C x ∈ stateNeighborhood W.S W.C G.base G.ε :=
    stateNeighborhood_mono W.S W.C hGb hGε
      (liftSectorParameter_mem_stateNeighborhood (C := W.C) (hsub hx) le_rfl)
  have hs (x : StateDirections W.S × ℝ) :
      stateSector W.S (liftSectorParameter W.S W.C x).1 :=
    W.through03.1.1.2.2.1.liftSectorParameter_sector x
  let src (side : Bool) := n04PositiveGeometry_source_some W X i side
  let m (side : Bool) : ℕ := (src side).choose
  have hm (side : Bool) : (X.src i side).val = some (m side) := (src side).choose_spec
  let Jψ (side : Bool) (j : Fin (n + 2)) : SmoothDirections (U ×ˢ univ)
      (n04PositiveGeometry_sourceAngleTrace W X i side j) :=
    (n04PositiveGeometry_sourceAngleTrace_joint hb hε hεW hεone hflow
      i side (m side) (hm side) (hctx (m side) (!side)) j (by omega)).restrict
      (hU.prod isOpen_univ) hsubProd
  let JX (side : Bool) (j : Fin (n + 2)) : SmoothDirections (U ×ˢ univ)
      (n04PositiveGeometry_sourceRadialTrace W X i side j) :=
    (n04PositiveGeometry_sourceRadialTrace_joint hb hε hεW hεone hflow
      i side (m side) (hm side) (hctx (m side) (!side)) j (by omega)).restrict
      (hU.prod isOpen_univ) hsubProd
  let ψ := fun (x : StateDirections W.S × ℝ) side p =>
    (n04PositiveSourceMap (X.src i side) (W.A X.e₀) (liftSectorParameter W.S W.C x) p).2
  let radialSource := fun (x : StateDirections W.S × ℝ) side p =>
    (n04PositiveSourceMap (X.src i side) (W.A X.e₀) (liftSectorParameter W.S W.C x) p).1
  have ho := G.buffer.ordered i
  let factors := n04PositiveGeometry_oneSidedTransportFactorDirections
    (W.hS.2.1 (3 / 4 : ℝ)) W.hT W.through03.1.1.1.1 (by norm_num)
    ((W.hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2) hU hc n
    ho.1 (ho.2.1.trans (ho.2.2.1.trans ho.2.2.2.1)) ho.2.2.2.2
    (half_pos (inv_pos.mpr (zero_lt_one.trans_le (G.input_one i))))
    (zero_le_one.trans (G.inverse_one i)) ψ radialSource
    (fun x hx side j => n04PositiveGeometry_sourceAngleTrace_contDiff (X := X)
      (hb.trans hbase) (hη.trans hεW) i side j hx)
    (fun x hx side j => n04PositiveGeometry_sourceAngleTrace_period (X := X)
      (hb.trans hbase) (hη.trans hεW) i side j hx)
    (fun side j b θ => smoothDirections_angularStateSlice (Jψ side j) b θ)
    (fun side j b => uniformData.choose_spec.2 larger hlarge η hη hηhalf
      i side (m side) (hm side) (hctx (m side) (!side)) j (by omega) (Jψ side j) b)
    JX
    (fun x hx side θ => (n04Coordinates_actualAtlas_positiveEndpoint_of_source
      W.hT W.hS W.through03 W.field X.e₀ (X.src i side)
      (stateNeighborhood_mono W.S W.C G.base_le G.radius_le (hzG x hx))
      (hs x)).root_radial θ)
    (fun x hx r θ => n04PositiveGeometry_controlled_angle_positive G (hzG x hx) (hs x) i r θ)
    (fun x hx side θ => lt_of_lt_of_le
      (by have hpos := inv_pos.mpr (zero_lt_one.trans_le (G.input_one i)); linarith only [hpos])
      (G.coefficient_lower _ (hzG x hx) (hs x) i side θ))
    (fun x hx side j θ => lt_of_le_of_lt
      (G.coefficient_bound _ (hzG x hx) (hs x) i side (j + 1) (by omega) (by omega) θ)
      (by have hpos := zero_lt_one.trans_le (G.inverse_one i); linarith only [hpos]))
  exact ⟨{
    angle := factors.1
    angleInverse := factors.2.1
    radial := factors.2.2.1
    radialInverse := factors.2.2.2.1
    coefficients := factors.2.2.2.2.1
    transport := factors.2.2.2.2.2.1
    inverseTransport := factors.2.2.2.2.2.2 }⟩

end ContinuousFlexibility.Analysis
