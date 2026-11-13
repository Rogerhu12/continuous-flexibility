import ContinuousFlexibility.Analysis.N04NegativeChartRootFlowFactory
import ContinuousFlexibility.Analysis.N04NegativeChartRootLabelRepresentative
import ContinuousFlexibility.Analysis.N04NegativeChartRootCoefficient
import ContinuousFlexibility.Analysis.N04NegativeChartProjectionAffineBounds
import ContinuousFlexibility.Analysis.N04NegativeChartPartialJets
import ContinuousFlexibility.Analysis.N04NegativeChartInteriorRawBudget

/-! One finite plot carries the actual divided fields, endpoint label and
their single inverse flow on a common open convex state neighborhood. -/

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub
  interiorRaw_parameterTopology interiorRaw_parameterAddGroup interiorRaw_parameterSMul

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}

/-- No derivative estimate on an extension is stored in this package.
Every equality holds on the complete physical half or angular fiber. -/
structure NegativeRootRepresentative (F : W.NegativeOpticalFactors e)
    {n : ℕ} (base : ℕ) (ε : ℝ) (z : Parameter W.S)
    (L : (Fin n → ℝ) →L[ℝ] Parameter W.S) (m : ℕ) (side : Bool) (δ : ℝ) where
  d : (Fin n → ℝ) × PolarPoint → ℝ
  c : (Fin n → ℝ) × PolarPoint → ℝ
  hd : ContDiff ℝ ∞ d
  hc : ContDiff ℝ ∞ c
  dp : ∀ y r, Function.Periodic (fun θ => d (y, (r, θ))) Real.pi
  cp : ∀ y r, Function.Periodic (fun θ => c (y, (r, θ))) Real.pi
  flow : NegativeChartRootFlowData d c δ
  h : (Fin n → ℝ) × ℝ → ℝ
  hh : ContDiff ℝ ∞ h
  V : Set (Fin n → ℝ)
  open_V : IsOpen V
  convex_V : Convex ℝ V
  zero_V : (0 : Fin n → ℝ) ∈ V
  sector : ∀ y ∈ V, z + L y ∈ sectorNeighborhood W.S base ε ε
  fields : ∀ y ∈ V, ∀ p : PolarPoint,
    p.1 ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) →
    d (y, p) = F.fullHalfDrift (liftSectorParameter W.S W.C (z + L y)) m side p ∧
    c (y, p) = F.fullHalfSpeed (liftSectorParameter W.S W.C (z + L y)) m side p
  label : ∀ y ∈ V, ∀ θ, h (y, θ) =
    n01RootLabel W.S W.C (liftSectorParameter W.S W.C (z + L y)) m side θ

/-- Construct the same flow and label once, independently of every
derivative order subsequently evaluated on this finite plot. -/
theorem negativeRootRepresentative_nonempty (F : W.NegativeOpticalFactors e)
    {n base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : ε ≤ W.ε / 2)
    (z : Parameter W.S) (hz : z ∈ sectorNeighborhood W.S base ε ε)
    (L : (Fin n → ℝ) →L[ℝ] Parameter W.S) (m : ℕ) (side : Bool) (δ : ℝ) :
    Nonempty (NegativeRootRepresentative F base ε z L m side δ) := by
  have hεW : ε ≤ W.ε := hε.trans (by linarith only [W.ε_pos])
  have hzW := sectorNeighborhood_mono W.S hb hεW hεW hz
  have hzstate := liftSectorParameter_mem_stateNeighborhood (C := W.C)
    (sectorNeighborhood_mono W.S hb hε hε hz) le_rfl
  let A := (sectorParameterInclusion W.S).comp L
  have ha (y : Fin n → ℝ) :
      liftSectorParameter W.S W.C (z + L y) = liftSectorParameter W.S W.C z + A y := by
    simp only [liftSectorParameter_eq_affine, map_add, A,
      ContinuousLinearMap.comp_apply, add_assoc]
  have hfields := F.fullHalfFields_finiteRootFlow
    (liftSectorParameter W.S W.C z) hzstate A m side δ
  let d := hfields.choose
  let c := hfields.choose_spec.choose
  have hd := hfields.choose_spec.choose_spec
  have hfieldV := hd.2.2.2.2.2.1
  let Vf := hfieldV.choose
  have hvf := hfieldV.choose_spec
  have hlabel := W.negativeRootLabel_finiteRepresentative z hzW L m side
  let h := hlabel.choose
  have hl := hlabel.choose_spec
  let Vl := hl.2.choose
  have hvl := hl.2.choose_spec
  let Vs := (fun y => z + L y) ⁻¹' sectorNeighborhood W.S base ε ε
  have hVs : IsOpen Vs := (sectorNeighborhood_isOpen W.S base ε ε).preimage
    (continuous_const.add L.continuous)
  have h0s : (0 : Fin n → ℝ) ∈ Vs := by
    simpa only [Vs, mem_preimage, map_zero, add_zero] using hz
  have h0 : (0 : Fin n → ℝ) ∈ Vf ∩ Vl ∩ Vs := ⟨⟨hvf.2.1, hvl.2.1⟩, h0s⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (((hvf.1.inter hvl.1).inter hVs).mem_nhds h0)
  refine ⟨{
    d := d, c := c, hd := hd.1, hc := hd.2.1,
    dp := hd.2.2.1, cp := hd.2.2.2.1, flow := hd.2.2.2.2.2.2.some,
    h := h, hh := hl.1, V := Metric.ball 0 r,
    open_V := Metric.isOpen_ball, convex_V := convex_ball 0 r,
    zero_V := Metric.mem_ball_self hr,
    sector := fun y hy => (hball hy).2,
    fields := ?_, label := ?_ }⟩
  · intro y hy p hp
    have he := hvf.2.2.2 y (hball hy).1.1 p hp
    rw [ha y]
    exact he
  · exact fun y hy θ => hvl.2.2.2 y (hball hy).1.2 θ

namespace NegativeRootRepresentative

variable {F : W.NegativeOpticalFactors e} {n base : ℕ} {ε δ : ℝ}
  {z : Parameter W.S} {L : (Fin n → ℝ) →L[ℝ] Parameter W.S}
  {m : ℕ} {side : Bool} (A : NegativeRootRepresentative F base ε z L m side δ)

/-- The normalized coordinate uses the supplied inverse and its actual
endpoint label; the initial angle is removed before taking projections. -/
def coordinate (y : Fin n → ℝ) (q : ℝ × ℝ × ℝ) : ℝ :=
  A.h (y, A.flow.inverse y (q.1, Real.sqrt δ * q.2.1) 1 q.2.2) - q.2.2

theorem coordinate_joint_contDiff :
    ContDiff ℝ ∞ (fun x : (Fin n → ℝ) × (ℝ × ℝ × ℝ) => A.coordinate x.1 x.2) := by
  have harg : ContDiff ℝ ∞
      (fun x : (Fin n → ℝ) × (ℝ × ℝ × ℝ) =>
        ((x.1, (x.2.1, Real.sqrt δ * x.2.2.1)), ((1 : ℝ), x.2.2.2))) :=
    (contDiff_fst.prodMk (contDiff_snd.fst.prodMk
      (contDiff_const.mul contDiff_snd.snd.fst))).prodMk
      (contDiff_const.prodMk contDiff_snd.snd.snd)
  have hflow : ContDiff ℝ ∞
      (fun x : (Fin n → ℝ) × (ℝ × ℝ × ℝ) =>
        A.flow.inverse x.1 (x.2.1, Real.sqrt δ * x.2.2.1) 1 x.2.2.2) := by
    simpa only [negativeChartRootPlotTimeChange, compactScalarFlowTime_one]
      using A.flow.inverse_smooth.comp harg
  exact (A.hh.comp (contDiff_fst.prodMk hflow)).sub contDiff_snd.snd.snd

theorem coordinate_actual (y : Fin n → ℝ) (hy : y ∈ A.V) :
    A.coordinate y = fun q => W.negativeRootInverseCoordinate A.flow
      (liftSectorParameter W.S W.C (z + L y)) m side y q - q.2.2 := by
  funext q
  exact congrArg (fun a : ℝ => a - q.2.2) (A.label y hy _)

set_option diagnostics true in
/-- Both exact projection identities hold on the same open state and
spatial neighborhood, so all later mixed jets use that single germ. -/
theorem projection_eq (hb : W.base ≤ base) (hε : ε ≤ W.ε / 2)
    (hδ : 0 < δ) (hband : δ * 2 ≤ W.negativeMaterialCollar m)
    (odd : Bool) (y : Fin n → ℝ) (hy : y ∈ A.V)
    (p : PolarPoint) (hp : p.1 ∈ Ioo (0 : ℝ) 2) :
    (if odd then W.negativeRootTravelCoefficient m side δ (z + L y) p
      else W.negativeRootAngleDefect m side δ (z + L y) p) =
      if odd then rootOddCoefficient (A.coordinate y) p else rootEven (A.coordinate y) p := by
  have hz := liftSectorParameter_mem_stateNeighborhood (C := W.C)
    (sectorNeighborhood_mono W.S hb hε hε (A.sector y hy)) le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector (z + L y)
  cases odd with
  | false =>
    exact (F.fullHalfFields_root_angle_defect A.hd A.hc A.dp A.cp
      A.flow y (z := z + L y) hz hs m side (by norm_num : (0 : ℝ) < 2) hδ hband
      (A.fields y hy) (p := p) ⟨hp.1, hp.2.le⟩).trans
        (congrArg (fun g => rootEven g p) (A.coordinate_actual y hy).symm)
  | true =>
    exact (F.fullHalfFields_root_coefficient A.hd A.hc A.dp A.cp
      A.flow y (z := z + L y) hz hs m side (by norm_num : (0 : ℝ) < 2) hδ hband
      (A.fields y hy) (p := p) ⟨hp.1, hp.2.le⟩).trans
        (congrArg (fun g => rootOddCoefficient g p) (A.coordinate_actual y hy).symm)

/-- A bound for the finite coordinate returns a bound for any actual
mixed tower. Its displayed projection constant precedes the component,
state, representatives and every supplied flow. -/
theorem projection_bound (s : ℕ) (hb : W.base ≤ base) (hε : ε ≤ W.ε / 2)
    (hδ : 0 < δ) (hband : δ * 2 ≤ W.negativeMaterialCollar m)
    (odd : Bool) (k : ℕ) (v : Fin k → (Fin n → ℝ)) {M : ℝ} (hM : 0 ≤ M)
    (a b : ℕ) (hab : a + b ≤ s)
    (hraw : CSBound (a + b + if odd then 1 else 0)
      (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ (univ : Set ℝ))
      (fun q => iteratedFDeriv ℝ k (fun y => A.coordinate y q) 0 v) M)
    (p : PolarPoint) (hp : p.1 ∈ Ioc (0 : ℝ) 1)
    (J : SmoothDirections (sectorNeighborhood W.S base ε ε)
      (fun x => mixedDerivative a b (fun q =>
        if odd then W.negativeRootTravelCoefficient m side δ x q
        else W.negativeRootAngleDefect m side δ x q) p)) :
    |J.D k z (fun i => L (v i))| ≤
      (n04NegativeChart_rootProjection_affine_bound
        (X := Parameter W.S) (P := Fin n → ℝ) s).choose * M := by
  let U := sectorNeighborhood W.S base ε ε
  let Ω : Set PolarPoint := Ioo (0 : ℝ) 2 ×ˢ univ
  let f : Parameter W.S × PolarPoint → ℝ := fun x =>
    if odd then W.negativeRootTravelCoefficient m side δ x.1 x.2
      else W.negativeRootAngleDefect m side δ x.1 x.2
  have hU : IsOpen U := sectorNeighborhood_isOpen W.S base ε ε
  have hΩ : IsOpen Ω := isOpen_Ioo.prod isOpen_univ
  have hεW : ε ≤ W.ε := hε.trans (by linarith only [W.ε_pos])
  have hsub : U ⊆ sectorNeighborhood W.S W.base W.ε W.ε :=
    sectorNeighborhood_mono W.S hb hεW hεW
  have hc : δ * 2 ≤ W.C.right m - W.C.left m := by
    have hhalf := (W.negativeMaterialCollar_bounds m).2.2.2 side
    have hwidth := W.negativeOpticalWidth_le_component m side
    have hwpos := W.negativeOpticalWidth_pos m side
    linarith only [hband, hhalf, hwidth, hwpos]
  let JF : SmoothDirections (U ×ˢ Ω) f := by
    cases odd
    · exact (W.negativeRootAngleDefectJointTower m side hδ hc).restrict
        (hU.prod hΩ) (fun _ hx => ⟨hsub hx.1, hx.2⟩)
    · exact (W.negativeRootTravelCoefficientJointTower m side hδ hc).restrict
        (hU.prod hΩ) (fun _ hx => ⟨hsub hx.1, hx.2⟩)
  have hj := n04NegativeChart_partial_stateJet_contDiff A.coordinate_joint_contDiff k 0 v
  exact (n04NegativeChart_rootProjection_affine_bound
    (X := Parameter W.S) (P := Fin n → ℝ) s).choose_spec.2
    odd U hU Ω hΩ ((convex_Ioo _ _).prod convex_univ) (fun _ hx => hx.1.1)
    f JF z L A.V A.open_V A.convex_V A.zero_V A.sector
    A.coordinate (fun q => A.coordinate_joint_contDiff.comp
      (contDiff_id.prodMk contDiff_const))
    (fun y hy q hq => A.projection_eq hb hε hδ hband odd y hy q hq.1)
    k v hj M hM a b hab hraw p ⟨⟨hp.1, hp.2.trans_lt (by norm_num)⟩, mem_univ _⟩ hp J

end NegativeRootRepresentative

end ContinuousFlexibility.Analysis.N04RealizationStart

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeRootRepresentative_nonempty'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeRootRepresentative_nonempty

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeRootRepresentative.projection_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeRootRepresentative.projection_eq

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeRootRepresentative.projection_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeRootRepresentative.projection_bound
