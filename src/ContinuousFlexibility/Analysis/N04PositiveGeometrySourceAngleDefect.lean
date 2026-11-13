import ContinuousFlexibility.Analysis.N04PositiveGeometryLabelDefectSampleBridge
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledRootLabelPrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointValues
import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundary
import ContinuousFlexibility.Analysis.N04PositiveGeometryRightSource

/-!
# The actual angular endpoint displacement

The zeroth angular coefficient of the source is its original inverse
root label minus the angle. Its genuine tower and sampled word bound
include the zeroth value. Positive radial orders use the same literal
trace definition, with no angular subtraction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

def n04PositiveGeometry_sourceAngleTrace
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool) (j : ℕ)
    (y : (StateDirections W.S × ℝ) × ℝ) : ℝ :=
  radialBoundaryJet (fun p =>
    (n04PositiveSourceMap (X.src i side) (W.A X.e₀) (liftSectorParameter W.S W.C y.1) p).2)
    (n04PositiveEndpoint i side) j y.2 - if j = 0 then y.2 else 0

theorem n04PositiveGeometry_sourceAngleTrace_zero_eq
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hεW : ε ≤ W.ε)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool)
    (m : ℕ) (hm : (X.src i side).val = some m)
    {z : StateDirections W.S × ℝ} (hz : z ∈ sectorNeighborhood W.S base ε ε) (θ : ℝ) :
    n04PositiveGeometry_sourceAngleTrace W X i side 0 (z, θ) =
      Function.invFun (n01RootLabel W.S W.C (liftSectorParameter W.S W.C z) m (!side)) θ - θ := by
  have hzW := liftSectorParameter_mem_stateNeighborhood (C := W.C)
    (sectorNeighborhood_mono W.S hb hεW hεW hz) le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have h := n04PositiveGeometry_source_endpoint_value W X i side m hm hzW hs θ
  simpa only [n04PositiveGeometry_sourceAngleTrace, radialBoundaryJet,
    iteratedDeriv_zero, ite_true] using congrArg (fun p : PolarPoint => p.2 - θ) h

def n04PositiveGeometry_sourceAngleTrace_zero_joint
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hεW : ε ≤ W.ε)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool) :
    SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (n04PositiveGeometry_sourceAngleTrace W X i side 0) := by
  let J := n04PositiveGeometry_sourceBoundaryAngleDefect_jointDirections
    W.hT W.hS W.through03 W.field X.e₀ (X.src i side)
  have hsub : (sectorNeighborhood W.S base ε ε ×ˢ (univ : Set ℝ)) ⊆
      sectorNeighborhood W.S W.base W.ε W.ε ×ˢ univ :=
    fun y hy => ⟨sectorNeighborhood_mono W.S hb hεW hεW hy.1, hy.2⟩
  exact (smoothDirectionsRestrict J
    ((sectorNeighborhood_isOpen W.S base ε ε).prod isOpen_univ) hsub).congrOn
      (fun y _ => by simp only [n04PositiveGeometry_sourceAngleTrace,
        radialBoundaryJet, iteratedDeriv_zero, ite_true])

theorem n04PositiveGeometry_sourceAngleTrace_zero_sample_prefix
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε) (hεW : ε ≤ W.ε)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i side, ∀ Q : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (n04PositiveGeometry_sourceAngleTrace W X i side 0),
      ∀ z ∈ sectorNeighborhood W.S base ε ε,
      pairGrading (sectorGrading W.S) realGrading low z ≤ 1 → ∀ θ : ℝ,
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) z ≤ R →
      N04BoundaryWordBounds Q K s 1 z θ
        (fun v => pairGrading (sectorGrading W.S) realGrading low v ≤ 1 ∧
          pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) v ≤ R)
        (A * W.U.E0 (W.U.sample (X.cell i)) ^ A)
        (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ))
        (R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))) shift := by
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  let data := n04PositiveGeometry_labelDefect_sample_bridge W X base ε 5
    (fun side m y => Function.invFun
      (n01RootLabel W.S W.C (liftSectorParameter W.S W.C y.1) m side) y.2 - y.2)
    (n04PositiveGeometry_rootInverseDefect_fixedBase_prefix_of_flow W.hT W.hS hN hflow)
  let heightData := n04PositiveGeometry_sample_height_bound W X
    (by norm_num : (0 : ℝ) < 3 / 4)
  refine ⟨data.choose, data.choose_spec.1, fun K => ?_⟩
  let prefix := data.choose_spec.2 K
  refine ⟨prefix.choose, fun s => ?_⟩
  let orderData := prefix.choose_spec s
  refine ⟨orderData.choose, orderData.choose_spec.1, ?_⟩
  intro i side Q z hz hzlow θ R hR hzR
  let source := n04PositiveGeometry_source_some W X i side
  let m : ℕ := source.choose
  have hm : (X.src i side).val = some m := source.choose_spec
  let Qδ := Q.congrOn (fun y hy =>
    n04PositiveGeometry_sourceAngleTrace_zero_eq W X hb hεW i side m hm hy.1 y.2)
  have hraw := orderData.choose_spec.2 i side m hm Qδ z hz hzlow θ R hR hzR
  have hE : 1 ≤ W.U.E0 (W.U.sample (X.cell i)) :=
    (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hM : 0 ≤ orderData.choose * W.U.E0 (W.U.sample (X.cell i)) ^ orderData.choose :=
    mul_nonneg (zero_le_one.trans orderData.choose_spec.1)
      (Real.rpow_nonneg (zero_le_one.trans hE) _)
  have hreserve := hraw.reserve hM (heightData.choose_spec.2 i).1
    (Real.one_le_rpow hR (by positivity)) (by decide : 1 ≤ 5)
  exact hreserve.congr hz (fun y hy =>
    (n04PositiveGeometry_sourceAngleTrace_zero_eq W X hb hεW i side m hm hy.1 y.2).symm)

end ContinuousFlexibility.Analysis
