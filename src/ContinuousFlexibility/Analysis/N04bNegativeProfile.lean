import ContinuousFlexibility.Analysis.N04bProfileLine
import ContinuousFlexibility.Analysis.N04bSingletonType
import ContinuousFlexibility.Analysis.N04bSqrtCrossing
import ContinuousFlexibility.Analysis.SmoothDirectionsScalarLine

/-!
# Strict negativity of the actual profile on negative components

At `q = 0`, the actual ordinary flow is the initial angle minus the
optical travel. Its first radial jet is therefore minus the actual
optical speed. N01 gives this jet a smooth directional tower in the
state parameters. Combined with the affine radicand identity, that
regularity excludes a zero crossing anywhere in the state neighborhood.

The `mixedDerivative 1 0` appearing in `ordinaryFlowFamily` is the
ordinary one-dimensional radial derivative from `Statements.Analysis`.
Its value below is obtained from the actual radial coefficients and ODE;
no differentiability of an arbitrary totalized coefficient is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

local instance n04bNegativeProfileStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

private theorem n04b_smoothDirections_differentiableAt_line
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {f : E → ℝ} (J : SmoothDirections U f)
    (x w : E) {t : ℝ} (ht : x + t • w ∈ U) :
    DifferentiableAt ℝ (fun s : ℝ => f (x + s • w)) t := by
  have hjet := J.hasDerivAt_line_jet x w 0 Fin.elim0 ht
  have hline : Continuous (fun s : ℝ => x + s • w) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hmem : ∀ᶠ s in 𝓝 t, x + s • w ∈ U :=
    hline.continuousAt.eventually (J.open_domain.mem_nhds ht)
  apply hjet.differentiableAt.congr_of_eventuallyEq
  filter_upwards [hmem] with s hs
  exact (J.zero _ hs).symm

theorem n04b_ordinaryFlowFamily_radial_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {x : AnnularState S} (hx : (x, (0 : ℝ)) ∈ stateNeighborhood S C base ε)
    (m : ℕ) {p : PolarPoint} (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    ordinaryFlowFamily S C m 1 0 p (x, 0) =
      -opticalSpeed (stateProfile D S C x) p.1 +
        opticalSpeed (stateProfile D S C C.referenceState) p.1 := by
  exact (hN.n04b_ordinaryFlowFamily_radial_zero hS hT hx m p.2 hp).trans
    (by ring)

/-- N01 supplies genuine scalar differentiability of the actual optical
speed at every point of the state line that lies in its open domain. -/
theorem n04b_opticalSpeed_stateLine_differentiableAt
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (x : AnnularState S) (m : ℕ) {r : ℝ}
    (hr : r ∈ Ioo (C.left m) (C.right m)) {t : ℝ}
    (ht : (n04bStateLine C x t, (0 : ℝ)) ∈ stateNeighborhood S C base ε) :
    DifferentiableAt ℝ
      (fun s : ℝ => opticalSpeed (stateProfile D S C (n04bStateLine C x s)) r) t := by
  -- N01's flow clause chooses the loss after the parameter order; `obtain` on
  -- these existentials is very slow, so the witnesses are selected.
  let orderData := hN.2.2.2.2.2.2.2.2.2.2.2.2 0
  let hJ := (orderData.choose_spec 1).choose_spec.2
  let J := (hJ m 1 0 (r, 0) (by norm_num) hr).choose
  have ht' : (C.referenceState, (0 : ℝ)) +
      t • (x - C.referenceState, (0 : ℝ)) ∈ stateNeighborhood S C base ε := by
    rw [n04bStateLine_joint]
    exact ht
  have hline := n04b_smoothDirections_differentiableAt_line J
    (C.referenceState, (0 : ℝ)) (x - C.referenceState, (0 : ℝ)) ht'
  have hf : DifferentiableAt ℝ
      (fun s : ℝ => ordinaryFlowFamily S C m 1 0 (r, 0)
        (n04bStateLine C x s, (0 : ℝ))) t := by
    simpa only [n04bStateLine_joint] using hline
  have hcontinuous : Continuous
      (fun s : ℝ => (n04bStateLine C x s, (0 : ℝ))) := by
    have hc : Continuous (fun s : ℝ => (C.referenceState, (0 : ℝ)) +
        s • (x - C.referenceState, (0 : ℝ))) :=
      continuous_const.add (continuous_id.smul continuous_const)
    exact hc.congr (fun s => n04bStateLine_joint C x s)
  have hmem : ∀ᶠ s in 𝓝 t,
      (n04bStateLine C x s, (0 : ℝ)) ∈ stateNeighborhood S C base ε :=
    hcontinuous.continuousAt.eventually (J.open_domain.mem_nhds ht)
  apply (hf.const_sub (opticalSpeed (stateProfile D S C C.referenceState) r)).congr_of_eventuallyEq
  filter_upwards [hmem] with s hs
  rw [n04b_ordinaryFlowFamily_radial_zero hN hS hT hs m (p := (r, 0)) hr]
  ring

theorem n04b_stateProfile_radicand_pos
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {x : AnnularState S} (hx : (x, (0 : ℝ)) ∈ stateNeighborhood S C base ε)
    (m : ℕ) {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    0 < -deriv (stateProfile D S C x) r / (r * stateProfile D S C x r) := by
  obtain ⟨_, hbounds⟩ := hN.1.1
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hrD : r ∈ Ioo D.a D.b :=
    ⟨(hC.1 m).1.trans hr.1, hr.2.trans (hC.1 m).2.2⟩
  have hbase : 0 < -deriv D.w r / (r * D.w r) :=
    div_pos (neg_pos.mpr (hC.2.2.2.1 m r hr))
      (mul_pos (hbounds.1.1.trans hrD.1) (hbounds.1.2.2.2.2.1 r hrD))
  rw [n04b_stateProfile_radicand_on_component hN x m hr]
  apply n04b_affine_pos_of_sqrt_differentiable hbase
  intro t ht
  have hregular := n04b_opticalSpeed_stateLine_differentiableAt hN hS hT x m hr
    (n04bStateLine_mem_stateNeighborhood hN.2.1 hx.1 ht)
  simpa only [opticalSpeed, n04b_stateProfile_radicand_stateLine hN x m hr] using hregular

/-- The reference negative components remain strictly negative for the
same actual profile throughout the original N01 neighborhood. -/
theorem n04b_stateProfile_deriv_neg
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {x : AnnularState S} (hx : (x, (0 : ℝ)) ∈ stateNeighborhood S C base ε)
    (m : ℕ) {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    deriv (stateProfile D S C x) r < 0 := by
  obtain ⟨_, hbounds⟩ := hN.1.1
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hrD : r ∈ Ioo D.a D.b :=
    ⟨(hC.1 m).1.trans hr.1, hr.2.trans (hC.1 m).2.2⟩
  have hwp : 0 < stateProfile D S C x r :=
    mul_pos (hbounds.1.2.2.2.2.1 r hrD) (Real.exp_pos _)
  exact neg_pos.mp ((div_pos_iff_of_pos_right
    (mul_pos (hbounds.1.1.trans hrD.1) hwp)).mp
      (n04b_stateProfile_radicand_pos hN hS hT hx m hr))

private theorem n04b_seminorm_double_affine_lt {E : Type*}
    [AddCommGroup E] [Module ℝ E] (p : Seminorm ℝ E) (x₀ x : E)
    {ε : ℝ} (hx : p (x - x₀) < ε / 2) :
    p ((x₀ + (2 : ℝ) • (x - x₀)) - x₀) < ε := by
  rw [add_sub_cancel_left, map_smul_eq_mul,
    Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  linarith only [hx]

/-- One halving of the state radius gives a relative lower bound, with
no component-dependent shrinking and no lower bound assumed on `w'`. -/
theorem n04b_stateProfile_radicand_reference_half_lt
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {x : AnnularState S}
    (hx : stateGrading S base (x - C.referenceState) < ε / 2)
    (m : ℕ) {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    (-deriv D.w r / (r * D.w r)) / 2 <
      -deriv (stateProfile D S C x) r / (r * stateProfile D S C x r) := by
  have hdouble : (n04bStateLine C x 2, (0 : ℝ)) ∈ stateNeighborhood S C base ε := by
    constructor
    · exact n04b_seminorm_double_affine_lt
        (stateGrading S base) C.referenceState x hx
    · simpa only [abs_zero] using hN.2.1
  have hpositive := n04b_stateProfile_radicand_pos hN hS hT hdouble m hr
  rw [n04b_stateProfile_radicand_stateLine hN x m hr] at hpositive
  rw [n04b_stateProfile_radicand_on_component hN x m hr]
  linarith

end ContinuousFlexibility.Statements
