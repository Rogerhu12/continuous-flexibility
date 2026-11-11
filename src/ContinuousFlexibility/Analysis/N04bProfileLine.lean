import ContinuousFlexibility.Analysis.N01RadialFlow
import ContinuousFlexibility.Analysis.SpacesSources

/-!
# The actual profile on a line from the reference state

On a negative component every other control and the positive border
control vanish. The logarithmic profile therefore contains precisely
one scalar control amplitude. The reference conditions and linearity of
the circle decoder make that amplitude affine on the actual state line.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

local instance n04bProfileLineStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

def n04bStateLine {S : PhysicalSpacesData} (C : NonlinearGeometryData S)
    (x : AnnularState S) (t : ℝ) : AnnularState S :=
  C.referenceState + t • (x - C.referenceState)

theorem n04bStateLine_zero {S : PhysicalSpacesData} (C : NonlinearGeometryData S)
    (x : AnnularState S) : n04bStateLine C x 0 = C.referenceState := by
  simp only [n04bStateLine, zero_smul, add_zero]

theorem n04bStateLine_one {S : PhysicalSpacesData} (C : NonlinearGeometryData S)
    (x : AnnularState S) : n04bStateLine C x 1 = x := by
  simp only [n04bStateLine, one_smul, add_sub_cancel]

theorem n04bStateLine_joint {S : PhysicalSpacesData} (C : NonlinearGeometryData S)
    (x : AnnularState S) (t : ℝ) :
    (C.referenceState, (0 : ℝ)) + t • (x - C.referenceState, (0 : ℝ)) =
      (n04bStateLine C x t, (0 : ℝ)) := by
  change (C.referenceState + t • (x - C.referenceState), (0 : ℝ) + t • 0) = _
  simp only [n04bStateLine, smul_zero, add_zero]

private theorem n04b_seminorm_affine_difference {E : Type*}
    [AddCommGroup E] [Module ℝ E] (p : Seminorm ℝ E) (x v : E) (t : ℝ) :
    p ((x + t • v) - x) = |t| * p v := by
  rw [add_sub_cancel_left, map_smul_eq_mul, Real.norm_eq_abs]

theorem n04bStateLine_mem_stateNeighborhood
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hε : 0 < ε) {x : AnnularState S}
    (hx : stateGrading S base (x - C.referenceState) < ε)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (n04bStateLine C x t, (0 : ℝ)) ∈ stateNeighborhood S C base ε := by
  constructor
  · have ht' : |t| ≤ 1 := by
      rw [abs_of_nonneg ht.1]
      exact ht.2
    exact lt_of_eq_of_lt
      (n04b_seminorm_affine_difference (stateGrading S base)
        C.referenceState (x - C.referenceState) t)
      ((mul_le_of_le_one_left (apply_nonneg (stateGrading S base)
        (x - C.referenceState)) ht').trans_lt hx)
  · simpa only [abs_zero] using hε

theorem n04b_stateKappa_stateLine
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (href : referenceStateConditions D S C) (x : AnnularState S) (m : ℕ) (t : ℝ) :
    stateKappa S (n04bStateLine C x t) m = t * stateKappa S x m := by
  have hzero : C.referenceState.2.2.1 = 0 := href.2.2.2.1
  have hcoord : (n04bStateLine C x t).2.2.1 = t • x.2.2.1 := by
    change C.referenceState.2.2.1 +
      t • (x.2.2.1 - C.referenceState.2.2.1) = t • x.2.2.1
    rw [hzero, sub_zero, zero_add]
  have hdecode : (S.circle (3 / 4 : ℝ)).decode (n04bStateLine C x t).2.2.1 m =
      fun θ => t * (S.circle (3 / 4 : ℝ)).decode x.2.2.1 m θ := by
    rw [hcoord]
    exact congrFun ((S.circle (3 / 4 : ℝ)).decode.map_smul t x.2.2.1) m
  change angularMean ((S.circle (3 / 4 : ℝ)).decode (n04bStateLine C x t).2.2.1 m) =
    t * angularMean ((S.circle (3 / 4 : ℝ)).decode x.2.2.1 m)
  rw [hdecode]
  exact spaces_angularMean_const_mul t ((S.circle (3 / 4 : ℝ)).decode x.2.2.1 m)

private theorem n04b_control_zero_other
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions D S C) {m n : ℕ} (hmn : n ≠ m)
    {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) : C.control n r = 0 := by
  by_contra hn
  have hnr : r ∈ Ioo (C.left n) (C.right n) := (hC.2.2.2.2.2.1 n).2.2 hn
  exact Set.disjoint_left.mp (hC.2.2.1 n m hmn) hnr hr

theorem n04b_stateProfile_on_component
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (x : AnnularState S) (m : ℕ)
    {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    stateProfile D S C x r = D.w r * Real.exp (stateKappa S x m * C.control m r) := by
  have hborder : D.chi r = 0 := by
    by_contra hχ
    have hp : 0 < deriv D.w r := (hN.1.2.2.2.1.2.2.1 hχ).2
    have hn := hN.2.2.2.1.2.2.2.1 m r hr
    exact (not_lt_of_ge hp.le) hn
  have hsum : (∑' n, stateKappa S x n * C.control n r) =
      stateKappa S x m * C.control m r := by
    apply tsum_eq_single m
    intro n hn
    rw [n04b_control_zero_other hN.2.2.2.1 hn hr, mul_zero]
  simp only [stateProfile, hborder, mul_zero, zero_add, hsum]

theorem n04b_stateProfile_radicand_on_component
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (x : AnnularState S) (m : ℕ)
    {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    -deriv (stateProfile D S C x) r / (r * stateProfile D S C x r) =
      -deriv D.w r / (r * D.w r) + stateKappa S x m * (-deriv (C.control m) r / r) := by
  obtain ⟨_, hbounds⟩ := hN.1.1
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hrD : r ∈ Ioo D.a D.b :=
    ⟨(hC.1 m).1.trans hr.1, hr.2.trans (hC.1 m).2.2⟩
  have hr0 : r ≠ 0 := (hbounds.1.1.trans hrD.1).ne'
  have hw0 : D.w r ≠ 0 := (hbounds.1.2.2.2.2.1 r hrD).ne'
  have hw : DifferentiableAt ℝ D.w r := hbounds.1.2.2.1.1.differentiable (by simp) r
  have hc : DifferentiableAt ℝ (C.control m) r :=
    (hC.2.2.2.2.2.1 m).1.differentiable (by simp) r
  have heq : stateProfile D S C x =ᶠ[𝓝 r]
      fun s => D.w s * Real.exp (stateKappa S x m * C.control m s) := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
    exact n04b_stateProfile_on_component hN x m hs
  have hd := (hw.hasDerivAt.mul
    ((hc.hasDerivAt.const_mul (stateKappa S x m)).exp)).deriv
  simp only [Pi.mul_apply] at hd
  rw [heq.deriv_eq, hd, heq.eq_of_nhds]
  field_simp [hr0, hw0, (Real.exp_pos (stateKappa S x m * C.control m r)).ne']
  <;> ring

/-- The actual optical radicand is affine in the state-line parameter. -/
theorem n04b_stateProfile_radicand_stateLine
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (x : AnnularState S) (m : ℕ)
    {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) (t : ℝ) :
    -deriv (stateProfile D S C (n04bStateLine C x t)) r /
        (r * stateProfile D S C (n04bStateLine C x t) r) =
      -deriv D.w r / (r * D.w r) +
        (stateKappa S x m * (-deriv (C.control m) r / r)) * t := by
  rw [n04b_stateProfile_radicand_on_component hN _ m hr,
    n04b_stateKappa_stateLine hN.2.2.1]
  ring

end ContinuousFlexibility.Statements
