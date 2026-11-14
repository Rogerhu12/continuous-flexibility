module

public import ContinuousFlexibility.Contracts.CartesianMetricRegularity
public import ContinuousFlexibility.Geometry.PullbackCurvature

/-!
# Actual flatness of the Cartesian remainder

The annular residual is transported through the actual polar coordinate
derivative and the curvature comparison of coframes for the same metric.
At the center, the existing constant-height/zero-profile inner disk gives
an actual zero connection germ. No Cartesian flatness premise is added to
the analytic core.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem contDiff_polarMap : ContDiff ℝ ∞ polarMap := by
  change ContDiff ℝ ∞ (fun p : PolarPoint =>
    (p.1 * Real.cos p.2, p.1 * Real.sin p.2))
  exact (contDiff_fst.mul contDiff_snd.cos).prodMk (contDiff_fst.mul contDiff_snd.sin)

theorem planeJacobian_polarMap (p : PolarPoint) : planeJacobian polarMap p = p.1 := by
  simp only [planeJacobian, (hasFDerivAt_polarMap p).fderiv, polarJacobian_apply]
  calc
    _ = p.1 * (Real.cos p.2 ^ 2 + Real.sin p.2 ^ 2) := by ring
    _ = p.1 := by rw [Real.cos_sq_add_sin_sq, mul_one]

/-- The actual global matrix connection of the Cartesian remainder. -/
def FlatAnnularCore.cartesianRemainderConnection (A : FlatAnnularCore) : PlaneOneForm :=
  matrixCoframeConnection (cartesianRemainderA A.w A.cartesianHeight)
    (cartesianRemainderB A.w A.cartesianHeight) (cartesianRemainderC A.w A.cartesianHeight)

theorem FlatAnnularCore.contDiff_cartesianRemainderCoframe (A : FlatAnnularCore)
    (x : PolarPoint) :
    ContDiffAt ℝ ∞ (matrixCoframeOne (cartesianRemainderA A.w A.cartesianHeight)
      (cartesianRemainderB A.w A.cartesianHeight) (cartesianRemainderC A.w A.cartesianHeight)).radial x ∧
    ContDiffAt ℝ ∞ (matrixCoframeOne (cartesianRemainderA A.w A.cartesianHeight)
      (cartesianRemainderB A.w A.cartesianHeight) (cartesianRemainderC A.w A.cartesianHeight)).angular x ∧
    ContDiffAt ℝ ∞ (matrixCoframeTwo (cartesianRemainderA A.w A.cartesianHeight)
      (cartesianRemainderB A.w A.cartesianHeight) (cartesianRemainderC A.w A.cartesianHeight)).radial x ∧
    ContDiffAt ℝ ∞ (matrixCoframeTwo (cartesianRemainderA A.w A.cartesianHeight)
      (cartesianRemainderB A.w A.cartesianHeight) (cartesianRemainderC A.w A.cartesianHeight)).angular x := by
  obtain ⟨ha, hb, hc⟩ := A.contDiff_cartesianRemainder_entries
  exact contDiffAt_matrixCoframe ha.contDiffAt hb.contDiffAt hc.contDiffAt
    (A.cartesianRemainderA_pos x) (A.cartesianRemainder_det_pos x)

theorem FlatAnnularCore.contDiff_cartesianRemainderConnection (A : FlatAnnularCore)
    (x : PolarPoint) :
    ContDiffAt ℝ ∞ A.cartesianRemainderConnection.radial x ∧
      ContDiffAt ℝ ∞ A.cartesianRemainderConnection.angular x := by
  obtain ⟨ha, hb, hc⟩ := A.contDiff_cartesianRemainder_entries
  exact contDiffAt_matrixCoframeConnection ha.contDiffAt hb.contDiffAt hc.contDiffAt
    (A.cartesianRemainderA_pos x) (A.cartesianRemainder_det_pos x)

/-- The actual Cartesian Cholesky coframe and the original height coframe
define the same quadratic metric after the actual polar pullback. -/
theorem FlatAnnularCore.cartesianCoframe_polar_same_metric (A : FlatAnnularCore)
    {p : PolarPoint} (hr : 0 < p.1) (v : PolarPoint) :
    formValue (matrixCoframeOne (cartesianRemainderA A.w A.cartesianHeight)
      (cartesianRemainderB A.w A.cartesianHeight) (cartesianRemainderC A.w A.cartesianHeight))
      (polarMap p) (fderiv ℝ polarMap p v) ^ 2 +
    formValue (matrixCoframeTwo (cartesianRemainderA A.w A.cartesianHeight)
      (cartesianRemainderB A.w A.cartesianHeight) (cartesianRemainderC A.w A.cartesianHeight))
      (polarMap p) (fderiv ℝ polarMap p v) ^ 2 =
      formValue (heightCoframeOne A.w A.z) p v ^ 2 +
        formValue (heightCoframeTwo A.w A.z) p v ^ 2 := by
  rw [(hasFDerivAt_polarMap p).fderiv,
    matrixCoframe_square_sum (A.cartesianRemainderA_pos (polarMap p))
      (A.cartesianRemainder_det_pos (polarMap p)).le,
    heightCoframe_square_sum (A.discriminant_pos_global p.1 p.2)]
  calc
    _ = cartesianRemainder A.w A.cartesianHeight (polarMap p)
        (polarJacobian p v) (polarJacobian p v) := by
      rw [cartesianRemainder_matrix]
      ring
    _ = _ := by rw [A.cartesianRemainder_polar_pullback hr, remainderBilinear_self]

/-- Actual standard matrix germs on the inner Euclidean disk. -/
theorem FlatAnnularCore.cartesianRemainder_entries_germ_left (A : FlatAnnularCore)
    {x : PolarPoint} (hx : cartesianRadius x < A.a) :
    cartesianRemainderA A.w A.cartesianHeight =ᶠ[𝓝 x] (fun _ => 1) ∧
    cartesianRemainderB A.w A.cartesianHeight =ᶠ[𝓝 x] (fun _ => 0) ∧
    cartesianRemainderC A.w A.cartesianHeight =ᶠ[𝓝 x] (fun _ => 1) := by
  have hn : {y : PolarPoint | cartesianRadius y < A.a} ∈ 𝓝 x :=
    (isOpen_lt continuous_cartesianRadius continuous_const).mem_nhds hx
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hn] with y hy
    exact (A.cartesianRemainder_standard_left hy).1
  · filter_upwards [hn] with y hy
    exact (A.cartesianRemainder_standard_left hy).2.1
  · filter_upwards [hn] with y hy
    exact (A.cartesianRemainder_standard_left hy).2.2

theorem FlatAnnularCore.cartesianRemainderConnection_zero_left (A : FlatAnnularCore)
    {x : PolarPoint} (hx : cartesianRadius x < A.a) :
    A.cartesianRemainderConnection.radial x = 0 ∧
      A.cartesianRemainderConnection.angular x = 0 := by
  obtain ⟨ha, hb, hc⟩ := A.cartesianRemainder_entries_germ_left hx
  exact matrixCoframeConnection_zero_of_eventually_standard ha hb hc

theorem FlatAnnularCore.cartesianRemainderConnection_germ_zero_left (A : FlatAnnularCore)
    {x : PolarPoint} (hx : cartesianRadius x < A.a) :
    A.cartesianRemainderConnection.radial =ᶠ[𝓝 x] (fun _ => 0) ∧
      A.cartesianRemainderConnection.angular =ᶠ[𝓝 x] (fun _ => 0) := by
  have hn : {y : PolarPoint | cartesianRadius y < A.a} ∈ 𝓝 x :=
    (isOpen_lt continuous_cartesianRadius continuous_const).mem_nhds hx
  constructor
  · filter_upwards [hn] with y hy
    exact (A.cartesianRemainderConnection_zero_left hy).1
  · filter_upwards [hn] with y hy
    exact (A.cartesianRemainderConnection_zero_left hy).2

theorem FlatAnnularCore.cartesianRemainderConnection_closed_left (A : FlatAnnularCore)
    {x : PolarPoint} (hx : cartesianRadius x < A.a) :
    exteriorCoefficient A.cartesianRemainderConnection x = 0 := by
  obtain ⟨hr, hθ⟩ := A.cartesianRemainderConnection_germ_zero_left hx
  unfold exteriorCoefficient radialPartial angularPartial
  rw [hθ.fderiv_eq, hr.fderiv_eq]
  simp

/-- Away from the center, flatness comes from the actual annular residual,
the actual metric pullback, and oriented-coframe curvature comparison. -/
theorem FlatAnnularCore.cartesianRemainderConnection_closed_polar (A : FlatAnnularCore)
    {p : PolarPoint} (hr : 0 < p.1) :
    exteriorCoefficient A.cartesianRemainderConnection (polarMap p) = 0 := by
  have hα := contDiffAt_heightConnection (x := p) A.smooth_w.contDiffAt A.smooth_z.contDiffAt
    hr.ne' (A.discriminant_pos_global p.1 p.2)
  have hβ := A.contDiff_cartesianRemainderConnection (polarMap p)
  have hcurv := cartan_curvature_pullback_eq_of_same_metric
    (U := {y : PolarPoint | 0 < y.1}) (x := p) (F := polarMap)
    (η₁ := heightCoframeOne A.w A.z) (η₂ := heightCoframeTwo A.w A.z)
    (ζ₁ := matrixCoframeOne (cartesianRemainderA A.w A.cartesianHeight)
      (cartesianRemainderB A.w A.cartesianHeight) (cartesianRemainderC A.w A.cartesianHeight))
    (ζ₂ := matrixCoframeTwo (cartesianRemainderA A.w A.cartesianHeight)
      (cartesianRemainderB A.w A.cartesianHeight) (cartesianRemainderC A.w A.cartesianHeight))
    (α := heightConnectionForm A.w A.z) (β := A.cartesianRemainderConnection)
    (isOpen_lt continuous_const continuous_fst) hr
    (fun _ _ => contDiff_polarMap.contDiffAt)
    (fun y hy => contDiffAt_heightCoframe A.smooth_w.contDiffAt A.smooth_z.contDiffAt
      hy.ne' (A.discriminant_pos_global y.1 y.2))
    (fun y _ => A.contDiff_cartesianRemainderCoframe (polarMap y))
    (hα.1.differentiableAt (by simp)) (hα.2.differentiableAt (by simp))
    (hβ.1.differentiableAt (by simp)) (hβ.2.differentiableAt (by simp))
    (fun y hy => heightCoframe_cartan (A.smooth_w.contDiffAt.differentiableAt (by simp))
      (A.smooth_z.contDiffAt.of_le (by simp)) hy.ne' (A.discriminant_pos_global y.1 y.2))
    (fun y _ => matrixCoframe_cartan (A.cartesianRemainderA_pos (polarMap y))
      (A.cartesianRemainder_det_pos (polarMap y)))
    (fun y hy v => A.cartesianCoframe_polar_same_metric hy v)
    (by
      intro y hy
      rw [planeJacobian_polarMap]
      exact mul_pos (heightCoframe_wedge_pos hy (A.discriminant_pos_global y.1 y.2))
        (mul_pos (matrixCoframe_wedge_pos (A.cartesianRemainderA_pos (polarMap y))
          (A.cartesianRemainder_det_pos (polarMap y))) hy))
  have hzero := heightConnection_closed_of_residual_zero
    (A.smooth_w.contDiffAt.differentiableAt (by simp))
    (A.smooth_z.contDiffAt.of_le (by simp)) hr.ne'
    (A.discriminant_pos_global p.1 p.2) (A.residual_zero_global p.1 p.2)
  rw [planeJacobian_polarMap, hzero] at hcurv
  exact (mul_eq_zero.mp hcurv).resolve_right hr.ne'

/-- The actual Cartesian remainder connection is closed on the whole
plane, including the center. No flatness condition is assumed here. -/
theorem FlatAnnularCore.cartesianRemainderConnection_closed (A : FlatAnnularCore)
    (x : PolarPoint) : exteriorCoefficient A.cartesianRemainderConnection x = 0 := by
  by_cases hx : x = 0
  · subst x
    apply A.cartesianRemainderConnection_closed_left
    simpa [cartesianRadius] using A.a_pos
  · let p : PolarPoint := (cartesianRadius x, (Complex.equivRealProdCLM.symm x).arg)
    have hp : 0 < p.1 := cartesianRadius_pos hx
    have heq : polarMap p = x := polarMap_cartesianCoordinates x
    rw [← heq]
    exact A.cartesianRemainderConnection_closed_polar hp

end ContinuousFlexibility
