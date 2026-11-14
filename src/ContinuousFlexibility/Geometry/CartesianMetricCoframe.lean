module

public import ContinuousFlexibility.Geometry.CartesianCoframe
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A global Cartesian coframe of a positive matrix metric

The Cholesky formulas use only the actual Cartesian metric entries. They
therefore extend across the center without choosing a polar angle. The
connection is solved from the actual exterior derivatives of this coframe.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def matrixDiscriminant (A B C : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  A x * C x - B x ^ 2

def matrixCoframeOne (A B _C : PolarPoint → ℝ) : PlaneOneForm :=
  ⟨fun x => Real.sqrt (A x), fun x => B x / Real.sqrt (A x)⟩

def matrixCoframeTwo (A B C : PolarPoint → ℝ) : PlaneOneForm :=
  ⟨fun _ => 0, fun x => Real.sqrt (matrixDiscriminant A B C x) / Real.sqrt (A x)⟩

/-- Solve the two actual Cartan equations for an upper triangular coframe. -/
def triangularCoframeConnection (a b c : PolarPoint → ℝ) : PlaneOneForm :=
  ⟨fun x => (radialPartial b x - angularPartial a x) / c x,
   fun x => (radialPartial c x +
     b x * (radialPartial b x - angularPartial a x) / c x) / a x⟩

def matrixCoframeConnection (A B C : PolarPoint → ℝ) : PlaneOneForm :=
  triangularCoframeConnection
    (matrixCoframeOne A B C).radial (matrixCoframeOne A B C).angular
    (matrixCoframeTwo A B C).angular

theorem cholesky_square_sum {A B C : ℝ} (hA : 0 < A) (hD : 0 ≤ A * C - B ^ 2)
    (u v : ℝ) :
    (Real.sqrt A * u + B / Real.sqrt A * v) ^ 2 +
      (Real.sqrt (A * C - B ^ 2) / Real.sqrt A * v) ^ 2 =
        A * u ^ 2 + 2 * B * u * v + C * v ^ 2 := by
  have ha := Real.sq_sqrt hA.le
  have hd := Real.sq_sqrt hD
  have hane := (Real.sqrt_pos.mpr hA).ne'
  field_simp [hane]
  linear_combination (Real.sqrt A ^ 2 * u ^ 2 - C * v ^ 2) * ha + v ^ 2 * hd

theorem matrixCoframe_square_sum {A B C : PolarPoint → ℝ} {x : PolarPoint}
    (hA : 0 < A x) (hD : 0 ≤ matrixDiscriminant A B C x) (v : PolarPoint) :
    formValue (matrixCoframeOne A B C) x v ^ 2 +
      formValue (matrixCoframeTwo A B C) x v ^ 2 =
        A x * v.1 ^ 2 + 2 * B x * v.1 * v.2 + C x * v.2 ^ 2 := by
  simpa only [formValue, matrixCoframeOne, matrixCoframeTwo, matrixDiscriminant,
    zero_mul, zero_add] using cholesky_square_sum hA hD v.1 v.2

theorem matrixCoframe_wedge {A B C : PolarPoint → ℝ} {x : PolarPoint}
    (hA : 0 < A x) :
    wedgeCoefficient (matrixCoframeOne A B C) (matrixCoframeTwo A B C) x =
      Real.sqrt (matrixDiscriminant A B C x) := by
  simp only [wedgeCoefficient, matrixCoframeOne, matrixCoframeTwo, mul_zero, sub_zero]
  field_simp [(Real.sqrt_pos.mpr hA).ne']

theorem matrixCoframe_wedge_pos {A B C : PolarPoint → ℝ} {x : PolarPoint}
    (hA : 0 < A x) (hD : 0 < matrixDiscriminant A B C x) :
    0 < wedgeCoefficient (matrixCoframeOne A B C) (matrixCoframeTwo A B C) x := by
  rw [matrixCoframe_wedge hA]
  exact Real.sqrt_pos.mpr hD

theorem contDiffAt_matrixCoframe {n : ℕ∞ω} {A B C : PolarPoint → ℝ}
    {x : PolarPoint} (hA : ContDiffAt ℝ n A x) (hB : ContDiffAt ℝ n B x)
    (hC : ContDiffAt ℝ n C x) (hApos : 0 < A x)
    (hD : 0 < matrixDiscriminant A B C x) :
    ContDiffAt ℝ n (matrixCoframeOne A B C).radial x ∧
      ContDiffAt ℝ n (matrixCoframeOne A B C).angular x ∧
      ContDiffAt ℝ n (matrixCoframeTwo A B C).radial x ∧
      ContDiffAt ℝ n (matrixCoframeTwo A B C).angular x := by
  have hasqrt := hA.sqrt hApos.ne'
  have hdsmooth : ContDiffAt ℝ n (matrixDiscriminant A B C) x :=
    (hA.mul hC).sub (hB.pow 2)
  exact ⟨hasqrt, hB.div hasqrt (Real.sqrt_pos.mpr hApos).ne', contDiffAt_const,
    (hdsmooth.sqrt hD.ne').div hasqrt (Real.sqrt_pos.mpr hApos).ne'⟩

theorem triangularCoframeConnection_cartan {a b c : PolarPoint → ℝ} {x : PolarPoint}
    (ha : a x ≠ 0) (hc : c x ≠ 0) :
    exteriorCoefficient (PlaneOneForm.mk a b) x =
        wedgeCoefficient (triangularCoframeConnection a b c) (PlaneOneForm.mk (fun _ => 0) c) x ∧
      exteriorCoefficient (PlaneOneForm.mk (fun _ => 0) c) x =
        -wedgeCoefficient (triangularCoframeConnection a b c) (PlaneOneForm.mk a b) x := by
  constructor
  · simp [exteriorCoefficient, wedgeCoefficient, triangularCoframeConnection, hc]
  · simp only [exteriorCoefficient, wedgeCoefficient, triangularCoframeConnection]
    rw [angularPartial_const]
    field_simp [ha, hc]
    ring

theorem matrixCoframe_cartan {A B C : PolarPoint → ℝ} {x : PolarPoint}
    (hA : 0 < A x) (hD : 0 < matrixDiscriminant A B C x) :
    exteriorCoefficient (matrixCoframeOne A B C) x =
        wedgeCoefficient (matrixCoframeConnection A B C) (matrixCoframeTwo A B C) x ∧
      exteriorCoefficient (matrixCoframeTwo A B C) x =
        -wedgeCoefficient (matrixCoframeConnection A B C) (matrixCoframeOne A B C) x := by
  exact triangularCoframeConnection_cartan (Real.sqrt_pos.mpr hA).ne'
    (div_ne_zero (Real.sqrt_pos.mpr hD).ne' (Real.sqrt_pos.mpr hA).ne')

theorem contDiffAt_triangularCoframeConnection
    {a b c : PolarPoint → ℝ} {x : PolarPoint}
    (ha : ContDiffAt ℝ ∞ a x) (hb : ContDiffAt ℝ ∞ b x) (hc : ContDiffAt ℝ ∞ c x)
    (hane : a x ≠ 0) (hcne : c x ≠ 0) :
    ContDiffAt ℝ ∞ (triangularCoframeConnection a b c).radial x ∧
      ContDiffAt ℝ ∞ (triangularCoframeConnection a b c).angular x := by
  have hbx : ContDiffAt ℝ ∞ (radialPartial b) x :=
    contDiffAt_radialPartial hb (by simp)
  have hay : ContDiffAt ℝ ∞ (angularPartial a) x :=
    contDiffAt_angularPartial ha (by simp)
  have hcx : ContDiffAt ℝ ∞ (radialPartial c) x :=
    contDiffAt_radialPartial hc (by simp)
  exact ⟨(hbx.sub hay).div hc hcne,
    (hcx.add ((hb.mul (hbx.sub hay)).div hc hcne)).div ha hane⟩

theorem contDiffAt_matrixCoframeConnection {A B C : PolarPoint → ℝ} {x : PolarPoint}
    (hA : ContDiffAt ℝ ∞ A x) (hB : ContDiffAt ℝ ∞ B x)
    (hC : ContDiffAt ℝ ∞ C x) (hApos : 0 < A x)
    (hD : 0 < matrixDiscriminant A B C x) :
    ContDiffAt ℝ ∞ (matrixCoframeConnection A B C).radial x ∧
      ContDiffAt ℝ ∞ (matrixCoframeConnection A B C).angular x := by
  obtain ⟨h1r, h1a, _, h2a⟩ := contDiffAt_matrixCoframe hA hB hC hApos hD
  exact contDiffAt_triangularCoframeConnection h1r h1a h2a
    (Real.sqrt_pos.mpr hApos).ne'
    (div_ne_zero (Real.sqrt_pos.mpr hD).ne' (Real.sqrt_pos.mpr hApos).ne')

theorem matrixCoframe_standard {A B C : PolarPoint → ℝ} {x : PolarPoint}
    (hA : A x = 1) (hB : B x = 0) (hC : C x = 1) :
    (matrixCoframeOne A B C).radial x = 1 ∧
      (matrixCoframeOne A B C).angular x = 0 ∧
      (matrixCoframeTwo A B C).radial x = 0 ∧
      (matrixCoframeTwo A B C).angular x = 1 := by
  simp [matrixCoframeOne, matrixCoframeTwo, matrixDiscriminant, hA, hB, hC]

theorem triangularCoframeConnection_zero_of_eventually_standard
    {a b c : PolarPoint → ℝ} {x : PolarPoint}
    (ha : a =ᶠ[𝓝 x] fun _ => 1) (hb : b =ᶠ[𝓝 x] fun _ => 0)
    (hc : c =ᶠ[𝓝 x] fun _ => 1) :
    (triangularCoframeConnection a b c).radial x = 0 ∧
      (triangularCoframeConnection a b c).angular x = 0 := by
  have hay : angularPartial a x = 0 := by
    unfold angularPartial
    rw [ha.fderiv_eq]
    simp
  have hbx : radialPartial b x = 0 := by
    unfold radialPartial
    rw [hb.fderiv_eq]
    simp
  have hcx : radialPartial c x = 0 := by
    unfold radialPartial
    rw [hc.fderiv_eq]
    simp
  simp [triangularCoframeConnection, hay, hbx, hcx]

theorem matrixCoframeConnection_zero_of_eventually_standard
    {A B C : PolarPoint → ℝ} {x : PolarPoint}
    (hA : A =ᶠ[𝓝 x] fun _ => 1) (hB : B =ᶠ[𝓝 x] fun _ => 0)
    (hC : C =ᶠ[𝓝 x] fun _ => 1) :
    (matrixCoframeConnection A B C).radial x = 0 ∧
      (matrixCoframeConnection A B C).angular x = 0 := by
  have ha : (matrixCoframeOne A B C).radial =ᶠ[𝓝 x] fun _ => 1 := by
    filter_upwards [hA, hB, hC] with y hyA hyB hyC
    exact (matrixCoframe_standard hyA hyB hyC).1
  have hb : (matrixCoframeOne A B C).angular =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hA, hB, hC] with y hyA hyB hyC
    exact (matrixCoframe_standard hyA hyB hyC).2.1
  have hc : (matrixCoframeTwo A B C).angular =ᶠ[𝓝 x] fun _ => 1 := by
    filter_upwards [hA, hB, hC] with y hyA hyB hyC
    exact (matrixCoframe_standard hyA hyB hyC).2.2.2
  exact triangularCoframeConnection_zero_of_eventually_standard ha hb hc

end ContinuousFlexibility
