module

public import ContinuousFlexibility.Scalar.FlatCollar
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The actual analytic-to-geometric annular interface

`FlatAnnularCore` is data which the nonlinear existence proof must construct.
It contains no planar development and no assumed existence theorem. Its
height and profile have actual global smooth extensions, with independent
constant values on the two exterior radial intervals.

The enlargement to `AnnularSolution` is proved below. The original core
has a strictly positive profile; the enlarged annulus has genuine open flat
collars and therefore does not have a strictly positive profile everywhere.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set Filter
open scoped ContDiff Topology

structure FlatAnnularCore where
  a : ℝ
  b : ℝ
  a_pos : 0 < a
  a_lt_b : a < b
  w : ℝ → ℝ
  z : PolarPoint → ℝ
  cLeft : ℝ
  cRight : ℝ
  smooth_w : ContDiff ℝ ∞ w
  smooth_z : ContDiff ℝ ∞ z
  w_pos : ∀ r ∈ Ioo a b, 0 < w r
  w_zero : ∀ r, r ≤ a ∨ b ≤ r → w r = 0
  z_left : ∀ r, r ≤ a → ∀ θ, z (r, θ) = cLeft
  z_right : ∀ r, b ≤ r → ∀ θ, z (r, θ) = cRight
  half_turn : Function.Periodic z (0, Real.pi)
  even : ∀ r θ, z (r, -θ) = z (r, θ)
  discriminant_pos : ∀ r ∈ Icc a b, ∀ θ, 0 < polarDiscriminant w z (r, θ)
  residual_zero : ∀ r ∈ Icc a b, ∀ θ, polarCoordinateResidual w z (r, θ) = 0
  nonradial : ∃ r ∈ Ioo a b, ∃ θ φ, z (r, θ) ≠ z (r, φ)

theorem FlatAnnularCore.b_pos (A : FlatAnnularCore) : 0 < A.b :=
  A.a_pos.trans A.a_lt_b

theorem FlatAnnularCore.periodic_two_pi (A : FlatAnnularCore) :
    Function.Periodic A.z (0, 2 * Real.pi) := by
  have h : (2 : ℕ) • ((0, Real.pi) : PolarPoint) = (0, 2 * Real.pi) := by
    ext <;> simp [two_smul, two_mul]
  rw [← h]
  exact A.half_turn.nsmul 2

theorem FlatAnnularCore.left_flat_germs (A : FlatAnnularCore) {r : ℝ}
    (hr : r < A.a) (θ : ℝ) :
    (A.w =ᶠ[𝓝 r] fun _ => 0) ∧ (A.z =ᶠ[𝓝 (r, θ)] fun _ => A.cLeft) := by
  constructor
  · filter_upwards [Iio_mem_nhds hr] with s hs
    exact A.w_zero s (Or.inl hs.le)
  · have hn : {y : PolarPoint | y.1 < A.a} ∈ 𝓝 (r, θ) :=
      (isOpen_lt continuous_fst continuous_const).mem_nhds hr
    filter_upwards [hn] with y hy
    exact A.z_left y.1 hy.le y.2

theorem FlatAnnularCore.right_flat_germs (A : FlatAnnularCore) {r : ℝ}
    (hr : A.b < r) (θ : ℝ) :
    (A.w =ᶠ[𝓝 r] fun _ => 0) ∧ (A.z =ᶠ[𝓝 (r, θ)] fun _ => A.cRight) := by
  constructor
  · filter_upwards [Ioi_mem_nhds hr] with s hs
    exact A.w_zero s (Or.inr hs.le)
  · have hn : {y : PolarPoint | A.b < y.1} ∈ 𝓝 (r, θ) :=
      (isOpen_lt continuous_const continuous_fst).mem_nhds hr
    filter_upwards [hn] with y hy
    exact A.z_right y.1 hy.le y.2

/-- This discriminant is the polar coordinate expression; its value at
radius zero is not a claim that the polar coordinate chart is regular there. -/
theorem FlatAnnularCore.discriminant_pos_global (A : FlatAnnularCore) (r θ : ℝ) :
    0 < polarDiscriminant A.w A.z (r, θ) := by
  by_cases hl : r < A.a
  · obtain ⟨hw, hz⟩ := A.left_flat_germs hl θ
    rw [flat_germ_discriminant_eq_one hw hz]
    norm_num
  by_cases hr : A.b < r
  · obtain ⟨hw, hz⟩ := A.right_flat_germs hr θ
    rw [flat_germ_discriminant_eq_one hw hz]
    norm_num
  exact A.discriminant_pos r ⟨le_of_not_gt hl, le_of_not_gt hr⟩ θ

theorem FlatAnnularCore.residual_zero_global (A : FlatAnnularCore) (r θ : ℝ) :
    polarCoordinateResidual A.w A.z (r, θ) = 0 := by
  by_cases hl : r < A.a
  · obtain ⟨hw, hz⟩ := A.left_flat_germs hl θ
    exact flat_germ_residual_eq_zero hw hz
  by_cases hr : A.b < r
  · obtain ⟨hw, hz⟩ := A.right_flat_germs hr θ
    exact flat_germ_residual_eq_zero hw hz
  exact A.residual_zero r ⟨le_of_not_gt hl, le_of_not_gt hr⟩ θ

/-- A genuine open-collar enlargement of the same analytic core. -/
structure AnnularSolution extends FlatAnnularCore where
  innerRadius : ℝ
  outerRadius : ℝ
  inner_pos : 0 < innerRadius
  inner_lt_a : innerRadius < a
  b_lt_outer : b < outerRadius
  discriminant_extended : ∀ r ∈ Icc innerRadius outerRadius, ∀ θ,
    0 < polarDiscriminant w z (r, θ)
  residual_extended : ∀ r ∈ Icc innerRadius outerRadius, ∀ θ,
    polarCoordinateResidual w z (r, θ) = 0

/-- No new height or profile is selected: only the two radial bounds change. -/
def FlatAnnularCore.enlarge (A : FlatAnnularCore) : AnnularSolution where
  toFlatAnnularCore := A
  innerRadius := A.a / 2
  outerRadius := A.b + 1
  inner_pos := div_pos A.a_pos (by norm_num)
  inner_lt_a := by linarith [A.a_pos]
  b_lt_outer := by linarith
  discriminant_extended := fun r _ θ => A.discriminant_pos_global r θ
  residual_extended := fun r _ θ => A.residual_zero_global r θ

@[simp] theorem FlatAnnularCore.enlarge_w (A : FlatAnnularCore) : A.enlarge.w = A.w := rfl
@[simp] theorem FlatAnnularCore.enlarge_z (A : FlatAnnularCore) : A.enlarge.z = A.z := rfl

theorem AnnularSolution.left_collar (A : AnnularSolution) {r : ℝ}
    (hr : r ∈ Ioo A.innerRadius A.a) (θ : ℝ) :
    A.w r = 0 ∧ A.z (r, θ) = A.cLeft :=
  ⟨A.w_zero r (Or.inl hr.2.le), A.z_left r hr.2.le θ⟩

theorem AnnularSolution.right_collar (A : AnnularSolution) {r : ℝ}
    (hr : r ∈ Ioo A.b A.outerRadius) (θ : ℝ) :
    A.w r = 0 ∧ A.z (r, θ) = A.cRight :=
  ⟨A.w_zero r (Or.inr hr.1.le), A.z_right r hr.1.le θ⟩

theorem AnnularSolution.left_collar_nonempty (A : AnnularSolution) :
    (Ioo A.innerRadius A.a).Nonempty := nonempty_Ioo.mpr A.inner_lt_a

theorem AnnularSolution.right_collar_nonempty (A : AnnularSolution) :
    (Ioo A.b A.outerRadius).Nonempty := nonempty_Ioo.mpr A.b_lt_outer

theorem AnnularSolution.nonradial_on_annulus (A : AnnularSolution) :
    ∃ r ∈ Ioo A.innerRadius A.outerRadius, ∃ θ φ, A.z (r, θ) ≠ A.z (r, φ) := by
  obtain ⟨r, hr, θ, φ, hne⟩ := A.nonradial
  exact ⟨r, ⟨A.inner_lt_a.trans hr.1, hr.2.trans A.b_lt_outer⟩, θ, φ, hne⟩

end ContinuousFlexibility
