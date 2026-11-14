module

public import ContinuousFlexibility.Statements.Nonlinear
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The actual orientations of the negative-component roots

The primitive profile decreases between its simple critical endpoints.
The one-sided slope limits therefore determine the signs of its actual
second derivatives. These signs are conclusions of N01, not additional
hypotheses of the root characteristic construction.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

/-- At the left simple zero of a function negative immediately to the
right, its actual derivative is strictly negative. -/
theorem n04b_left_simple_root_derivative_neg
    {f : ℝ → ℝ} {a b f' : ℝ} (hab : a < b)
    (hf : HasDerivAt f f' a) (ha : f a = 0) (hne : f' ≠ 0)
    (hneg : ∀ x ∈ Ioo a b, f x < 0) : f' < 0 := by
  have hle : f' ≤ 0 := by
    apply le_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hf).2
    have hb : ∀ᶠ x in 𝓝[>] a, x < b :=
      nhdsWithin_le_nhds (Iio_mem_nhds hab)
    filter_upwards [self_mem_nhdsWithin, hb] with x hax hxb
    rw [slope_def_field, ha, sub_zero]
    exact div_nonpos_of_nonpos_of_nonneg (hneg x ⟨hax, hxb⟩).le
      (sub_nonneg.mpr hax.le)
  exact lt_of_le_of_ne hle hne

/-- At the right simple zero of a function negative immediately to the
left, its actual derivative is strictly positive. -/
theorem n04b_right_simple_root_derivative_pos
    {f : ℝ → ℝ} {a b f' : ℝ} (hab : a < b)
    (hf : HasDerivAt f f' b) (hb : f b = 0) (hne : f' ≠ 0)
    (hneg : ∀ x ∈ Ioo a b, f x < 0) : 0 < f' := by
  have hle : 0 ≤ f' := by
    apply ge_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hf).1
    have ha : ∀ᶠ x in 𝓝[<] b, a < x :=
      nhdsWithin_le_nhds (Ioi_mem_nhds hab)
    filter_upwards [self_mem_nhdsWithin, ha] with x hxb hax
    rw [slope_def_field, hb, sub_zero]
    exact div_nonneg_of_nonpos (hneg x ⟨hax, hxb⟩).le
      (sub_nonpos.mpr hxb.le)
  exact lt_of_le_of_ne hle hne.symm

/-- Every actual N01 negative component has the signs required for the
left orientation +1 and the right orientation -1. -/
theorem n04b_component_root_orientations
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (m : ℕ) :
    deriv (deriv D.w) (C.left m) < 0 ∧
      0 < deriv (deriv D.w) (C.right m) := by
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  obtain ⟨_, hbounds⟩ := hN.1.1
  have hw : ContDiff ℝ ∞ D.w := hbounds.1.2.2.1.1
  have hwd : ContDiff ℝ ∞ (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2
  have hneg := hcontrol.2.2.2.1 m
  have hroot := hcontrol.2.1 m
  exact ⟨n04b_left_simple_root_derivative_neg (hcontrol.1 m).2.1
      ((hwd.differentiable (by simp) _).hasDerivAt) hroot.1 hroot.2.2.1 hneg,
    n04b_right_simple_root_derivative_pos (hcontrol.1 m).2.1
      ((hwd.differentiable (by simp) _).hasDerivAt) hroot.2.1 hroot.2.2.2 hneg⟩

end ContinuousFlexibility.Analysis
