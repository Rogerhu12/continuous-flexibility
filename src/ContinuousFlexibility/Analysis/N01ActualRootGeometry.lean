import ContinuousFlexibility.Analysis.N01CommonRootCharacteristicStrip
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The actual two endpoints and a genuine material cell collar

The endpoint orientation follows from the negative derivative inside the
component and its simple zeros. A nonzero member of the actual radial
partition supplies a cell neighborhood of each root; no prescribed cell
is assumed to contain a neighborhood of that root.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def n01ComponentRoot {S : PhysicalSpacesData} (C : NonlinearGeometryData S)
    (m : ℕ) (rightEnd : Bool) : ℝ :=
  if rightEnd then C.right m else C.left m

def n01ComponentRootOrientation (rightEnd : Bool) : ℝ :=
  if rightEnd then -1 else 1

theorem n01ComponentRootOrientation_eq (rightEnd : Bool) :
    n01ComponentRootOrientation rightEnd = 1 ∨
      n01ComponentRootOrientation rightEnd = -1 := by
  cases rightEnd <;> simp [n01ComponentRootOrientation]

theorem n01_component_root_data
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (m : ℕ) (rightEnd : Bool) :
    n01ComponentRoot C m rightEnd ∈ Ioo D.a D.b ∧
      deriv D.w (n01ComponentRoot C m rightEnd) = 0 ∧
      n01ComponentRootOrientation rightEnd *
        deriv (deriv D.w) (n01ComponentRoot C m rightEnd) < 0 := by
  obtain ⟨_, hD⟩ := hN.1.1
  have hw : ContDiff ℝ ∞ D.w := hD.1.2.2.1.1
  have hwd : ContDiff ℝ ∞ (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2
  have hgeometry : controlGeometryConditions D S C := hN.2.2.2.1
  have ho := hgeometry.1 m
  have hz := hgeometry.2.1 m
  have hnegative := hgeometry.2.2.2.1 m
  have hl : deriv (deriv D.w) (C.left m) ≤ 0 := by
    have hd := (hwd.differentiable (by simp) (C.left m)).hasDerivAt
    apply le_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hd).2
    have hnear : ∀ᶠ x in 𝓝[>] (C.left m), x < C.right m :=
      (eventually_lt_nhds ho.2.1).filter_mono nhdsWithin_le_nhds
    filter_upwards [hnear, self_mem_nhdsWithin] with x hx (hlx : C.left m < x)
    rw [slope_def_field, hz.1, sub_zero]
    exact div_nonpos_of_nonpos_of_nonneg (hnegative x ⟨hlx, hx⟩).le
      (sub_pos.mpr hlx).le
  have hr : 0 ≤ deriv (deriv D.w) (C.right m) := by
    have hd := (hwd.differentiable (by simp) (C.right m)).hasDerivAt
    apply ge_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hd).1
    have hnear : ∀ᶠ x in 𝓝[<] (C.right m), C.left m < x :=
      (eventually_gt_nhds ho.2.1).filter_mono nhdsWithin_le_nhds
    filter_upwards [hnear, self_mem_nhdsWithin] with x hx (hxr : x < C.right m)
    rw [slope_def_field, hz.2.1, sub_zero]
    simpa only [neg_div_neg_eq] using
      div_nonneg (neg_nonneg.mpr (hnegative x ⟨hx, hxr⟩).le)
        (neg_nonneg.mpr (sub_nonpos.mpr hxr.le))
  have hl' : deriv (deriv D.w) (C.left m) < 0 := lt_of_le_of_ne hl hz.2.2.1
  have hr' : 0 < deriv (deriv D.w) (C.right m) := lt_of_le_of_ne hr hz.2.2.2.symm
  cases rightEnd
  · simpa [n01ComponentRoot, n01ComponentRootOrientation] using
      And.intro (And.intro ho.1 (ho.2.1.trans ho.2.2)) (And.intro hz.1 hl')
  · simpa [n01ComponentRoot, n01ComponentRootOrientation] using
      And.intro (And.intro (ho.1.trans ho.2.1) ho.2.2)
        (And.intro hz.2.1 (neg_neg_of_pos hr'))

/-- The partition identity supplies a nonzero localizer. Its open
nonzero set is contained in the corresponding actual material cell. -/
theorem exists_radialCell_collar_of_partition {D : ReferenceData}
    (hP : RadialPartition D) {r : ℝ} (hr : r ∈ radialCore D) :
    ∃ m : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ Ioo (r - ρ) (r + ρ) ⊆ D.cells m := by
  classical
  have hex : ∃ m : ℕ, D.localizer m r ≠ 0 := by
    by_contra! hzero
    have hs := (hP.2.2.2.2.1 r hr).2
    simp only [hzero, tsum_zero] at hs
    norm_num at hs
  obtain ⟨m, hm⟩ := hex
  have hnear : ∀ᶠ y in 𝓝 r, D.localizer m y ≠ 0 :=
    (isOpen_ne.preimage (hP.1 m).continuous).mem_nhds hm
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨m, ρ, hρ, ?_⟩
  intro y hy
  apply hP.2.2.1 m
  apply hball
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hy.1, hy.2]

end ContinuousFlexibility.Analysis
