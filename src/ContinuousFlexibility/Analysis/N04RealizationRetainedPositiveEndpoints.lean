module

public import ContinuousFlexibility.Analysis.N05SeedNegativeEnumeration
public import ContinuousFlexibility.Analysis.PositiveComponentEndpoints

/-!
# Interior positive endpoints of the same retained seed

The supplied seed retains both genuine Morse tails. Their model endpoints
converge to its own two ambient endpoints, so negative turning intervals
supply negative points in every endpoint neighborhood. A positive
component therefore has two interior simple-root endpoints.

This reuses the argument of the held
RetainedPositiveComponentInteriorEndpoints (snapshot 16, 0db1a62e),
with the active seed tail enumeration instead of the legacy enumeration
package. No reference, material data, cell, or atlas is selected again.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped Topology ContDiff

/-- Actual retained tail components approach each endpoint of this seed. -/
theorem n04Realization_seed_negative_near_endpoints
    {q : ℝ} (Q : SeedReferenceConstruction q) (side : Bool)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r ∈ radialCore Q.reference,
      |r - (if side then Q.reference.b else Q.reference.a)| < ε ∧
        deriv Q.reference.w r < 0 := by
  let R : ℝ := Q.n05TailScale side
  let c : ℝ := if side then Q.reference.b else Q.reference.a
  have hR : 0 < R := Q.n05TailScale_pos side
  have hend : R * (if side then (Q.selected.family Q.selected.sigma).b
      else (Q.selected.family Q.selected.sigma).a) = c := by
    cases side
    · exact Q.left_endpoint.symm
    · exact Q.right_endpoint.symm
  have hlimits := Q.realization.2.2.2.2.2.2.1 side
  have hleft : Tendsto
      (fun n => R * Q.selected.chain.radius side n (Q.selected.chain.leftX side n))
      atTop (𝓝 c) := by
    simpa only [hend] using hlimits.1.const_mul R
  have hright : Tendsto
      (fun n => R * Q.selected.chain.radius side n (Q.selected.chain.rightX side n))
      atTop (𝓝 c) := by
    simpa only [hend] using hlimits.2.const_mul R
  have hl : ∀ᶠ n in atTop,
      c - ε < R * Q.selected.chain.radius side n (Q.selected.chain.leftX side n) :=
    hleft.eventually (Ioi_mem_nhds (by linarith only [hε]))
  have hr : ∀ᶠ n in atTop,
      R * Q.selected.chain.radius side n (Q.selected.chain.rightX side n) < c + ε :=
    hright.eventually (Iio_mem_nhds (by linarith only [hε]))
  obtain ⟨n, hn, hnl, hnr⟩ :=
    ((eventually_ge_atTop Q.retainedIndex).and (hl.and hr)).exists
  have hn₀ : Q.selected.chain.index ≤ n := Q.retainedIndex_ge.trans hn
  let J : Q.N05NegativeComponent := Q.n05TailNegativeComponent side (n - Q.retainedIndex)
  have hJL : J.val.1 = R * Q.n05ModelLeft side n := by
    simp only [J, R, SeedReferenceConstruction.n05TailNegativeComponent,
      Nat.add_sub_of_le hn]
  have hJR : J.val.2 = R * Q.n05ModelRight side n := by
    simp only [J, R, SeedReferenceConstruction.n05TailNegativeComponent,
      Nat.add_sub_of_le hn]
  obtain ⟨hL, hturn, hU⟩ := morseRealization_turns_retained Q.realization side hn₀
  have hfull := (Q.realization.2.2.1 side n hn₀).2.1
  have hsub := Icc_subset_Icc hL.le hU.le
  have hmono := Q.realization.radius_strictMonoOn side n hn₀
  have hmodelL :
      R * Q.selected.chain.radius side n (Q.selected.chain.leftX side n) < J.val.1 := by
    rw [hJL]
    exact mul_lt_mul_of_pos_left
      (hmono (left_mem_Icc.mpr hfull.le) (hsub (left_mem_Icc.mpr hturn.le)) hL) hR
  have hmodelR :
      J.val.2 < R * Q.selected.chain.radius side n (Q.selected.chain.rightX side n) := by
    rw [hJR]
    exact mul_lt_mul_of_pos_left
      (hmono (hsub (right_mem_Icc.mpr hturn.le)) (right_mem_Icc.mpr hfull.le) hU) hR
  have hJ : NegativeRadialComponent Q.reference J.val.1 J.val.2 := J.property
  let r : ℝ := (J.val.1 + J.val.2) / 2
  have hrJ : r ∈ Ioo J.val.1 J.val.2 := by
    change J.val.1 < (J.val.1 + J.val.2) / 2 ∧
      (J.val.1 + J.val.2) / 2 < J.val.2
    constructor <;> linarith only [hJ.2.1]
  refine ⟨r, ⟨hJ.1.trans hrJ.1, hrJ.2.trans hJ.2.2.1⟩,
    ?_, hJ.2.2.2.2.2 r hrJ⟩
  change |r - c| < ε
  exact abs_lt.mpr ⟨by linarith only [hnl, hmodelL, hrJ.1],
    by linarith only [hnr, hmodelR, hrJ.2]⟩

/-- Every positive endpoint of the supplied seed is a genuine simple root. -/
theorem n04Realization_seed_positive_endpoints_interior
    {q : ℝ} (Q : SeedReferenceConstruction q)
    (i : N04PositiveComponent Q.reference.a Q.reference.b (deriv Q.reference.w))
    (side : Bool) :
    n04PositiveEndpoint i side ∈ radialCore Q.reference ∧
      deriv Q.reference.w (n04PositiveEndpoint i side) = 0 ∧
      deriv (deriv Q.reference.w) (n04PositiveEndpoint i side) ≠ 0 := by
  have hD : RadialProfileGeometry Q.reference := Q.accumulating.choose_spec.1
  have hf : Continuous (deriv Q.reference.w) := hD.2.2.1.1.continuous_deriv (by simp)
  rcases n04PositiveEndpoint_ambient_or_simple_root hD i side with hamb | hroot
  · have hb := n04PositiveComponent_bounds hf i
    let ε : ℝ := (n04PositiveRight i - n04PositiveLeft i) / 2
    have hε : 0 < ε := half_pos (sub_pos.mpr hb.2.1)
    obtain ⟨r, hr, hclose, hnegative⟩ :=
      n04Realization_seed_negative_near_endpoints Q side hε
    have hri : r ∈ i.val := by
      apply (n04PositiveComponent_mem_iff hf i).mpr
      have hc := abs_lt.mp hclose
      cases side <;> simp only [n04PositiveEndpoint, Bool.false_eq_true,
        ite_false, ite_true] at hamb hc
      · exact ⟨by rw [hamb]; exact hr.1,
          by dsimp only [ε] at hc; linarith only [hc.2, hb.2.1, hamb]⟩
      · exact ⟨by dsimp only [ε] at hc; linarith only [hc.1, hb.2.1, hamb],
          by rw [hamb]; exact hr.2⟩
    exact False.elim ((not_lt_of_ge (n04PositiveComponent_subset i hri).2.le) hnegative)
  · exact hroot

/-- Transport to the original connected reference using its retained
seed equality. The supplied seed and the actual reference are unchanged. -/
theorem n04Realization_seed_positive_endpoints_sameReference
    {q : ℝ} (Q : SeedReferenceConstruction q) {D : ReferenceData}
    (hreference : Q.reference = D)
    (i : N04PositiveComponent D.a D.b (deriv D.w)) (side : Bool) :
    n04PositiveEndpoint i side ∈ radialCore D ∧
      deriv D.w (n04PositiveEndpoint i side) = 0 ∧
      deriv (deriv D.w) (n04PositiveEndpoint i side) ≠ 0 := by
  subst D
  exact n04Realization_seed_positive_endpoints_interior Q i side

end ContinuousFlexibility.Analysis
