module

public import ContinuousFlexibility.Analysis.RetainedReferenceComponentEnumeration
public import ContinuousFlexibility.Analysis.PositiveComponentEndpoints

/-!
# Interior positive endpoints for the same retained reference

The actual two Morse tails have model endpoints converging to the two
ambient endpoints. Their genuine negative turning intervals therefore
supply negative points in every endpoint neighborhood. This excludes an
ambient positive component for that same retained reference. The
retained-coordinate certificate is explicit and is not extracted from
an arbitrary Through03 witness.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis
open scoped Topology ContDiff

theorem retainedReference_negative_near_endpoints
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    (side : Bool) {ε : ℝ} (hε : 0 < ε) :
    ∃ r ∈ radialCore Γ.reference,
      |r - (if side then Γ.reference.b else Γ.reference.a)| < ε ∧
        deriv Γ.reference.w r < 0 := by
  obtain ⟨e, _, _, he⟩ := retainedReference_natural_component_enumeration
    P hS hband hq hΓ hw hcoordinates
  let D := S.family S.sigma
  let R : ℝ := if side then P.pair.radiusR else P.pair.radiusL
  let a : ℝ := if side then Γ.reference.b else Γ.reference.a
  have hR : 0 < R := by
    cases side
    · exact P.pair.radiusL_pos
    · exact P.pair.radiusL_pos.trans_le P.pair.radius_order
  have hreal : MorseChainRealization S.chain S.sigma D S.constants :=
    (hS.2.2.2.1 S.sigma hS.2.2.1).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ha, hb⟩ := hcoordinates
  have hend : R * (if side then D.b else D.a) = a := by
    cases side
    · exact ha.symm
    · exact hb.symm
  have hlimits := hreal.2.2.2.2.2.2.1 side
  have hleft : Tendsto (fun n => R * S.chain.radius side n (S.chain.leftX side n))
      atTop (𝓝 a) := by
    simpa only [hend] using (hlimits.1.const_mul R)
  have hright : Tendsto (fun n => R * S.chain.radius side n (S.chain.rightX side n))
      atTop (𝓝 a) := by
    simpa only [hend] using (hlimits.2.const_mul R)
  have hl : ∀ᶠ n in atTop, a - ε < R * S.chain.radius side n (S.chain.leftX side n) :=
    hleft.eventually (Ioi_mem_nhds (by linarith only [hε]))
  have hr : ∀ᶠ n in atTop, R * S.chain.radius side n (S.chain.rightX side n) < a + ε :=
    hright.eventually (Iio_mem_nhds (by linarith only [hε]))
  obtain ⟨n, hn, hnl, hnr⟩ := ((eventually_ge_atTop S.chain.index).and (hl.and hr)).exists
  let J := e (morseTailIndex side (n - S.chain.index))
  have hJ := he side (n - S.chain.index)
  simp only [Nat.add_sub_of_le hn] at hJ
  have hJL : J.left = R * S.chain.radius side n
      (morseLeftTurn (morseChainA S.chain n) (morseChainB S.chain n)) := hJ.1
  have hJR : J.right = R * S.chain.radius side n
      (morseRightTurn (morseChainA S.chain n) (morseChainB S.chain n)) := hJ.2
  obtain ⟨hL, hturn, hU⟩ := morseRealization_turns_retained hreal side hn
  have hLU := (hreal.2.2.1 side n hn).2.1
  have hmono := hreal.radius_strictMonoOn side n hn
  have hmodelL : R * S.chain.radius side n (S.chain.leftX side n) < J.left := by
    rw [hJL]
    exact mul_lt_mul_of_pos_left
      (hmono (left_mem_Icc.mpr hLU.le) ⟨hL.le, (hturn.trans hU).le⟩ hL) hR
  have hmodelR : J.right < R * S.chain.radius side n (S.chain.rightX side n) := by
    rw [hJR]
    exact mul_lt_mul_of_pos_left
      (hmono ⟨(hL.trans hturn).le, hU.le⟩ (right_mem_Icc.mpr hLU.le) hU) hR
  let r := (J.left + J.right) / 2
  have hrJ : r ∈ J.interval := by
    change J.left < (J.left + J.right) / 2 ∧ (J.left + J.right) / 2 < J.right
    constructor <;> linarith only [J.left_lt_right]
  refine ⟨r, J.mem_core hrJ, ?_, J.negative hrJ⟩
  change |r - a| < ε
  exact abs_lt.mpr ⟨by linarith only [hnl, hmodelL, hrJ.1],
    by linarith only [hnr, hmodelR, hrJ.2]⟩

/-- Both endpoints of every whole positive piece of the retained
reference are genuine interior simple roots. This does not assert the
same conclusion for an arbitrary unrelated nonlinear witness. -/
theorem retainedReference_positive_endpoints_interior
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w))
    (side : Bool) :
    n04PositiveEndpoint i side ∈ radialCore Γ.reference ∧
      deriv Γ.reference.w (n04PositiveEndpoint i side) = 0 ∧
      deriv (deriv Γ.reference.w) (n04PositiveEndpoint i side) ≠ 0 := by
  have hD : RadialProfileGeometry Γ.reference := hΓ.2.1.choose_spec.1
  have hf : Continuous (deriv Γ.reference.w) := hD.2.2.1.1.continuous_deriv (by simp)
  rcases n04PositiveEndpoint_ambient_or_simple_root hD i side with hamb | hroot
  · have hb := n04PositiveComponent_bounds hf i
    let ε := (n04PositiveRight i - n04PositiveLeft i) / 2
    have hε : 0 < ε := half_pos (sub_pos.mpr hb.2.1)
    obtain ⟨r, hr, hclose, hnegative⟩ := retainedReference_negative_near_endpoints
      P hS hband hq hΓ hw hcoordinates side hε
    have hri : r ∈ i.val := by
      apply (n04PositiveComponent_mem_iff hf i).mpr
      have hc := abs_lt.mp hclose
      cases side <;> simp only [n04PositiveEndpoint, Bool.false_eq_true, ↓reduceIte] at hamb hc
      · exact ⟨by rw [hamb]; exact hr.1, by dsimp only [ε] at hc; linarith only [hc.2, hb.2.1, hamb]⟩
      · exact ⟨by dsimp only [ε] at hc; linarith only [hc.1, hb.2.1, hamb], by rw [hamb]; exact hr.2⟩
    exact False.elim ((not_lt_of_ge (n04PositiveComponent_subset i hri).2.le) hnegative)
  · exact hroot

end ContinuousFlexibility.Radial
