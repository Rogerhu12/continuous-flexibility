import ContinuousFlexibility.Analysis.N04PositiveComponentRecognition
import ContinuousFlexibility.Analysis.RetainedMorsePositiveGapCoordinates
import ContinuousFlexibility.Radial.RetainedMorseGapSlope

/-!
# The actual positive components of the retained Morse tails

The original N06 gap has strictly positive derivative between its two
turning roots. The same retained profile germ and radius dilation
transport that statement, including both zero endpoints. The displayed
physical interval is therefore one complete positive component of the
same reference, without changing its component indexing.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis
open scoped ContDiff

theorem retainedReference_positive_gap_deriv
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    {D : ReferenceData} (hw : D.w = P.pair.profile)
    (side : Bool) {n : ℕ} (hn : S.chain.index ≤ n) {r : ℝ}
    (hr : r ∈ Icc (n06MorsePositiveLeft S.chain side n)
      (n06MorsePositiveRight S.chain side n)) :
    deriv D.w (P.sideRadius side * r) =
      P.sideHeight side * deriv (S.family S.sigma).w r := by
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hd := hS.2.2.2.2.2 side S.chain.index 2 le_rfl (by decide) hband
  have hentry : S.entry side S.chain.index =
      morseChainSeam S.chain side S.chain.index := hd.2.2.2.2.2.1
  have ht := morseRealization_positive_gap_subset_tail hreal side hn hr
  rw [← hentry] at ht
  have hcore : r ∈ radialCore (S.family S.sigma) := by
    cases side
    · exact ⟨ht.1, ht.2.trans hd.2.1.2⟩
    · exact ⟨hd.2.1.1.trans ht.1, ht.2⟩
  have hout : if side then S.cut side S.chain.index ≤ r
      else r ≤ S.cut side S.chain.index := by
    have ho := hd.2.2.2.2.1
    cases side
    · exact (ht.2.trans (ho.1.trans ho.2)).le
    · exact ((ho.1.trans ho.2).trans ht.1).le
  exact P.reference_side_old_deriv hw hS side hcore hout

theorem retainedReference_positive_gap_is_component
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    (side : Bool) {n : ℕ} (hn : S.chain.index ≤ n) :
    ∃! i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w),
      n04PositiveLeft i = P.sideRadius side * n06MorsePositiveLeft S.chain side n ∧
      n04PositiveRight i = P.sideRadius side * n06MorsePositiveRight S.chain side n := by
  let D := S.family S.sigma
  let l := n06MorsePositiveLeft S.chain side n
  let u := n06MorsePositiveRight S.chain side n
  let R := P.sideRadius side
  have hR : 0 < R := P.sideRadius_pos side
  have hreal : MorseChainRealization S.chain S.sigma D S.constants :=
    (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hgeom := n06_morsePositive_gap_geometry hreal side hn
  have hlu : l < u := hgeom.2.1.trans (hgeom.2.2.1.trans hgeom.2.2.2.1)
  have hpartition : RadialPartition Γ.reference := hΓ.2.1.choose_spec.2.1
  have hcells := (retainedReference_positive_gap_cell_transport P hS hband hcoordinates).1
  have hcore (r : ℝ) (hr : r ∈ Icc l u) : R * r ∈ radialCore Γ.reference := by
    obtain ⟨m, _, hrm⟩ := morseRealization_positive_gap_cell_labels hreal side hn hr
    exact hpartition.2.2.2.1 m (hcells side n hn m r hr hrm)
  have hderiv (r : ℝ) (hr : r ∈ Icc l u) :
      deriv Γ.reference.w (R * r) = P.sideHeight side * deriv D.w r :=
    retainedReference_positive_gap_deriv P hS hband hw side hn hr
  let d : ℕ := if side then n else n + 1
  let a : ℕ := if side then n + 1 else n
  have hd : S.chain.index ≤ d := by
    cases side
    · exact hn.trans (Nat.le_succ n)
    · exact hn
  have ha : S.chain.index ≤ a := by
    cases side
    · exact hn
    · exact hn.trans (Nat.le_succ n)
  have hlzero : deriv D.w l = 0 :=
    (morseRealization_model_return hreal hS.2.2.1 side hd).1.2.2.2.2.1
  have huzero : deriv D.w u = 0 :=
    (morseRealization_model_return hreal hS.2.2.1 side ha).1.2.2.2.1
  have hleft := hcore l (left_mem_Icc.mpr hlu.le)
  have hright := hcore u (right_mem_Icc.mpr hlu.le)
  have hf : Continuous (deriv Γ.reference.w) :=
    hΓ.2.1.choose_spec.1.2.2.1.1.continuous_deriv (by simp)
  apply n04PositiveComponent_existsUnique_of_zero_endpoints hf hleft.1.le
    (mul_lt_mul_of_pos_left hlu hR) hright.2.le
  · rw [hderiv l (left_mem_Icc.mpr hlu.le), hlzero, mul_zero]
  · rw [hderiv u (right_mem_Icc.mpr hlu.le), huzero, mul_zero]
  · intro x hx
    let r := x / R
    have hr : r ∈ Ioo l u := by
      constructor
      · exact (lt_div_iff₀ hR).mpr (by simpa only [mul_comm] using hx.1)
      · exact (div_lt_iff₀ hR).mpr (by simpa only [mul_comm] using hx.2)
    have hrclosed : r ∈ Icc l u := ⟨hr.1.le, hr.2.le⟩
    have hrpos : 0 < r := hreal.geometry.1.trans (hgeom.1.trans hr.1)
    obtain ⟨c, A, hc, _, hlow⟩ :=
      n06_morseRealization_positive_gap_product_lower hreal hS.2.2.1
    have hp : 0 < c * radialE (n + 1) ^ (-A) * (r - l) * (u - r) :=
      mul_pos (mul_pos (mul_pos hc (Real.rpow_pos_of_pos (Real.exp_pos _) _))
        (sub_pos.mpr hr.1)) (sub_pos.mpr hr.2)
    have hpositive : 0 < deriv D.w r := by
      have hh := (lt_div_iff₀ hrpos).mp (hp.trans_le (hlow side n hn r hrclosed))
      simpa only [zero_mul] using hh
    have he : R * r = x := by
      dsimp only [r]
      field_simp [hR.ne'] <;> ring
    rw [← he, hderiv r hrclosed]
    exact mul_pos (P.sideHeight_pos side) hpositive

end ContinuousFlexibility.Radial
