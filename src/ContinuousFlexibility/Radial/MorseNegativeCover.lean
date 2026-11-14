module

public import ContinuousFlexibility.Radial.MorseModelReturn
public import ContinuousFlexibility.Radial.ReferenceReturnComponents
public import Lean.Elab.Tactic.Omega

/-!
# Exhaustion of the actual Morse tails by their negative model components

The seam limits force every tail point into a finite seam block. The
closed joins have nonnegative profile derivative, so a negative point
belongs to a retained model. Both endpoint orientations use this same
argument in the signed physical coordinate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

private theorem exists_nat_sandwich_of_tendsto
    {f : ℕ → ℝ} {e r : ℝ} (hf : Tendsto f atTop (𝓝 e))
    (hre : r < e) (N : ℕ) (hN : f N ≤ r) :
    ∃ n : ℕ, N ≤ n ∧ f n ≤ r ∧ r < f (n + 1) := by
  have hcross : ∀ᶠ n in atTop, r < f n := hf.eventually (Ioi_mem_nhds hre)
  have hevent : ∀ᶠ n in atTop, N ≤ n ∧ r < f n := by
    filter_upwards [eventually_ge_atTop N, hcross] with n hn hr
    exact ⟨hn, hr⟩
  have hex : ∃ n : ℕ, N ≤ n ∧ r < f n := hevent.exists
  let k := Nat.find hex
  have hspec : N ≤ k ∧ r < f k := Nat.find_spec hex
  have hkN : k ≠ N := by
    intro h
    rw [h] at hspec
    exact (not_lt_of_ge hN) hspec.2
  have hNk : N < k := by omega
  have hn : N ≤ k - 1 := by omega
  refine ⟨k - 1, hn, ?_, ?_⟩
  · apply le_of_not_gt
    intro h
    exact (Nat.find_min hex (show k - 1 < k by omega)) ⟨hn, h⟩
  · have hpred : k - 1 + 1 = k := by omega
    rw [hpred]
    exact hspec.2

theorem morseRealization_join_deriv_nonneg
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (side : Bool) {n : ℕ}
    (hn : T.index ≤ n) :
    ∀ r ∈ Icc (T.joinLeft side n) (T.joinRight side n), 0 ≤ deriv D.w r := by
  have hj := hreal.join_data side n hn
  have hn₁ : T.index ≤ n + 1 := hn.trans (Nat.le_succ n)
  have hleft (i : ℕ) (hi : T.index ≤ i) :
      T.radius side i (T.leftX side i) ∈ radialCore D :=
    hreal.radius_mem_core side i hi _ ⟨le_rfl, (hreal.2.2.1 side i hi).2.1.le⟩
  have hright (i : ℕ) (hi : T.index ≤ i) :
      T.radius side i (T.rightX side i) ∈ radialCore D :=
    hreal.radius_mem_core side i hi _ ⟨(hreal.2.2.1 side i hi).2.1.le, le_rfl⟩
  have hL : T.joinLeft side n ∈ radialCore D := by
    rw [hj.2.1]
    cases side
    · exact hright (n + 1) hn₁
    · exact hright n hn
  have hR : T.joinRight side n ∈ radialCore D := by
    rw [hj.2.2.1]
    cases side
    · exact hleft n hn
    · exact hleft (n + 1) hn₁
  have hpositive : Ioo (T.joinLeft side n) (T.joinRight side n) ⊆
      {r | 0 ≤ deriv D.w r} := by
    intro r hr
    have hcore : r ∈ radialCore D := ⟨hL.1.trans hr.1, hr.2.trans hR.2⟩
    have hrp := hreal.geometry.1.trans hcore.1
    have hwp := hreal.geometry.2.2.2.2.1 r hcore
    have hratio : 0 < deriv D.w r / D.w r :=
      (div_pos (by norm_num : (0 : ℝ) < 2) hrp).trans_le (hj.2.2.2.2 r hr)
    exact ((div_pos_iff_of_pos_right hwp).mp hratio).le
  have hw := (contDiff_infty_iff_deriv.mp hreal.geometry.2.2.1.1).2.continuous
  have hclosed : IsClosed {r | 0 ≤ deriv D.w r} := isClosed_le continuous_const hw
  have hclosure := closure_minimal hpositive hclosed
  rw [closure_Ioo hj.1.ne] at hclosure
  exact hclosure

/-- A negative point on either actual tail lies in some retained model
image. This uses the original geometric realization, not a canonical
partition or a new coverage hypothesis. -/
theorem morseRealization_negative_tail_model_from_start
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (side : Bool)
    {N : ℕ} (hN : T.index ≤ N) {r : ℝ}
    (hr : r ∈ radialTailInterval D side (morseChainSeam T side N))
    (hneg : deriv D.w r < 0) :
    ∃ n : ℕ, N ≤ n ∧ ∃ x ∈ Icc (T.leftX side n) (T.rightX side n),
      r = T.radius side n x := by
  let f : ℕ → ℝ := fun n =>
    if side then morseChainSeam T side n else -morseChainSeam T side n
  let e : ℝ := if side then D.b else -D.a
  let x : ℝ := if side then r else -r
  have hlimits := hreal.2.2.2.2.2.2.1 side
  have hf : Tendsto f atTop (𝓝 e) := by
    cases side
    · simpa only [f, e, morseChainSeam, Bool.false_eq_true, ↓reduceIte] using hlimits.2.neg
    · simpa only [f, e, morseChainSeam, ↓reduceIte] using hlimits.1
  have hx : x < e := by
    cases side
    · exact neg_lt_neg hr.1
    · exact hr.2
  have hstart : f N ≤ x := by
    cases side
    · exact neg_le_neg hr.2.le
    · exact hr.1.le
  obtain ⟨n, hNn, hbefore, hafter⟩ := exists_nat_sandwich_of_tendsto hf hx N hstart
  have hn : T.index ≤ n := hN.trans hNn
  have hmodel : r ∈ Icc (T.radius side n (T.leftX side n))
      (T.radius side n (T.rightX side n)) := by
    have hj := hreal.join_data side n hn
    cases side with
    | false =>
      change -T.radius false n (T.rightX false n) ≤ -r at hbefore
      change -r < -T.radius false (n + 1) (T.rightX false (n + 1)) at hafter
      have hlow : T.radius false (n + 1) (T.rightX false (n + 1)) < r := by
        linarith only [hafter]
      have hhigh : r ≤ T.radius false n (T.rightX false n) := by
        linarith only [hbefore]
      refine ⟨?_, hhigh⟩
      apply le_of_not_gt
      intro h
      have hjoin : r ∈ Icc (T.joinLeft false n) (T.joinRight false n) := by
        rw [hj.2.1, hj.2.2.1]
        exact ⟨hlow.le, h.le⟩
      exact (not_lt_of_ge (morseRealization_join_deriv_nonneg hreal false hn r hjoin)) hneg
    | true =>
      change T.radius true n (T.leftX true n) ≤ r at hbefore
      change r < T.radius true (n + 1) (T.leftX true (n + 1)) at hafter
      refine ⟨hbefore, ?_⟩
      apply le_of_not_gt
      intro h
      have hjoin : r ∈ Icc (T.joinLeft true n) (T.joinRight true n) := by
        rw [hj.2.1, hj.2.2.1]
        exact ⟨h.le, hafter.le⟩
      exact (not_lt_of_ge (morseRealization_join_deriv_nonneg hreal true hn r hjoin)) hneg
  have hab := (hreal.2.2.1 side n hn).2.1
  obtain ⟨X, hX, hRX⟩ := intermediate_value_Icc hab.le
    (hreal.radius_smooth side n hn).continuous.continuousOn hmodel
  exact ⟨n, hNn, X, hX, hRX.symm⟩

theorem morseRealization_negative_tail_model
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (side : Bool)
    {N : ℕ} (hN : T.index ≤ N) {r : ℝ}
    (hr : r ∈ radialTailInterval D side (morseChainSeam T side N))
    (hneg : deriv D.w r < 0) :
    ∃ n : ℕ, T.index ≤ n ∧ ∃ x ∈ Icc (T.leftX side n) (T.rightX side n),
      r = T.radius side n x := by
  obtain ⟨n, hn, x, hx, hrx⟩ :=
    morseRealization_negative_tail_model_from_start hreal side hN hr hneg
  exact ⟨n, hN.trans hn, x, hx, hrx⟩

/-- A positive entry cannot cut a negative component. A component
meeting its outward tail has its whole closed interval in that tail. -/
theorem negativeRadialComponent_closed_subset_tail
    {D : ReferenceData} {side : Bool} {entry l h r : ℝ}
    (hcomponent : NegativeRadialComponent D l h)
    (hr : r ∈ Ioo l h) (hrtail : r ∈ radialTailInterval D side entry)
    (hentry : 0 < deriv D.w entry) :
    Icc l h ⊆ radialTailInterval D side entry := by
  cases side with
  | false =>
    have hh : h < entry := by
      apply lt_of_not_ge
      intro hle
      rcases lt_or_eq_of_le hle with hlt | heq
      · have hn := hcomponent.2.2.2.2.2 entry ⟨hr.1.trans hrtail.2, hlt⟩
        linarith only [hn, hentry]
      · have hz := hcomponent.2.2.2.2.1
        rw [← heq] at hz
        linarith only [hz, hentry]
    intro t ht
    exact ⟨hcomponent.1.trans_le ht.1, ht.2.trans_lt hh⟩
  | true =>
    have hl : entry < l := by
      apply lt_of_not_ge
      intro hle
      rcases lt_or_eq_of_le hle with hlt | heq
      · have hn := hcomponent.2.2.2.2.2 entry ⟨hlt, hrtail.1.trans hr.2⟩
        linarith only [hn, hentry]
      · have hz := hcomponent.2.2.2.1
        rw [heq] at hz
        linarith only [hz, hentry]
    intro t ht
    exact ⟨hl.trans_le ht.1, ht.2.trans_lt hcomponent.2.2.1⟩

/-- Every negative tail point belongs to a retained full model component,
whose whole closure stays on that same old tail. -/
theorem morseRealization_negative_tail_component
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (side : Bool) {N : ℕ} (hN : T.index ≤ N) {r : ℝ}
    (hr : r ∈ radialTailInterval D side (morseChainSeam T side N))
    (hneg : deriv D.w r < 0) :
    ∃ n : ℕ, T.index ≤ n ∧ ∃ l h : ℝ,
      NegativeRadialComponent D l h ∧ r ∈ Ioo l h ∧
      Icc l h ⊆ radialTailInterval D side (morseChainSeam T side N) ∧
      radialTravel D l h = Real.pi / (2 * sqrt (T.d n : ℝ)) ∧
      ∀ t ∈ Ioo l h, ∃ m, D.cellIndex m = n ∧ t ∈ D.cells m := by
  obtain ⟨n, hn, x, hx, rfl⟩ := morseRealization_negative_tail_model hreal side hN hr hneg
  have hxin := (morseRealization_negative_at_radius_iff hreal hσ side hn hx).mp hneg
  obtain ⟨hleft, hab, hright⟩ := morseRealization_turns_retained hreal side hn
  have hsub := Icc_subset_Icc hleft.le hright.le
  have ha := hsub (left_mem_Icc.mpr hab.le)
  have hb := hsub (right_mem_Icc.mpr hab.le)
  have hm := hreal.radius_strictMonoOn side n hn
  have hrI := And.intro (hm ha hx hxin.1) (hm hx hb hxin.2)
  obtain ⟨hcomponent, htravel, hcover⟩ := morseRealization_model_return hreal hσ side hn
  refine ⟨n, hn, _, _, hcomponent, hrI, ?_, htravel, hcover⟩
  exact negativeRadialComponent_closed_subset_tail hcomponent hrI hr
    (morseRealization_seam_deriv_pos hreal hσ side hN)

end ContinuousFlexibility.Radial
