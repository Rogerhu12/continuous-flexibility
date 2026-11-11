import ContinuousFlexibility.Radial.MorseSecondModeMassTransport
import ContinuousFlexibility.Radial.MorseCellMassTravel

/-!
# Geometry of the actual outward second-mode tail

The same signed logarithmic coordinate orders both sides outward.
All entries and nodes are actual retained Morse radii, with the original
flat endpoint as their limit.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

theorem morseSecondMode_modelOrder {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (right : Bool) {n : ℕ}
    (hn : T.index ≤ n) :
    morseSecondModeMassLeft T right n < morseChainMassEnd T right n ∧
      morseChainMassEnd T right n < T.radius right n (T.rightX right n) := by
  obtain ⟨_, hgeometry, hmodels, _, _, _, _, _, _, _⟩ := h
  have hG := hgeometry right n hn
  obtain ⟨hr, hinterval, hmodel⟩ := hmodels right n hn
  have hmono := morseCell_strictMonoOn hr (fun x hx => (hmodel x hx).1)
  have hl : T.leftX right n ∈ Icc (T.leftX right n) (T.rightX right n) :=
    ⟨le_rfl, hinterval.le⟩
  have ht : morseChainRightTurn T n ∈ Icc (T.leftX right n) (T.rightX right n) :=
    ⟨hG.2.2.2.1.le, hG.2.2.2.2.1.le⟩
  have hrx : T.rightX right n ∈ Icc (T.leftX right n) (T.rightX right n) :=
    ⟨hinterval.le, le_rfl⟩
  exact ⟨hmono hl ht hG.2.2.2.1, hmono ht hrx hG.2.2.2.2.1⟩

theorem morseSecondMode_gapOrder {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) {n : ℕ} (hn : T.index ≤ n)
    (right : Bool) :
    morseChainMassEnd T right (if right then n else n + 1) <
      morseSecondModeMassLeft T right (if right then n + 1 else n) := by
  obtain ⟨_, _, _, hjoins, _, _, _, _, _, _⟩ := h
  have hj := hjoins right n hn
  have horder := hj.1
  rw [hj.2.1, hj.2.2.1] at horder
  cases right
  · simp only [Bool.false_eq_true, ↓reduceIte] at horder ⊢
    exact (morseSecondMode_modelOrder h false (by omega : T.index ≤ n + 1)).2.trans horder
  · simp only [↓reduceIte] at horder ⊢
    exact (morseSecondMode_modelOrder h true hn).2.trans horder

theorem morseSecondMode_node_order {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) {N : ℕ} (hN : T.index ≤ N)
    (right : Bool) (n : ℕ) :
    (morseSecondModeTail D T N right).node n <
        (morseSecondModeTail D T N right).massEnd n ∧
      (morseSecondModeTail D T N right).massEnd n <
        (morseSecondModeTail D T N right).node (n + 1) := by
  have hg := morseSecondMode_profileGeometry h
  have hi : T.index ≤ N + n := hN.trans (Nat.le_add_right N n)
  have hi' : T.index ≤ N + n + 1 := by omega
  have hm := morseSecondMode_modelOrder h right hi
  have hgap := morseSecondMode_gapOrder h hi right
  have hleft := (morseSecondMode_massEndpoints h right hi).1
  have hturn := (morseSecondMode_massEndpoints h right hi).2
  have hnext := (morseSecondMode_massEndpoints h right hi').2
  cases right
  · simp only [morseSecondModeTail, Bool.false_eq_true, ↓reduceIte, Nat.add_assoc] at hgap ⊢
    exact ⟨neg_lt_neg (log_lt_log (hg.1.trans hleft.1) hm.1),
      neg_lt_neg (log_lt_log (hg.1.trans hnext.1) hgap)⟩
  · simp only [morseSecondModeTail, ↓reduceIte, Nat.add_assoc] at hgap ⊢
    exact ⟨log_lt_log (hg.1.trans hleft.1) hm.1,
      log_lt_log (hg.1.trans hturn.1) hgap⟩

theorem morseSecondMode_radius_mem_core {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) {N : ℕ} (hN : T.index < N)
    (right : Bool) {x : ℝ}
    (hx : x ∈ Ico (morseSecondModeTail D T N right).entrance
      (morseSecondModeTail D T N right).endpoint) :
    tailPhysicalRadius right x ∈ radialCore D := by
  have hg := morseSecondMode_profileGeometry h
  cases right
  · have hL := (morseSecondMode_massEndpoints h false (show T.index ≤ N - 1 by omega)).1
    have hLp : 0 < morseSecondModeMassLeft T false (N - 1) := hg.1.trans hL.1
    simp only [morseSecondModeTail, Bool.false_eq_true, ↓reduceIte] at hx
    change D.a < exp (-x) ∧ exp (-x) < D.b
    have hlow : D.a < exp (-x) := by
      have hx' : log D.a < -x := by linarith only [hx.2]
      simpa only [exp_log hg.1] using exp_lt_exp.mpr hx'
    have hhigh : exp (-x) ≤ morseSecondModeMassLeft T false (N - 1) := by
      have hx' : -x ≤ log (morseSecondModeMassLeft T false (N - 1)) := by
        linarith only [hx.1]
      simpa only [exp_log hLp] using exp_le_exp.mpr hx'
    exact ⟨hlow, hhigh.trans_lt hL.2⟩
  · have hL := (morseSecondMode_massEndpoints h true hN.le).1
    have hLp : 0 < morseSecondModeMassLeft T true N := hg.1.trans hL.1
    simp only [morseSecondModeTail, ↓reduceIte] at hx
    change D.a < exp x ∧ exp x < D.b
    have hlow : morseSecondModeMassLeft T true N ≤ exp x := by
      simpa only [exp_log hLp] using exp_le_exp.mpr hx.1
    have hhigh : exp x < D.b := by
      simpa only [exp_log (hg.1.trans hg.2.1)] using exp_lt_exp.mpr hx.2
    exact ⟨hL.1.trans_le hlow, hhigh⟩

theorem morseSecondMode_entrance_order {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) {N : ℕ} (hN : T.index < N)
    (right : Bool) :
    (morseSecondModeTail D T N right).entrance <
        (morseSecondModeTail D T N right).endpoint ∧
      (morseSecondModeTail D T N right).entrance ≤
        (morseSecondModeTail D T N right).node 0 := by
  have hg := morseSecondMode_profileGeometry h
  cases right
  · have hpred : T.index ≤ N - 1 := by omega
    have hsucc : N - 1 + 1 = N := by omega
    have hL := (morseSecondMode_massEndpoints h false hpred).1
    have hM := (morseSecondMode_massEndpoints h false hN.le).2
    have hgap := morseSecondMode_gapOrder h hpred false
    simp only [Bool.false_eq_true, ↓reduceIte, hsucc] at hgap
    simp only [morseSecondModeTail, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    exact ⟨neg_lt_neg (log_lt_log hg.1 hL.1),
      (neg_lt_neg (log_lt_log (hg.1.trans hM.1) hgap)).le⟩
  · have hL := (morseSecondMode_massEndpoints h true hN.le).1
    simp only [morseSecondModeTail, ↓reduceIte, Nat.add_zero]
    exact ⟨log_lt_log (hg.1.trans hL.1) hL.2, le_rfl⟩

private theorem morseSecondMode_shift (N : ℕ) :
    Tendsto (fun n : ℕ => N + n) atTop atTop := by
  refine tendsto_atTop.2 (fun b => ?_)
  filter_upwards [eventually_ge_atTop b] with n hn
  omega

theorem morseSecondMode_massEnd_tendsto {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) {N : ℕ} (hN : T.index ≤ N)
    (right : Bool) :
    Tendsto (fun n => morseChainMassEnd T right (N + n)) atTop
      (𝓝 (if right then D.b else D.a)) := by
  obtain ⟨_, _, _, _, _, _, hends, _, _, _⟩ := h
  have hL := (hends right).1.comp (morseSecondMode_shift N)
  have hR := (hends right).2.comp (morseSecondMode_shift N)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hL hR
  · intro n
    exact (morseSecondMode_modelOrder h right (hN.trans (Nat.le_add_right N n))).1.le
  · intro n
    exact (morseSecondMode_modelOrder h right (hN.trans (Nat.le_add_right N n))).2.le

theorem morseSecondMode_node_tendsto {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) {N : ℕ} (hN : T.index ≤ N)
    (right : Bool) :
    Tendsto (morseSecondModeTail D T N right).node atTop
      (𝓝 (morseSecondModeTail D T N right).endpoint) := by
  have hg := morseSecondMode_profileGeometry h
  have hM := morseSecondMode_massEnd_tendsto h hN right
  obtain ⟨_, _, _, _, _, _, hends, _, _, _⟩ := h
  cases right
  · have ht := (Real.continuousAt_log hg.1.ne').tendsto.comp hM
    exact ht.neg
  · have hL := (hends true).1.comp (morseSecondMode_shift N)
    exact (Real.continuousAt_log (hg.1.trans hg.2.1).ne').tendsto.comp hL

theorem morseSecondMode_density_smooth {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (N : ℕ) (right : Bool) :
    ContDiff ℝ ∞ (morseSecondModeTail D T N right).p := by
  have hw := (morseSecondMode_profileGeometry h).2.2.1.1
  have he : ContDiff ℝ ∞ (fun x : ℝ => exp ((if right then 1 else -1) * x)) :=
    (contDiff_const.mul contDiff_id).exp
  exact ((hw.comp he).mul (he.pow 7)).div_const _

theorem morseSecondMode_density_pos {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) {N : ℕ} (hN : T.index < N)
    (right : Bool) {x : ℝ}
    (hx : x ∈ Ico (morseSecondModeTail D T N right).entrance
      (morseSecondModeTail D T N right).endpoint) :
    0 < (morseSecondModeTail D T N right).p x := by
  have hg := morseSecondMode_profileGeometry h
  have hr := morseSecondMode_radius_mem_core h hN right hx
  have hw := hg.2.2.2.2.1 _ hr
  have hR := morseSecondMode_endpoint_pos hg right
  cases right <;>
    simp only [morseSecondModeTail, morseSecondModeDensity, tailPhysicalRadius,
      Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul] at hw hR ⊢ <;>
    exact div_pos (mul_pos hw (pow_pos (exp_pos _) 7)) (pow_pos hR 8)

end ContinuousFlexibility.Radial
