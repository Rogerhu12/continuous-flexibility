module

public import ContinuousFlexibility.Radial.SelectedLaterPhysicalIncoming
public import ContinuousFlexibility.Radial.SelectedRetainedMorseProfile
public import ContinuousFlexibility.Radial.TerminalMorseLiftEnergy

/-!
# The actual normalized terminal cap on a retained reference

The preceding cell coordinates identify both selected endpoints exactly.
The same radius-scaled incoming solution therefore supplies the profile,
equation, zero value, unit value and initial derivative required by the
terminal source and energy estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem MorseChainGeometryWitness.cell_terminal_parameters {T : MorseChainData}
    (G : MorseChainGeometryWitness T) {m : ℕ} (hm : T.index ≤ m) :
    0 < morseChainB T m ∧ 4 * morseChainB T m < morseChainA T m ∧
      morseChainA T m ≤ 1 / 1000 ∧
      morseChainA T m ^ 9 / (9 : ℝ) ^ 9 ≤ morseChainB T m ∧
      morseChainB T m ≤ morseChainA T m ^ 9 := by
  have hd : (2 : ℝ) ≤ T.d m := by
    rw [G.d_exact]
    exact_mod_cast morseChainInteger_ge_two m
  have hp := morseChainParameters_pos T m hd
  have hb := morseChainB_A_bounds T m ((by norm_num : (1 : ℝ) ≤ 2).trans hd)
  refine ⟨hp.2, hp.1, ?_, hb⟩
  apply morseChainA_le_of_sq_ge_log T m (G.d_exact m) (by norm_num)
  have hm100 : (100 : ℝ) ≤ m := by exact_mod_cast G.start_large.trans hm
  have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100) hm100 2
  have hlog := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9000)
  norm_num at hlog ⊢
  linarith only [hlog, hsq]

theorem MorseChainGeometryWitness.scaled_previousCap_endpoints {T : MorseChainData}
    (G : MorseChainGeometryWitness T) (κ : ℝ) (side : Bool) {m : ℕ}
    (hm : T.index ≤ m) :
    let k := m - T.index
    let A := morseChainA T m
    let B := morseChainB T m
    (κ * G.factor side k) * G.normal k
        (if side then morseRightTurn A B else morseShortLeftCapCut) =
      κ * r07PreviousCellCut T side m ∧
    (κ * G.factor side k) * G.normal k
        (if side then morseRightCapEnd A B (1 / 100) else morseCellLeftCut) =
      κ * r07PreviousCellJoin T side m := by
  let k := m - T.index
  have hk : T.index + k = m := Nat.add_sub_of_le hm
  have hR : T.radius side m = fun x => G.factor side k * G.normal k x := by
    simpa only [hk] using G.radius_eq side k
  have hl : T.leftX side m = morseCellLeftCut := by
    simpa only [hk] using G.leftX_eq side k
  have hr : T.rightX side m = morseRightCapEnd (morseChainA T m)
      (morseChainB T m) (1 / 100) := by
    simpa only [hk] using G.rightX_eq side k
  constructor
  · simp only [r07PreviousCellCut, r07CapCut, hR, mul_assoc, k]
  · simp only [r07PreviousCellJoin, hl, hr, hR, mul_assoc, k]

/-- The entire normalized cap maps into the two actual cap endpoints. -/
theorem terminalMorse_cap_radius_mem (side : Bool) {A B s x : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s)
    (hr : IsNormalizedMorseCell A B r)
    (hx : x ∈ Icc (if side then morseRightTurn A B else morseCellLeftCut)
      (if side then morseRightCapEnd A B (1 / 100) else morseShortLeftCapCut)) :
    s * r x ∈ uIcc
      (s * r (if side then morseRightTurn A B else morseShortLeftCapCut))
      (s * r (if side then morseRightCapEnd A B (1 / 100) else morseCellLeftCut)) := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hm : MonotoneOn r (Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100))) :=
    (morseCell_strictMonoOn hr.smooth (fun t ht =>
      (by positivity : 0 < A ^ 5 / 100).trans_le
        (terminalMorse_retained_speed_lower hr ht))).monotoneOn
  have hsub : Icc (if side then morseRightTurn A B else morseCellLeftCut)
      (if side then morseRightCapEnd A B (1 / 100) else morseShortLeftCapCut) ⊆
      Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)) := by
    cases side
    · exact Icc_subset_Icc le_rfl
        (((morseShortLeftCapCut_lt_leftTurn hB hAB).trans (morseTurn_order hB hAB)).le.trans
          (le_add_of_nonneg_right (morseRightCapLength_pos hA (by norm_num)).le))
    · exact Icc_subset_Icc (morseCellLeftCut_lt_rightTurn hB hAB).le le_rfl
  have hlo := mul_le_mul_of_nonneg_left
    (hm (hsub ⟨le_rfl, hx.1.trans hx.2⟩) (hsub hx) hx.1) hs.le
  have hhi := mul_le_mul_of_nonneg_left
    (hm (hsub hx) (hsub ⟨hx.1.trans hx.2, le_rfl⟩) hx.2) hs.le
  cases side
  · simp only [Bool.false_eq_true, ite_false] at hlo hhi ⊢
    rw [uIcc_of_ge (hlo.trans hhi)]
    exact ⟨hlo, hhi⟩
  · simp only [ite_true] at hlo hhi ⊢
    rw [uIcc_of_le (hlo.trans hhi)]
    exact ⟨hlo, hhi⟩

theorem SeedRetainedPair.reference_later_cap_data {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    {D : ReferenceData} (hw : D.w = P.pair.profile) (hS : IsSelectedTail S)
    (G : MorseChainGeometryWitness S.chain) (hentry : S.entry = r07CellEntry S.chain)
    (hfirst : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hC : 1000 ≤ S.Cstar) (side : Bool) {n j : ℕ}
    (hn : S.chain.index < n) (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand S.chain S.Cstar n j)
    (hcut : S.cut side n = r07PreviousCellCut S.chain side (n - 1))
    (hjoin : S.joinInner side n = r07PreviousCellJoin S.chain side (n - 1))
    (hu : ContDiff ℝ ∞ (S.incoming side j)) :
    let m := n - 1
    let A := morseChainA S.chain m
    let B := morseChainB S.chain m
    let r := G.normal (m - S.chain.index)
    let s := P.sideRadius side * G.factor side (m - S.chain.index)
    let weightScale := P.sideHeight side * morseChainAmplitude S.chain S.sigma m
    let U := radialRadiusScale (P.sideRadius side) 1 (S.incoming side j)
    0 < s ∧ 0 < weightScale ∧ IsNormalizedMorseCell A B r ∧ ContDiff ℝ ∞ U ∧
      (∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)),
        D.w (s * r x) = weightScale * (s * deriv r x)) ∧
      (∀ x ∈ Icc (if side then morseRightTurn A B else morseCellLeftCut)
          (if side then morseRightCapEnd A B (1 / 100) else morseShortLeftCapCut),
        radialJacobi ((j : ℝ) ^ 2) D.w U (s * r x) = 0) ∧
      U (s * r (if side then morseRightTurn A B else morseShortLeftCapCut)) = 0 ∧
      U (s * r (if side then morseRightCapEnd A B (1 / 100) else morseCellLeftCut)) = 1 ∧
      (side = true → 0 < deriv U (s * r (morseRightTurn A B))) := by
  let m := n - 1
  let k := m - S.chain.index
  let A := morseChainA S.chain m
  let B := morseChainB S.chain m
  let r := G.normal k
  let κ := P.sideRadius side
  let s := κ * G.factor side k
  have hm : S.chain.index ≤ m := by dsimp only [m]; omega
  have hk : S.chain.index + k = m := Nat.add_sub_of_le hm
  have hκ : 0 < κ := P.sideRadius_pos side
  have hs : 0 < s := mul_pos hκ (G.factorLo_pos.trans_le (G.factor_bounds side k).1)
  have hr : IsNormalizedMorseCell A B r := by simpa only [hk] using G.model k
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hB : 0 < B := (hreal.retained_data side m hm).1
  have hAB : 4 * B < A := (hreal.retained_data side m hm).2.1
  have hdata := P.reference_later_incoming_data hw hS G hentry hfirst hC side
    hn hj heven hband hcut hjoin hu
  have hends := G.scaled_previousCap_endpoints κ side hm
  rw [← hcut, ← hjoin] at hends
  have hp : κ * S.joinInner side n ∈
      uIcc (κ * S.cut side n) (κ * S.entry side n) := by
    apply (mem_uIcc_div_pos hκ).mp
    have he : κ * S.joinInner side n / κ = S.joinInner side n := by
      field_simp [hκ.ne']
    rw [he]
    exact (selected_later_span_retained hS G hentry side hn hj heven hband hcut).1
  refine ⟨hs, mul_pos (P.sideHeight_pos side)
    (morseChainAmplitude_pos S.chain S.sigma hS.2.2.1 m), hr, hdata.1, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact P.reference_normalized_morse_profile_at hw hS G hfirst side hm hx
  · intro x hx
    have hmem := terminalMorse_cap_radius_mem side hB hAB hs hr hx
    rw [hends.1, hends.2] at hmem
    exact hdata.2.2.2.2.1 _ (uIcc_subset_uIcc_left hp hmem)
  · rw [hends.1]
    exact hdata.2.1
  · rw [hends.2]
    exact hdata.2.2.1
  · intro hside
    subst side
    simp only [ite_true] at hends
    rw [hends.1]
    exact hdata.2.2.2.1

end ContinuousFlexibility.Radial
