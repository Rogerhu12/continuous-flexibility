module

public import ContinuousFlexibility.Radial.R07JoinParameterJets
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Updating one height scales precisely the corresponding outward tail

The cell amplitudes are cumulative products.  An update at index `n` therefore
multiplies all later cell amplitudes by one common positive scalar.  The exact
parameter identities for the actual joins transfer this scaling to every
physical point of the outward tail, as a full smooth germ.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter Function
open scoped Topology ContDiff BigOperators

theorem morseHeight_update_admissible {σ : ℕ → ℝ}
    (hσ : ∀ i, 1 ≤ σ i ∧ σ i ≤ 2) (n : ℕ) {t : ℝ} (ht : 1 ≤ t ∧ t ≤ 2) :
    ∀ i, 1 ≤ update σ n t i ∧ update σ n t i ≤ 2 := by
  intro i
  by_cases hi : i = n
  · subst i
    simpa only [update_self] using ht
  · simpa only [update_of_ne hi] using hσ i

/-- A single height update has one exact scalar effect on every subsequent
cell amplitude. -/
theorem morseChainAmplitude_update {T : Statements.MorseChainData} {σ : ℕ → ℝ}
    {n m : ℕ} {t : ℝ} (hN : T.index ≤ n) (hnm : n ≤ m) (hσn : σ n ≠ 0) :
    Statements.morseChainAmplitude T (update σ n t) m =
      (t / σ n) * Statements.morseChainAmplitude T σ m := by
  have hn : n ∈ Finset.Icc T.index m := Finset.mem_Icc.mpr ⟨hN, hnm⟩
  have hp := Finset.mul_prod_erase (Finset.Icc T.index m) σ hn
  unfold Statements.morseChainAmplitude
  rw [Finset.prod_update_of_mem hn, Finset.sdiff_singleton_eq_erase, ← hp]
  field_simp [hσn]

theorem morseChainHeightLogRatio_scale {T : Statements.MorseChainData}
    {σ τ : ℕ → ℝ} (hσ : ∀ i, 1 ≤ σ i ∧ σ i ≤ 2) {m : ℕ} {scale : ℝ}
    (hs : 0 < scale)
    (hA : Statements.morseChainAmplitude T τ m = scale * Statements.morseChainAmplitude T σ m) :
    morseChainHeightLogRatio T τ m = morseChainHeightLogRatio T σ m + log scale := by
  unfold morseChainHeightLogRatio
  rw [hA, log_mul hs.ne' (morseChainAmplitude_pos T σ hσ m).ne']
  ring

private theorem eventuallyEq_add_shift {f g h : ℝ → ℝ} {x a b c : ℝ}
    (hf : f =ᶠ[𝓝 x] fun y => h y + a) (hg : g =ᶠ[𝓝 x] fun y => h y + b)
    (ha : a = b + c) : f =ᶠ[𝓝 x] fun y => g y + c := by
  filter_upwards [hf, hg] with y hy hz
  rw [hy, hz, ha]
  ring

/-- If both adjacent cell amplitudes scale by the same positive number, the
actual chosen join scales by that number on a neighborhood of every point
of the closed physical join. -/
theorem morseChainChosenJoinProfile_scale_germ {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (σ τ : ℕ → ℝ)
    (hσ : ∀ i, 1 ≤ σ i ∧ σ i ≤ 2) (hτ : ∀ i, 1 ≤ τ i ∧ τ i ≤ 2)
    (side : Bool) (k : ℕ) {scale x : ℝ} (hs : 0 < scale)
    (hDeparture : Statements.morseChainAmplitude T τ (T.index + morseChainJoinDeparture side k) =
      scale * Statements.morseChainAmplitude T σ (T.index + morseChainJoinDeparture side k))
    (hArrival : Statements.morseChainAmplitude T τ (T.index + morseChainJoinArrival side k) =
      scale * Statements.morseChainAmplitude T σ (T.index + morseChainJoinArrival side k))
    (hx : x ∈ Icc (T.joinLeft side (T.index + k)) (T.joinRight side (T.index + k))) :
    morseChainChosenJoinProfile G τ hτ side k =ᶠ[𝓝 x]
      fun y => scale * morseChainChosenJoinProfile G σ hσ side k y := by
  let P := morseChainChosenJoin G σ hσ side k
  let Q := morseChainChosenJoin G τ hτ side k
  obtain ⟨hPL, hPR⟩ := morseChainChosenJoin_log_germs G σ hσ side k
  obtain ⟨hQL, hQR⟩ := morseChainChosenJoin_log_germs G τ hτ side k
  have hLg (y : ℝ) (hy : y ∈ Icc (T.joinLeft side (T.index + k))
      (T.joinLeft side (T.index + k) + morseChainProfileJoinCutoff T side k)) :
      Q.leftLog =ᶠ[𝓝 y] fun z => P.leftLog z + log scale :=
    eventuallyEq_add_shift (hQL y hy) (hPL y hy) (morseChainHeightLogRatio_scale hσ hs hDeparture)
  have hRg (y : ℝ) (hy : y ∈ Icc
      (T.joinRight side (T.index + k) - morseChainProfileJoinCutoff T side k)
      (T.joinRight side (T.index + k))) :
      Q.rightLog =ᶠ[𝓝 y] fun z => P.rightLog z + log scale :=
    eventuallyEq_add_shift (hQR y hy) (hPR y hy) (morseChainHeightLogRatio_scale hσ hs hArrival)
  have hab := morseChainPhysicalJoin_order G side k
  have hh : 0 < morseChainProfileJoinCutoff T side k :=
    div_pos (sub_pos.mpr hab) (by norm_num)
  have hsep : T.joinLeft side (T.index + k) + morseChainProfileJoinCutoff T side k <
      T.joinRight side (T.index + k) - morseChainProfileJoinCutoff T side k := by
    unfold morseChainProfileJoinCutoff
    linarith only [hab]
  have he := morseJoinProfile_germs_of_germs hh hh hsep
    (P.left_smooth.add contDiff_const) (P.right_smooth.add contDiff_const)
    Q.left_smooth Q.right_smooth hLg hRg hx
  exact he.trans (Filter.Eventually.of_forall fun y =>
    morseJoinProfile_add_log_same P.left_smooth P.right_smooth hs y)

private theorem morseOutward_piece_exists_ge {endpoint : ℝ}
    (D : MorseOutwardProfileData endpoint) (N : ℕ) {x : ℝ}
    (hx : D.enter N ≤ x) (he : x < endpoint) :
    ∃ k, N ≤ k ∧
      (x ∈ Icc (D.enter k) (D.leave k) ∨ x ∈ Icc (D.leave k) (D.enter (k + 1))) := by
  obtain ⟨k, hk⟩ := morse_outward_block_exists D.limit
    ((D.enter_strictMono.monotone (Nat.zero_le N)).trans hx) he
  have hNk : N ≤ k := by
    by_contra h
    have hle : k + 1 ≤ N := by omega
    exact (not_le_of_gt hk.2) ((D.enter_strictMono.monotone hle).trans hx)
  refine ⟨k, hNk, ?_⟩
  rcases le_total x (D.leave k) with h | h
  · exact Or.inl ⟨hk.1, h⟩
  · exact Or.inr ⟨h, hk.2.le⟩

/-- Every point beyond a selected cell entrance belongs to a retained cell
or to an intervening join, with an outward index no smaller than the entrance
index.  The same geometric statement covers the two orientations. -/
theorem morseChain_tail_cell_or_join {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (N : ℕ) {x : ℝ}
    (hx : if side then x ∈ Ico (morseChainCellLeftRadius T true N) G.rightEnd
      else x ∈ Ioc 1 (morseChainCellRightRadius T false N)) :
    ∃ k, N ≤ k ∧
      (x ∈ Icc (morseChainCellLeftRadius T side k) (morseChainCellRightRadius T side k) ∨
        x ∈ Icc (T.joinLeft side (T.index + k)) (T.joinRight side (T.index + k))) := by
  cases side
  · let D := morseChainLeftProfileData G morseUnitHeights morseUnitHeights_admissible
    obtain ⟨k, hk, hm | hj⟩ := morseOutward_piece_exists_ge D N
      (neg_le_neg hx.2) (neg_lt_neg hx.1)
    · refine ⟨k, hk, Or.inl ?_⟩
      have h₁ : -morseChainCellRightRadius T false k ≤ -x := hm.1
      have h₂ : -x ≤ -morseChainCellLeftRadius T false k := hm.2
      exact ⟨by simpa only [neg_neg] using neg_le_neg h₂,
        by simpa only [neg_neg] using neg_le_neg h₁⟩
    · refine ⟨k, hk, Or.inr ?_⟩
      rw [(G.joins k).2.2.1, (G.joins k).2.2.2]
      have h₁ : -morseChainCellLeftRadius T false k ≤ -x := hj.1
      have h₂ : -x ≤ -morseChainCellRightRadius T false (k + 1) := hj.2
      exact ⟨by simpa only [morseChainCellRightRadius, neg_neg] using neg_le_neg h₂,
        by simpa only [morseChainCellLeftRadius, neg_neg] using neg_le_neg h₁⟩
  · let D := morseChainRightProfileData G morseUnitHeights morseUnitHeights_admissible
    obtain ⟨k, hk, hm | hj⟩ := morseOutward_piece_exists_ge D N hx.1 hx.2
    · exact ⟨k, hk, Or.inl hm⟩
    · refine ⟨k, hk, Or.inr ?_⟩
      rw [(G.joins k).1, (G.joins k).2.1]
      exact hj

/-- Common scaling of all cell amplitudes after one entrance scales the
entire actual outward tail, including every transition point. -/
theorem morseChainGluedProfile_scale_tail_germ {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (σ τ : ℕ → ℝ)
    (hσ : ∀ i, 1 ≤ σ i ∧ σ i ≤ 2) (hτ : ∀ i, 1 ≤ τ i ∧ τ i ≤ 2)
    (N : ℕ) {scale : ℝ} (hs : 0 < scale)
    (hA : ∀ k, N ≤ k → Statements.morseChainAmplitude T τ (T.index + k) =
      scale * Statements.morseChainAmplitude T σ (T.index + k))
    (side : Bool) {x : ℝ}
    (hx : if side then x ∈ Ico (morseChainCellLeftRadius T true N) G.rightEnd
      else x ∈ Ioc 1 (morseChainCellRightRadius T false N)) :
    morseChainGluedProfile G τ hτ =ᶠ[𝓝 x] fun y => scale * morseChainGluedProfile G σ hσ y := by
  obtain ⟨k, hk, hm | hj⟩ := morseChain_tail_cell_or_join G side N hx
  · have hτg := morseChainGluedProfile_model_germ G τ hτ side k hm
    have hσg := morseChainGluedProfile_model_germ G σ hσ side k hm
    filter_upwards [hτg, hσg] with y hyτ hyσ
    rw [hyτ, hyσ]
    simp only [morseChainPhysicalModelHeight, hA k hk]
    ring
  · have hdep : N ≤ morseChainJoinDeparture side k := by
      cases side
      · exact hk.trans (Nat.le_succ k)
      · exact hk
    have harr : N ≤ morseChainJoinArrival side k := by
      cases side
      · exact hk
      · exact hk.trans (Nat.le_succ k)
    have he := morseChainChosenJoinProfile_scale_germ G σ τ hσ hτ side k hs
      (hA _ hdep) (hA _ harr) hj
    exact (morseChainGluedProfile_join_germ G τ hτ side k hj).trans
      (he.trans ((morseChainGluedProfile_join_germ G σ hσ side k hj).symm.fun_comp
        (fun z => scale * z)))

/-- Updating `σ n` leaves the normalized homogeneous problem on the entire
outward tail unchanged: the actual coefficient is multiplied by `t / σ n`. -/
theorem morseChainGluedProfile_update_tail_germ {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (σ : ℕ → ℝ)
    (hσ : ∀ i, 1 ≤ σ i ∧ σ i ≤ 2) {n : ℕ} (hn : T.index ≤ n)
    {t : ℝ} (ht : 1 ≤ t ∧ t ≤ 2) (side : Bool) {x : ℝ}
    (hx : if side then x ∈ Ico (morseChainCellLeftRadius T true (n - T.index)) G.rightEnd
      else x ∈ Ioc 1 (morseChainCellRightRadius T false (n - T.index))) :
    morseChainGluedProfile G (update σ n t) (morseHeight_update_admissible hσ n ht) =ᶠ[𝓝 x]
      fun y => (t / σ n) * morseChainGluedProfile G σ hσ y := by
  have hs : 0 < t / σ n := div_pos (zero_lt_one.trans_le ht.1)
    (zero_lt_one.trans_le (hσ n).1)
  apply morseChainGluedProfile_scale_tail_germ G σ (update σ n t) hσ
    (morseHeight_update_admissible hσ n ht) (n - T.index) hs ?_ side hx
  intro k hk
  exact morseChainAmplitude_update hn (by omega) (zero_lt_one.trans_le (hσ n).1).ne'

end ContinuousFlexibility.Radial
