module

public import ContinuousFlexibility.Radial.R07ChainIncoming
public import ContinuousFlexibility.Radial.StandInBoundarySlope

/-!
# The actual later stand-in has positive normalized slope at the join

The function is the selected incoming solution itself: its Dirichlet
value and derivative sign at the canonical preceding cap, and its actual
radial equation on the complete cut-to-entry interval, identify the
stand-in. Pullback through the realized cap and Riccati comparison give
the positive normalized slope and its upper bound one half.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem r10a_actual_later_standIn_bounds {T : MorseChainData}
    (G : MorseChainGeometryWitness T) {σ K : ℕ → ℝ} {D : ReferenceData}
    (hreal : MorseChainRealization T σ D K)
    (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) {C : ℝ} (hC : 1000 ≤ C)
    (right : Bool) (k : ℕ) {j : ℕ} (hj : 2 ≤ j)
    (hband : radialFrequencyBand T C (T.index + k + 1) j)
    {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (hode : ∀ x ∈ uIcc (r07PreviousCellCut T right (T.index + k))
      (r07CellEntry T right (T.index + k + 1)),
      radialJacobi ((j : ℝ) ^ 2) D.w u x = 0)
    (hzero : u (r07PreviousCellCut T right (T.index + k)) = 0)
    (hsign : if right then 0 < deriv u (r07PreviousCellCut T right (T.index + k))
      else deriv u (r07PreviousCellCut T right (T.index + k)) < 0) :
    let p := r07PreviousCellJoin T right (T.index + k)
    0 < u p ∧ 0 < standInBoundarySlope (r07OutwardSign right) ((j : ℝ) ^ 2) p u ∧
      standInBoundarySlope (r07OutwardSign right) ((j : ℝ) ^ 2) p u ≤ 1 / 2 := by
  let m := T.index + k
  let A := Statements.morseChainA T m
  let B := Statements.morseChainB T m
  let s := G.factor right k
  let r := G.normal k
  let R := r07CapRadius right A B s r
  let L := r07CapLength right A
  let c := r07PreviousCellCut T right m
  let p := r07PreviousCellJoin T right m
  let e := r07CellEntry T right (m + 1)
  have hm : T.index ≤ m := Nat.le_add_right _ _
  have hmnext : T.index ≤ m + 1 := hm.trans (Nat.le_succ _)
  have hB : 0 < B := (hreal.retained_data right m hm).1
  have hAB : 4 * B < A := (hreal.retained_data right m hm).2.1
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hd₂ : (2 : ℝ) ≤ T.d m := by
    rw [G.d_exact]
    exact_mod_cast morseChainInteger_ge_two m
  have hBA : B ≤ A ^ 9 :=
    (morseChainB_A_bounds T m ((by norm_num : (1 : ℝ) ≤ 2).trans hd₂)).2
  have hs : 0 < s := G.factorLo_pos.trans_le (G.factor_bounds right k).1
  have hr : IsNormalizedMorseCell A B r := G.model k
  have hRad : T.radius right m = fun x => s * r x := G.radius_eq right k
  have hxL : T.leftX right m = morseCellLeftCut := G.leftX_eq right k
  have hxR : T.rightX right m = morseRightCapEnd A B (1 / 100) := G.rightX_eq right k
  have hL : 0 < L := r07CapLength_pos right hA
  have hR : ContDiff ℝ ∞ R := r07CapRadius_smooth right A B s hr.smooth
  have hdir : ∀ t ∈ Icc 0 L, if right then 0 < deriv R t else deriv R t < 0 :=
    fun t ht => (r07CapRadius_model_bounds right hB hAB hs hr ht).2
  have hc : R 0 = c := by
    change s * r (r07CapPoint right A B 0) = T.radius right m (r07CapCut right A B)
    rw [r07CapPoint_zero, hRad]
  have hp : R L = p := by
    change s * r (r07CapPoint right A B (r07CapLength right A)) =
      T.radius right m (if right then T.rightX right m else T.leftX right m)
    rw [r07CapPoint_end, hRad, hxL, hxR]
    cases right <;> rfl
  have hcore : ∀ t ∈ Icc 0 L, R t ∈ Statements.radialCore D := by
    intro t ht
    have hx : r07CapPoint right A B t ∈ Icc (T.leftX right m) (T.rightX right m) := by
      rw [hxL, hxR]
      exact r07CapPoint_mem_cell right hB hAB ht
    have h := hreal.radius_mem_core right m hm _ hx
    rw [hRad] at h
    exact h
  have hcCore : c ∈ Statements.radialCore D := by
    rw [← hc]
    exact hcore 0 ⟨le_rfl, hL.le⟩
  have hpCore : p ∈ Statements.radialCore D := by
    rw [← hp]
    exact hcore L ⟨hL.le, le_rfl⟩
  have heCore : e ∈ Statements.radialCore D := by
    apply hreal.radius_mem_core right (m + 1) hmnext
    have hcuts := (hreal.2.2.1 right (m + 1) hmnext).2.1.le
    cases right
    · exact ⟨hcuts, le_rfl⟩
    · exact ⟨le_rfl, hcuts⟩
  have houter : if right then p < e else e < p := by
    have hjoin := hreal.join_data right m hm
    have hlt := hjoin.1
    rw [hjoin.2.1, hjoin.2.2.1] at hlt
    cases right <;> exact hlt
  have hmap : ∀ t ∈ Icc 0 L, R t ∈ Icc (min c e) (max c e) := by
    have h := r07_cap_maps_to_entry right hL hR hdir (by simpa only [hp] using houter)
    simpa only [hc] using h
  have hlam : 0 < Statements.morseChainAmplitude T σ m := morseChainAmplitude_pos T σ hσ m
  have haction : 1000 ≤ (j : ℝ) * sqrt A :=
    r07_cap_action_of_later_band T hC (by have := G.start_large; omega)
      (fun n _ => G.d_exact n) hband hm (by omega)
  let lam := morseChainAmplitude T σ m
  let scale := lam * r07OutwardSign right
  have hscale : scale ≠ 0 := mul_ne_zero hlam.ne'
    (by cases right <;> norm_num [r07OutwardSign])
  have hweight : ∀ t ∈ Icc 0 L, D.w (R t) = scale * deriv R t := by
    intro t ht
    rw [r07CapRadius_deriv right A B s t hr.smooth]
    change D.w (s * r (r07CapPoint right A B t)) =
      (lam * r07OutwardSign right) * (s * deriv r (r07CapPoint right A B t) * r07OutwardSign right)
    rw [r07_realized_normalized_cell_profile G hreal right k _
      (r07CapPoint_mem_cell right hB hAB ht)]
    calc
      _ = lam * (s * deriv r (r07CapPoint right A B t)) * r07OutwardSign right ^ 2 := by
        rw [r07OutwardSign_sq, mul_one]
      _ = _ := by ring
  obtain ⟨hU, hU'⟩ := r07_cap_pullback_system hL hscale hR
    hreal.geometry.2.2.1.1 hu hweight (fun t ht => hode (R t) (hmap t ht))
  have hj₀ : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  have hinit : 0 < deriv u (R 0) * deriv R 0 := by
    have hd := hdir 0 ⟨le_rfl, hL.le⟩
    have hs₀ : if right then 0 < deriv u (R 0) else deriv u (R 0) < 0 := by
      simpa only [hc] using hsign
    cases right
    · exact mul_pos_of_neg_of_neg hs₀ hd
    · exact mul_pos hs₀ hd
  have hzero₀ : u (R 0) = 0 := by simpa only [hc] using hzero
  have hε : r07OutwardSign right = 1 ∨ r07OutwardSign right = -1 := by
    cases right
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hbound := standInBoundarySlope_bounds_of_cap hε hL (sq_pos_of_pos hj₀)
    (r07CapRiccatiBound_pos right hA hj₀)
    (hreal.geometry.1.trans (hcore L ⟨hL.le, le_rfl⟩).1)
    ((r07OutwardSign_mul_pos_iff right _).mpr (hdir L ⟨hL.le, le_rfl⟩))
    hU hU' (fun t ht => r07CapRadius_scalar_bound right hB hAB hBA hs hr ht)
    hzero₀ hinit (r07CapRadius_slope_small right hB hAB hs hj₀ hr haction)
  simpa only [hp] using hbound

/-- The actual selected incoming solution is the stand-in on its canonical
later cap, so its true normalized boundary slope has the required bounds. -/
theorem selected_later_standIn_bounds {S : SelectedTailData}
    (hS : IsSelectedTail S) (G : MorseChainGeometryWitness S.chain)
    (hC : 1000 ≤ S.Cstar) (right : Bool) {n j : ℕ}
    (hn : S.chain.index < n) (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand S.chain S.Cstar n j)
    (hcut : S.cut right n = r07PreviousCellCut S.chain right (n - 1))
    (hjoin : S.joinInner right n = r07PreviousCellJoin S.chain right (n - 1))
    (hu : ContDiff ℝ ∞ (S.incoming right j)) :
    S.incoming right j (S.joinInner right n) = 1 ∧
      0 < standInBoundarySlope (r07OutwardSign right) ((j : ℝ) ^ 2)
        (S.joinInner right n) (S.incoming right j) ∧
      standInBoundarySlope (r07OutwardSign right) ((j : ℝ) ^ 2)
        (S.joinInner right n) (S.incoming right j) ≤ 1 / 2 := by
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hb := hS.2.2.2.2.2 right n j hj heven hband
  rcases hb with ⟨_, _, _, _, _, heq, hinit, _, _, _, hODE, _, _⟩
  have hentry : S.entry right n = r07CellEntry S.chain right n := heq
  have hnorm : S.incoming right j (S.cut right n) = 0 ∧
      S.incoming right j (S.joinInner right n) = 1 ∧
      (if right then 0 < deriv (S.incoming right j) (S.cut right n)
        else deriv (S.incoming right j) (S.cut right n) < 0) := by
    simpa only [if_neg hn.ne'] using hinit
  let k := n - 1 - S.chain.index
  have hm : S.chain.index + k = n - 1 := by dsimp only [k]; omega
  have hn' : S.chain.index + k + 1 = n := by omega
  have hn'' : n - 1 + 1 = n := by omega
  have hbound := r10a_actual_later_standIn_bounds G hreal hS.2.2.1 hC right k hj
    (by simpa only [hn'] using hband) hu
    (by simpa only [hm, hn', hn'', hentry, hcut] using hODE.2)
    (by simpa only [hm, hcut] using hnorm.1)
    (by simpa only [hm, hcut] using hnorm.2.2)
  refine ⟨hnorm.2.1, ?_⟩
  simpa only [hm, hjoin] using hbound.2

end ContinuousFlexibility.Radial
