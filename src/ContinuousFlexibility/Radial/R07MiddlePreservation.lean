import ContinuousFlexibility.Radial.R07MiddleRealization
import ContinuousFlexibility.Radial.R07Assembly
import ContinuousFlexibility.Radial.R07ChainIncoming
import ContinuousFlexibility.Radial.R07NaturalTailScale

/-!
# Matching data are preserved outside the finite middle

The replacement has the original full profile germ on both closed tails.
Consequently it preserves the radial equation even at finite interval
endpoints, the weighted natural-tail condition, and the matching states.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem r07MiddleReferenceFamily_exterior_germ {T : MorseChainData}
    (G : MorseChainGeometryWitness T) {M : ℝ → ℝ} (hM : R07MiddleAdmissible G M)
    (phi : ℝ → ℝ) (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) {r : ℝ}
    (hr : r ≤ morseChainCellRightRadius T false 0 ∨ morseChainCellLeftRadius T true 0 ≤ r) :
    (r07MiddleReferenceFamily G M phi σ).w =ᶠ[𝓝 r] (morseChainReferenceFamily G phi σ).w := by
  rw [r07MiddleReferenceFamily_admissible G M phi σ hσ,
    morseChainReferenceFamily_admissible G phi σ hσ]
  exact (r07MiddlePatchedProfile_germs G hM σ hσ).1 r hr

theorem r07CellEntry_outside_middle {T : MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) {n : ℕ} (hn : T.index ≤ n) :
    if side then morseChainCellLeftRadius T true 0 ≤ r07CellEntry T side n
    else r07CellEntry T side n ≤ morseChainCellRightRadius T false 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  let P := morseChainSelectedProfileData G (fun _ => 1) (fun _ => ⟨le_rfl, by norm_num⟩)
  cases side
  · exact le_of_neg_le_neg (P.left.enter_strictMono.monotone (Nat.zero_le k))
  · exact P.right.enter_strictMono.monotone (Nat.zero_le k)

theorem r07PreviousCellCut_outside_middle {T : MorseChainData}
    (G : MorseChainGeometryWitness T) {σ C : ℕ → ℝ} {D : ReferenceData}
    (hreal : MorseChainRealization T σ D C) (side : Bool) (k : ℕ) :
    if side then morseChainCellLeftRadius T true 0 ≤ r07PreviousCellCut T side (T.index + k)
    else r07PreviousCellCut T side (T.index + k) ≤ morseChainCellRightRadius T false 0 := by
  have hret := hreal.retained_data side (T.index + k) (Nat.le_add_right _ _)
  have hA : 0 < morseChainA T (T.index + k) :=
    (mul_pos (by norm_num) hret.1).trans hret.2.1
  have hcut := r07CapPoint_mem_cell side hret.1 hret.2.1
    (left_mem_Icc.mpr (r07CapLength_pos side hA).le)
  rw [r07CapPoint_zero] at hcut
  have hx : r07CapCut side (morseChainA T (T.index + k)) (morseChainB T (T.index + k)) ∈
      Icc (T.leftX side (T.index + k)) (T.rightX side (T.index + k)) := by
    rw [G.leftX_eq side k, G.rightX_eq side k]
    exact hcut
  have hEq := G.actual_radius_equation side k
  have hmono := (morseCell_strictMonoOn hEq.1 (fun t ht => (hEq.2.2 t ht).1)).monotoneOn
  have hcell : r07PreviousCellCut T side (T.index + k) ∈
      Icc (morseChainCellLeftRadius T side k) (morseChainCellRightRadius T side k) :=
    ⟨hmono (left_mem_Icc.mpr hEq.2.1.le) hx hx.1,
      hmono hx (right_mem_Icc.mpr hEq.2.1.le) hx.2⟩
  have hentry := r07CellEntry_outside_middle G side (Nat.le_add_right T.index k)
  cases side
  · exact hcell.2.trans hentry
  · exact hentry.trans hcell.1

theorem r07MiddleReferenceFamily_natural_iff {T : MorseChainData}
    (G : MorseChainGeometryWitness T) {M : ℝ → ℝ} (hM : R07MiddleAdmissible G M)
    (phi : ℝ → ℝ) (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (side : Bool) {e : ℝ}
    (he : if side then morseChainCellLeftRadius T true 0 ≤ e
      else e ≤ morseChainCellRightRadius T false 0) (j : ℕ) (v : ℝ → ℝ) :
    RadialNaturalTail (r07MiddleReferenceFamily G M phi σ) side j e v ↔
      RadialNaturalTail (morseChainReferenceFamily G phi σ) side j e v := by
  refine radialNaturalTail_scale_iff
    (D := morseChainReferenceFamily G phi σ)
    (E := r07MiddleReferenceFamily G M phi σ)
    (right := side) (entry := e) (scale := 1) rfl rfl (by norm_num) ?_ j v
  intro r hr
  have hout : r ≤ morseChainCellRightRadius T false 0 ∨ morseChainCellLeftRadius T true 0 ≤ r := by
    cases side
    · exact Or.inl (hr.2.le.trans he)
    · exact Or.inr (he.trans hr.1.le)
  simpa only [one_mul] using (r07MiddleReferenceFamily_exterior_germ G hM phi σ hσ hout).eq_of_nhds

theorem r07MiddleReferenceFamily_natural_entry_iff {T : MorseChainData}
    (G : MorseChainGeometryWitness T) {M : ℝ → ℝ} (hM : R07MiddleAdmissible G M)
    (phi : ℝ → ℝ) (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (side : Bool) {n : ℕ} (hn : T.index ≤ n) (j : ℕ) (v : ℝ → ℝ) :
    RadialNaturalTail (r07MiddleReferenceFamily G M phi σ) side j (r07CellEntry T side n) v ↔
      RadialNaturalTail (morseChainReferenceFamily G phi σ) side j (r07CellEntry T side n) v :=
  r07MiddleReferenceFamily_natural_iff G hM phi σ hσ side
    (r07CellEntry_outside_middle G side hn) j v

theorem r07MiddleReferenceFamily_radialState {T : MorseChainData}
    (G : MorseChainGeometryWitness T) {M : ℝ → ℝ} (hM : R07MiddleAdmissible G M)
    (phi : ℝ → ℝ) (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) {r p : ℝ}
    (hr : r ≤ morseChainCellRightRadius T false 0 ∨ morseChainCellLeftRadius T true 0 ≤ r)
    (hp : p ≤ morseChainCellRightRadius T false 0 ∨ morseChainCellLeftRadius T true 0 ≤ p)
    (j : ℕ) (u : ℝ → ℝ) :
    radialState (r07MiddleReferenceFamily G M phi σ) j r
        ((r07MiddleReferenceFamily G M phi σ).w p) u =
      radialState (morseChainReferenceFamily G phi σ) j r
        ((morseChainReferenceFamily G phi σ).w p) u := by
  unfold radialState
  rw [(r07MiddleReferenceFamily_exterior_germ G hM phi σ hσ hr).eq_of_nhds,
    (r07MiddleReferenceFamily_exterior_germ G hM phi σ hσ hp).eq_of_nhds]

theorem R07MatchingGeometry.replace_middle {T : MorseChainData}
    {G : MorseChainGeometryWitness T} {M phi : ℝ → ℝ} (hM : R07MiddleAdmissible G M)
    {σ : ℕ → ℝ} (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    {side : Bool} {n j : ℕ} {c p e : ℝ} {u v : ℝ → ℝ}
    (h : R07MatchingGeometry T (morseChainReferenceFamily G phi σ) side n j c p e u v)
    (hn : n ≠ T.index)
    (hc : if side then morseChainCellLeftRadius T true 0 ≤ c
      else c ≤ morseChainCellRightRadius T false 0) :
    R07MatchingGeometry T (r07MiddleReferenceFamily G M phi σ) side n j c p e u v := by
  have hp : p ∈ uIcc c e := by
    have ho := h.order
    cases side
    · rw [uIcc_of_ge (ho.1.trans ho.2).le]
      exact ⟨ho.1.le, ho.2.le⟩
    · rw [uIcc_of_le (ho.1.trans ho.2).le]
      exact ⟨ho.1.le, ho.2.le⟩
  have hout (r : ℝ) (hr : r ∈ uIcc c e) :
      r ≤ morseChainCellRightRadius T false 0 ∨ morseChainCellLeftRadius T true 0 ≤ r := by
    have ho := h.order
    cases side
    · rw [uIcc_of_ge (ho.1.trans ho.2).le] at hr
      exact Or.inl (hr.2.trans hc)
    · rw [uIcc_of_le (ho.1.trans ho.2).le] at hr
      exact Or.inr (hc.trans hr.1)
  have he : if side then morseChainCellLeftRadius T true 0 ≤ e
      else e ≤ morseChainCellRightRadius T false 0 := by
    have ho := h.order
    cases side
    · exact (ho.1.trans ho.2).le.trans hc
    · exact hc.trans (ho.1.trans ho.2).le
  have hg (r : ℝ) (hr : r ∈ uIcc c e) :=
    r07MiddleReferenceFamily_exterior_germ G hM phi σ hσ (hout r hr)
  refine ⟨h.cut_mem, h.entry_mem, h.join_mem, ?_, h.order, h.entry_eq, ?_, ?_,
    h.cut_smooth, h.entry_smooth, ?_, ?_⟩
  · rw [(hg p hp).eq_of_nhds]
    exact h.join_positive
  · simpa only [if_neg hn] using h.initial
  · intro r hr
    have hr' : r ∈ uIcc c p := ⟨hr.1.le, hr.2.le⟩
    rw [(hg r (uIcc_subset_uIcc_left hp hr')).deriv_eq]
    exact h.profile_increasing r hr
  · refine ⟨h.incoming_equation.1, fun r hr => ?_⟩
    rw [radialJacobi_profile_congr_germ (hg r hr)]
    exact h.incoming_equation.2 r hr
  · exact (r07MiddleReferenceFamily_natural_iff G hM phi σ hσ side he j v).mpr h.outgoing_natural

theorem R07MatchingGeometry.angle_replace_middle {T : MorseChainData}
    {G : MorseChainGeometryWitness T} {M phi : ℝ → ℝ} (hM : R07MiddleAdmissible G M)
    {σ : ℕ → ℝ} (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    {side : Bool} {n j : ℕ} {c p e : ℝ} {u v : ℝ → ℝ}
    (h : R07MatchingGeometry T (morseChainReferenceFamily G phi σ) side n j c p e u v)
    (hc : if side then morseChainCellLeftRadius T true 0 ≤ c
      else c ≤ morseChainCellRightRadius T false 0) :
    radialAngleSine
        (radialState (r07MiddleReferenceFamily G M phi σ) j e
          ((r07MiddleReferenceFamily G M phi σ).w p) u)
        (radialState (r07MiddleReferenceFamily G M phi σ) j e
          ((r07MiddleReferenceFamily G M phi σ).w p) v) =
      radialAngleSine
        (radialState (morseChainReferenceFamily G phi σ) j e
          ((morseChainReferenceFamily G phi σ).w p) u)
        (radialState (morseChainReferenceFamily G phi σ) j e
          ((morseChainReferenceFamily G phi σ).w p) v) := by
  have hp : p ≤ morseChainCellRightRadius T false 0 ∨ morseChainCellLeftRadius T true 0 ≤ p := by
    have ho := h.order
    cases side
    · exact Or.inl (ho.2.le.trans hc)
    · exact Or.inr (hc.trans ho.1.le)
  have he : e ≤ morseChainCellRightRadius T false 0 ∨ morseChainCellLeftRadius T true 0 ≤ e := by
    have ho := h.order
    cases side
    · exact Or.inl ((ho.1.trans ho.2).le.trans hc)
    · exact Or.inr (hc.trans (ho.1.trans ho.2).le)
  rw [r07MiddleReferenceFamily_radialState G hM phi σ hσ he hp,
    r07MiddleReferenceFamily_radialState G hM phi σ hσ he hp]

end ContinuousFlexibility.Radial
