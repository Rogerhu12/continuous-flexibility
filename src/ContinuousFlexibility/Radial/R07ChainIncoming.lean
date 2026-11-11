import ContinuousFlexibility.Radial.R07MorseIncoming
import ContinuousFlexibility.Radial.MorseRealizationBasic

/-!
# Incoming solutions at the actual chain cut, join, and entry

This specialization supplies the physical interval and every profile
hypothesis directly from the realization and its geometric witness.
The resulting homogeneous solution exists on the whole cut-to-entry
interval, including the connector after the preceding Morse cell.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff

def r07PreviousCellCut (T : Statements.MorseChainData) (right : Bool) (m : ℕ) : ℝ :=
  T.radius right m (r07CapCut right (Statements.morseChainA T m) (Statements.morseChainB T m))

def r07PreviousCellJoin (T : Statements.MorseChainData) (right : Bool) (m : ℕ) : ℝ :=
  T.radius right m (if right then T.rightX right m else T.leftX right m)

def r07CellEntry (T : Statements.MorseChainData) (right : Bool) (n : ℕ) : ℝ :=
  T.radius right n (if right then T.leftX right n else T.rightX right n)

/-- The closed oriented cap lies inside every interval that extends from
its cut past the join in the outward direction. -/
theorem r07_cap_maps_to_entry (right : Bool) {R : ℝ → ℝ} {L e : ℝ}
    (hL : 0 < L) (hR : ContDiff ℝ ∞ R)
    (hdir : ∀ t ∈ Icc 0 L, if right then 0 < deriv R t else deriv R t < 0)
    (houter : if right then R L < e else e < R L) :
    ∀ t ∈ Icc 0 L, R t ∈ Icc (min (R 0) e) (max (R 0) e) := by
  have hmono : StrictMonoOn (fun t => r07OutwardSign right * R t) (Icc 0 L) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 L)
      (contDiff_const.mul hR).continuous.continuousOn
    intro t ht
    rw [deriv_const_mul_field]
    exact (r07OutwardSign_mul_pos_iff right _).mpr (hdir t (interior_subset ht))
  have horder := r07_cap_order right hL hR hdir
  intro t ht
  have hleft := hmono.monotoneOn ⟨le_rfl, hL.le⟩ ht ht.1
  have hright := hmono.monotoneOn ht ⟨hL.le, le_rfl⟩ ht.2
  cases right
  · have hec : e ≤ R 0 := houter.le.trans horder.le
    simp only [r07OutwardSign, Bool.false_eq_true, if_false, neg_one_mul, neg_le_neg_iff] at hleft hright
    rw [min_eq_right hec, max_eq_left hec]
    exact ⟨houter.le.trans hright, hleft⟩
  · have hce : R 0 ≤ e := horder.le.trans houter.le
    simp only [r07OutwardSign, if_true, one_mul] at hleft hright
    rw [min_eq_left hce, max_eq_right hce]
    exact ⟨hleft, hright.trans houter.le⟩

/-- The realization's cell identity in the normalized model used by the
two cap constructions. -/
theorem r07_realized_normalized_cell_profile {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) {σ K : ℕ → ℝ} {D : Statements.ReferenceData}
    (hreal : Statements.MorseChainRealization T σ D K) (right : Bool) (k : ℕ) :
    ∀ x ∈ Icc morseCellLeftCut
      (morseRightCapEnd (Statements.morseChainA T (T.index + k))
        (Statements.morseChainB T (T.index + k)) (1 / 100)),
      D.w (G.factor right k * G.normal k x) =
        Statements.morseChainAmplitude T σ (T.index + k) *
          (G.factor right k * deriv (G.normal k) x) := by
  intro x hx
  have hx' : x ∈ Icc (T.leftX right (T.index + k)) (T.rightX right (T.index + k)) := by
    rw [G.leftX_eq right k, G.rightX_eq right k]
    exact hx
  have he := hreal.profile_eq right (T.index + k) (Nat.le_add_right _ _) x hx'
  rw [G.radius_eq right k, deriv_const_mul_field] at he
  exact he

/-- Every band strictly after the starting cell has an actual normalized
incoming solution. The cap, the whole connector, and the entry radius are
all retained in the same smooth physical initial-value solution. -/
theorem exists_r07_incoming_on_preceding_cell {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) {σ K : ℕ → ℝ} {D : Statements.ReferenceData}
    (hreal : Statements.MorseChainRealization T σ D K)
    (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) {C : ℝ} (hC : 1000 ≤ C)
    (right : Bool) (k : ℕ) {j : ℕ} (hj : 2 ≤ j)
    (hband : Statements.radialFrequencyBand T C (T.index + k + 1) j) :
    let m := T.index + k
    let c := r07PreviousCellCut T right m
    let p := r07PreviousCellJoin T right m
    let e := r07CellEntry T right (m + 1)
    ∃ (u : ℝ → ℝ) (a : ℝ),
      c ∈ Statements.radialCore D ∧ p ∈ Statements.radialCore D ∧ e ∈ Statements.radialCore D ∧
      0 < D.w p ∧ (if right then c < p ∧ p < e else e < p ∧ p < c) ∧
      u c = 0 ∧ u p = 1 ∧ (if right then 0 < deriv u c else deriv u c < 0) ∧
      (∀ y ∈ Statements.radialOpenSpan c p, 0 < deriv D.w y) ∧ ContDiff ℝ ∞ u ∧
      Statements.RadialHomogeneousOn D j (uIcc c e) u ∧
      a ∈ Icc (-(3 : ℝ) / 2) (-1 / 2) ∧
      Statements.radialState D j p (D.w p) u = (1, a) := by
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
  have hsol := exists_r07_normalized_morse_incoming right hreal.geometry hB hAB hBA hs hlam hj hr
    (lt_min hcCore.1 heCore.1) (min_le_max : min c e ≤ max c e) (max_lt hcCore.2 heCore.2) hmap
    (r07_realized_normalized_cell_profile G hreal right k) haction
  have hc' : s * r (r07CapCut right A B) = c := by
    rw [← hc]
    change s * r (r07CapCut right A B) = s * r (r07CapPoint right A B 0)
    rw [r07CapPoint_zero]
  have hp' : s * r (r07CapEnd right A B) = p := by
    rw [← hp]
    change s * r (r07CapEnd right A B) = s * r (r07CapPoint right A B (r07CapLength right A))
    rw [r07CapPoint_end]
  rw [hc', hp'] at hsol
  obtain ⟨u, a, hu, hu₀, hup, hsign, hcap, hwpos, hode, ha, hstate⟩ := hsol
  have horder : if right then c < p ∧ p < e else e < p ∧ p < c := by
    cases right
    · exact ⟨houter, hcap⟩
    · exact ⟨hcap, houter⟩
  have hhom : Statements.RadialHomogeneousOn D j (uIcc c e) u := by
    cases right
    · have hec : e ≤ c := houter.le.trans hcap.le
      rw [uIcc_of_ge hec]
      simpa only [min_eq_right hec, max_eq_left hec] using hode
    · have hce : c ≤ e := hcap.le.trans houter.le
      rw [uIcc_of_le hce]
      simpa only [min_eq_left hce, max_eq_right hce] using hode
  exact ⟨u, a, hcCore, hpCore, heCore, hreal.geometry.2.2.2.2.1 p hpCore,
    horder, hu₀, hup, hsign, hwpos, hu, hhom, ha, hstate⟩

end ContinuousFlexibility.Radial
