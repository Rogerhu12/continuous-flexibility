import ContinuousFlexibility.Radial.OuterDeepLocalization
import ContinuousFlexibility.Radial.OuterOutwardHilbert

/-!
# Actual seam windows in the outward physical coordinate

The collar in the realization contract is at most one sixteenth of each
incident block length. Thus a cell of known physical label can only meet
its own seam block and the two neighboring blocks. These are geometric
statements about the specified cell, not existential covering labels.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

theorem morseRealized_outward_seam_step {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (right : Bool) (n : ℕ) (hn : M.index ≤ n) :
    outerOutwardRadius right (morseChainSeam M right n) <
      outerOutwardRadius right (morseChainSeam M right (n + 1)) := by
  have hc := (morseRealized_retained_endpoints h right n hn).2.2
  have hj := h.join_data right n hn
  cases right with
  | false =>
      have ho : M.radius false (n + 1) (M.rightX false (n + 1)) <
          M.radius false n (M.leftX false n) := by
        simpa only [hj.2.1, hj.2.2.1, Bool.false_eq_true, ite_false] using hj.1
      change -M.radius false n (M.rightX false n) <
        -M.radius false (n + 1) (M.rightX false (n + 1))
      exact neg_lt_neg (ho.trans hc)
  | true =>
      have ho : M.radius true n (M.rightX true n) <
          M.radius true (n + 1) (M.leftX true (n + 1)) := by
        simpa only [hj.2.1, hj.2.2.1, ite_true] using hj.1
      exact hc.trans ho

theorem morseRealized_outward_seam_strictMonoOn {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (right : Bool) :
    StrictMonoOn (fun n => outerOutwardRadius right (morseChainSeam M right n)) (Ici M.index) := by
  have hs : StrictMono (fun k =>
      outerOutwardRadius right (morseChainSeam M right (M.index + k))) := by
    apply strictMono_nat_of_lt_succ
    intro k
    simpa only [Nat.add_assoc] using
      morseRealized_outward_seam_step h right (M.index + k) (Nat.le_add_right _ _)
  intro m hm n hn hmn
  change M.index ≤ m at hm
  change M.index ≤ n at hn
  have hsub : m - M.index < n - M.index := by omega
  simpa only [Nat.add_sub_of_le hm, Nat.add_sub_of_le hn] using hs hsub

private theorem outer_abs_sub_of_outward_lt (right : Bool) {a b : ℝ}
    (h : outerOutwardRadius right a < outerOutwardRadius right b) :
    |b - a| = outerOutwardRadius right b - outerOutwardRadius right a := by
  cases right with
  | false =>
      change -a < -b at h
      change |b - a| = -b - -a
      rw [abs_of_neg (by linarith : b - a < 0)]
      ring
  | true => exact abs_of_pos (sub_pos.mpr h)

theorem morseChainSeamCollar_le_inward (M : MorseChainData) (D : ReferenceData)
    (right : Bool) {n : ℕ} (hn : M.index < n) :
    morseChainSeamCollar M D right n ≤
      |morseChainSeam M right n - morseChainSeam M right (n - 1)| / 16 := by
  simp only [morseChainSeamCollar, if_pos hn]
  exact div_le_div_of_nonneg_right
    ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num)

theorem morseChainSeamCollar_le_outward (M : MorseChainData) (D : ReferenceData)
    (right : Bool) (n : ℕ) :
    morseChainSeamCollar M D right n ≤
      |morseChainSeam M right (n + 1) - morseChainSeam M right n| / 16 := by
  unfold morseChainSeamCollar
  exact div_le_div_of_nonneg_right
    ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)

/-- A region of label `i` lies strictly between seams `i-1` and `i+2`.
The strict inequalities also handle points at the region's closed endpoints. -/
theorem morseRealized_region_near_seams {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (right : Bool) {i : ℕ} (hi : M.index < i) {r : ℝ}
    (hr : r ∈ morseChainLocalizerRegion M D right i) :
    outerOutwardRadius right (morseChainSeam M right (i - 1)) < outerOutwardRadius right r ∧
      outerOutwardRadius right r < outerOutwardRadius right (morseChainSeam M right (i + 2)) := by
  have hmono := morseRealized_outward_seam_strictMonoOn h right
  have hp : M.index ≤ i - 1 := by omega
  have hprev := hmono hp hi.le (by omega : i - 1 < i)
  have hnext := hmono (hi.le.trans (Nat.le_succ i))
    (show M.index ≤ i + 2 by omega) (by omega : i + 1 < i + 2)
  have hci := morseChainSeamCollar_le_inward M D right hi
  have hcn := morseChainSeamCollar_le_outward M D right (i + 1)
  rw [outer_abs_sub_of_outward_lt right hprev] at hci
  have hnext' : outerOutwardRadius right (morseChainSeam M right (i + 1)) <
      outerOutwardRadius right (morseChainSeam M right (i + 1 + 1)) := by
    simpa only [show i + 1 + 1 = i + 2 by omega] using hnext
  rw [outer_abs_sub_of_outward_lt right hnext'] at hcn
  have hwindow :
      outerOutwardRadius right (morseChainSeam M right i) - morseChainSeamCollar M D right i ≤
          outerOutwardRadius right r ∧
        outerOutwardRadius right r ≤
          outerOutwardRadius right (morseChainSeam M right (i + 1)) +
            morseChainSeamCollar M D right (i + 1) := by
    cases right
    · change morseChainSeam M false (i + 1) - morseChainSeamCollar M D false (i + 1) ≤ r ∧
        r ≤ morseChainSeam M false i + morseChainSeamCollar M D false i at hr
      change -morseChainSeam M false i - morseChainSeamCollar M D false i ≤ -r ∧
        -r ≤ -morseChainSeam M false (i + 1) + morseChainSeamCollar M D false (i + 1)
      exact ⟨by linarith only [hr.2], by linarith only [hr.1]⟩
    · exact hr
  have heq : i + 1 + 1 = i + 2 := by omega
  simp only [heq] at hcn
  constructor <;> linarith only [hci, hcn, hwindow.1, hwindow.2, hprev, hnext]

/-- Closed physical blocks become ordinary ordered closed intervals after
the fixed outward reflection. -/
theorem morseRealized_mem_block_iff_outward {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (right : Bool) (n : ℕ) (hn : M.index ≤ n) (r : ℝ) :
    r ∈ morseChainBlock M right n ↔
      outerOutwardRadius right (morseChainSeam M right n) ≤ outerOutwardRadius right r ∧
        outerOutwardRadius right r ≤ outerOutwardRadius right (morseChainSeam M right (n + 1)) := by
  have hs := morseRealized_outward_seam_step h right n hn
  cases right with
  | false =>
      change -morseChainSeam M false n < -morseChainSeam M false (n + 1) at hs
      have ho : morseChainSeam M false (n + 1) ≤ morseChainSeam M false n := by linarith
      simp only [morseChainBlock, uIcc_of_ge ho, mem_Icc, outerOutwardRadius,
        Bool.false_eq_true, ite_false]
      constructor <;> rintro ⟨hl, hr⟩ <;> constructor <;> linarith only [hl, hr]
  | true =>
      change morseChainSeam M true n < morseChainSeam M true (n + 1) at hs
      simp only [morseChainBlock, uIcc_of_le hs.le, mem_Icc, outerOutwardRadius, ite_true]

end ContinuousFlexibility.Radial
