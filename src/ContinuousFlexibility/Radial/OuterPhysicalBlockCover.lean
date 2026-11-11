import ContinuousFlexibility.Radial.OuterLocalizerBlocks
import ContinuousFlexibility.Radial.OuterDeepFactory
import ContinuousFlexibility.Radial.OuterFullCore

/-!
# Exact seam blocks met by the outer core and actual deep edges

A right node edge is one seam block. A left node edge crosses the next
seam and is contained in two consecutive blocks. The complete left initial
edge and the complete transition core also have explicit two-block covers.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

theorem morseRealized_log_block_mem {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (right : Bool) (p : ℕ) (hp : M.index ≤ p) {x : ℝ}
    (hx : x ∈ Icc (tailPhysicalLog right (morseChainSeam M right p))
      (tailPhysicalLog right (morseChainSeam M right (p + 1)))) :
    tailPhysicalRadius right x ∈ morseChainBlock M right p := by
  have hpos (k : ℕ) (hk : M.index ≤ k) : 0 < morseChainSeam M right k := by
    have hc := morseRealized_mass_geometry h right k hk
    cases right
    · exact h.geometry.1.trans hc.2.2.1.1
    · exact h.geometry.1.trans hc.1.1
  change r07OutwardLog right (morseChainSeam M right p) ≤ x ∧
    x ≤ r07OutwardLog right (morseChainSeam M right (p + 1)) at hx
  have hx' : x ∈ uIcc (r07OutwardLog right (morseChainSeam M right p))
      (r07OutwardLog right (morseChainSeam M right (p + 1))) :=
    ⟨(min_le_left _ _).trans hx.1, hx.2.trans (le_max_right _ _)⟩
  change tailPhysicalRadius right x ∈ uIcc (morseChainSeam M right p) (morseChainSeam M right (p + 1))
  exact r07_radius_mem_log_interval (hpos p hp) (hpos (p + 1) (hp.trans (Nat.le_succ p))) hx'

/-- The actual closed node edge meets only its own seam block and the next.
On the right the first alternative always suffices. -/
theorem morsePhysicalDeepTail_edge_blocks {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (right : Bool) (j N : ℕ) (hN : M.index ≤ N) (η K : ℝ) (n : ℕ) :
    let Q := morsePhysicalDeepTail M D right j (N + 1) (morseOuterDeepEntrance M right N) η K
    ∀ x ∈ Icc (Q.node n) (Q.node (n + 1)),
      tailPhysicalRadius right x ∈ morseChainBlock M right (N + 1 + n) ∨
        tailPhysicalRadius right x ∈ morseChainBlock M right (N + 1 + n + 1) := by
  intro x hx
  let p := N + 1 + n
  have hp : M.index ≤ p := by dsimp only [p]; omega
  have hp1 : M.index ≤ p + 1 := hp.trans (Nat.le_succ p)
  have he : N + 1 + (n + 1) = p + 1 := by dsimp only [p]; omega
  cases right with
  | true =>
      change log (morseChainSeam M true p) ≤ x ∧
        x ≤ log (morseChainSeam M true (N + 1 + (n + 1))) at hx
      left
      apply morseRealized_log_block_mem h true p hp
      change log (morseChainSeam M true p) ≤ x ∧ x ≤ log (morseChainSeam M true (p + 1))
      simpa only [he] using hx
  | false =>
      change -log (morseChainMassEnd M false p) ≤ x ∧
        x ≤ -log (morseChainMassEnd M false (N + 1 + (n + 1))) at hx
      have hxU : x ≤ -log (morseChainMassEnd M false (p + 1)) := by simpa only [he] using hx.2
      have ho := morseRealized_left_log_order h p hp
      have ho' := morseRealized_left_log_order h (p + 1) hp1
      by_cases hc : x ≤ -log (morseChainSeam M false (p + 1))
      · left
        exact morseRealized_log_block_mem h false p hp ⟨ho.1.le.trans hx.1, hc⟩
      · right
        exact morseRealized_log_block_mem h false (p + 1) hp1
          ⟨(lt_of_not_ge hc).le, hxU.trans (ho'.2.1.trans ho'.2.2.1).le⟩

/-- The full initial resistance interval uses blocks `N` and `N+1`.
The right initial interval is empty because its entrance is already node zero. -/
theorem morsePhysicalDeepTail_initial_blocks {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (right : Bool) (j N : ℕ) (hN : M.index ≤ N) (η K : ℝ) :
    let Q := morsePhysicalDeepTail M D right j (N + 1) (morseOuterDeepEntrance M right N) η K
    ∀ x ∈ Ico Q.entrance (Q.node 0),
      tailPhysicalRadius right x ∈ morseChainBlock M right N ∨
        tailPhysicalRadius right x ∈ morseChainBlock M right (N + 1) := by
  intro x hx
  cases right with
  | true =>
      have he := morsePhysicalDeepTail_right_entrance h j N hN η K
      have hxU := hx.2.trans_eq he
      exact False.elim ((not_lt_of_ge hx.1) hxU)
  | false =>
      change -log (M.radius false N (M.leftX false N)) ≤ x ∧
        x < -log (morseChainMassEnd M false (N + 1 + 0)) at hx
      have hxU : x ≤ -log (morseChainMassEnd M false (N + 1)) := by
        simpa only [Nat.add_zero] using hx.2.le
      have ho := morseRealized_left_log_order h N hN
      have ho' := morseRealized_left_log_order h (N + 1) (hN.trans (Nat.le_succ N))
      by_cases hc : x ≤ -log (morseChainSeam M false (N + 1))
      · left
        exact morseRealized_log_block_mem h false N hN
          ⟨(ho.1.trans ho.2.1).le.trans hx.1, hc⟩
      · right
        exact morseRealized_log_block_mem h false (N + 1) (hN.trans (Nat.le_succ N))
          ⟨(lt_of_not_ge hc).le, hxU.trans (ho'.2.1.trans ho'.2.2.1).le⟩

/-- The complete finite core lies in the two seam blocks with labels
`N-1` and `N`, including its outgoing right join. -/
theorem morseOuterFullCore_block_cover {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (right : Bool) (N : ℕ) (hN : M.index < N) {r : ℝ}
    (hr : r ∈ Icc (morseOuterCoreLeft M right N) (morseOuterFullCoreRight M right N)) :
    r ∈ morseChainBlock M right (N - 1) ∨ r ∈ morseChainBlock M right N := by
  have hp : M.index ≤ N - 1 := by omega
  have he : N - 1 + 1 = N := by omega
  have hend := (morseRealized_retained_endpoints h right (N - 1) hp).2.2
  have hj := h.join_data right (N - 1) hp
  have hjN := h.join_data right N hN.le
  have hwindow :
      outerOutwardRadius right (morseChainSeam M right (N - 1)) ≤ outerOutwardRadius right r ∧
        outerOutwardRadius right r ≤ outerOutwardRadius right (morseChainSeam M right (N + 1)) := by
    cases right with
    | true =>
        change M.joinLeft true (N - 1) ≤ r ∧ r ≤ M.joinRight true N at hr
        have hL : M.joinLeft true (N - 1) = M.radius true (N - 1) (M.rightX true (N - 1)) := by
          simpa only [ite_true] using hj.2.1
        have hR : M.joinRight true N = M.radius true (N + 1) (M.leftX true (N + 1)) := by
          simpa only [ite_true] using hjN.2.2.1
        rw [hL, hR] at hr
        exact ⟨hend.le.trans hr.1, hr.2⟩
    | false =>
        change M.radius false N (M.leftX false N) ≤ r ∧ r ≤ M.joinRight false (N - 1) at hr
        have hR : M.joinRight false (N - 1) = M.radius false (N - 1) (M.leftX false (N - 1)) := by
          simpa only [Bool.false_eq_true, ite_false] using hj.2.2.1
        rw [hR] at hr
        have hnext : M.radius false (N + 1) (M.rightX false (N + 1)) <
            M.radius false N (M.leftX false N) := by
          simpa only [hjN.2.1, hjN.2.2.1, Bool.false_eq_true, ite_false] using hjN.1
        change -M.radius false (N - 1) (M.rightX false (N - 1)) ≤ -r ∧
          -r ≤ -M.radius false (N + 1) (M.rightX false (N + 1))
        exact ⟨neg_le_neg (hr.2.trans hend.le), neg_le_neg (hnext.le.trans hr.1)⟩
  by_cases hc : outerOutwardRadius right r ≤ outerOutwardRadius right (morseChainSeam M right N)
  · left
    apply (morseRealized_mem_block_iff_outward h right (N - 1) hp r).mpr
    exact ⟨hwindow.1, by simpa only [he] using hc⟩
  · right
    exact (morseRealized_mem_block_iff_outward h right N hN.le r).mpr
      ⟨(lt_of_not_ge hc).le, hwindow.2⟩

end ContinuousFlexibility.Radial
