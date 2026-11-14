module

public import ContinuousFlexibility.Radial.OuterPhysicalBlockCover
public import ContinuousFlexibility.Radial.OuterEndpointDistances

/-!
# Uniform reverse localization beyond one actual outer cutoff

Low-label cells stay a fixed positive distance from both endpoints by the
original accumulating-profile bounds. Far enough outward, every nonzero
specified localizer therefore has a label to which the seam-region clause
applies. This yields the same two-label displacement on ordinary deep
edges, the complete initial interval, and the full compact core.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology
open ContinuousFlexibility.Statements

/-- A sufficiently short endpoint distance excludes every low physical
label, independently of which localizer is nonzero at the point. -/
theorem morseRealized_localizer_index_of_distance {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (right : Bool) (p m : ℕ) {r : ℝ}
    (hnear : (if right then D.b - morseChainSeam M right p
      else morseChainSeam M right p - D.a) <
        (C 0)⁻¹ * exp (-((M.index : ℝ) + 1) ^ 2))
    (hafter : outerOutwardRadius right (morseChainSeam M right p) ≤ outerOutwardRadius right r)
    (hθ : D.localizer m r ≠ 0) : M.index < D.cellIndex m := by
  have hpart : RadialPartition D := h.accumulating.2.1
  have hcell : r ∈ D.cells m := hpart.2.2.1 m hθ
  have hC : 0 < C 0 := h.constants_pos 0
  have hlower : (C 0)⁻¹ * exp (-((D.cellIndex m : ℝ) + 1) ^ 2) ≤ min (r - D.a) (D.b - r) := by
    rcases h.accumulating with ⟨_, _, _, _, _, _, hd, _⟩
    exact (hd m r hcell).1
  have hmin : min (r - D.a) (D.b - r) ≤
      (if right then D.b - morseChainSeam M right p else morseChainSeam M right p - D.a) := by
    cases right with
    | false =>
        change -morseChainSeam M false p ≤ -r at hafter
        change min (r - D.a) (D.b - r) ≤ morseChainSeam M false p - D.a
        exact (min_le_left _ _).trans (by linarith only [hafter])
    | true =>
        change morseChainSeam M true p ≤ r at hafter
        change min (r - D.a) (D.b - r) ≤ D.b - morseChainSeam M true p
        exact (min_le_right _ _).trans (by linarith only [hafter])
  by_contra hnot
  have hi : D.cellIndex m ≤ M.index := le_of_not_gt hnot
  have hcast : (D.cellIndex m : ℝ) + 1 ≤ (M.index : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hi 1
  have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (D.cellIndex m : ℝ) + 1) hcast 2
  have he := mul_le_mul_of_nonneg_left (exp_le_exp.mpr (neg_le_neg hs)) (inv_nonneg.mpr hC.le)
  exact (not_lt_of_ge ((he.trans hlower).trans hmin)) hnear

theorem morseRealized_eventually_label_distance {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C) :
    ∀ᶠ p : ℕ in atTop, ∀ right : Bool,
      (if right then D.b - morseChainSeam M right p else morseChainSeam M right p - D.a) <
        (C 0)⁻¹ * exp (-((M.index : ℝ) + 1) ^ 2) := by
  have hC : 0 < C 0 := h.constants_pos 0
  have hδ : 0 < (C 0)⁻¹ * exp (-((M.index : ℝ) + 1) ^ 2) := by positivity
  apply eventually_all.mpr
  intro right
  have ht := morseRealized_seam_tendsto h right
  have hz : Tendsto (fun p => if right then D.b - morseChainSeam M right p
      else morseChainSeam M right p - D.a) atTop (𝓝 0) := by
    cases right
    · simpa only [Bool.false_eq_true, ite_false, sub_self] using ht.sub (tendsto_const_nhds (x := D.a))
    · simpa only [ite_true, sub_self] using (tendsto_const_nhds (x := D.b)).sub ht
  exact hz.eventually (eventually_lt_nhds hδ)

theorem morseRealized_eventually_low_localizer_labels {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C) :
    ∀ᶠ p : ℕ in atTop, ∀ (right : Bool) (m : ℕ) (r : ℝ),
      outerOutwardRadius right (morseChainSeam M right p) ≤ outerOutwardRadius right r →
        D.localizer m r ≠ 0 → M.index < D.cellIndex m := by
  filter_upwards [morseRealized_eventually_label_distance h] with p hp
  intro right m r hafter hθ
  exact morseRealized_localizer_index_of_distance h right p m (hp right) hafter hθ

/-- The three concrete reverse support conclusions for the actual localizers.
The location labels are `N+1+n` on an edge, `N+1` on the initial interval,
and `N` on the core. -/
def MorseOuterLocalizerLabels (M : MorseChainData) (D : ReferenceData) (N : ℕ) : Prop :=
    (∀ (right : Bool) (j : ℕ) (η K : ℝ) (n m : ℕ) (x : ℝ),
        let Q := morsePhysicalDeepTail M D right j (N + 1) (morseOuterDeepEntrance M right N) η K
        x ∈ Icc (Q.node n) (Q.node (n + 1)) → D.localizer m (tailPhysicalRadius right x) ≠ 0 →
          N + 1 + n ≤ D.cellIndex m + 2 ∧ D.cellIndex m ≤ N + 1 + n + 2) ∧
      (∀ (right : Bool) (j : ℕ) (η K : ℝ) (m : ℕ) (x : ℝ),
        let Q := morsePhysicalDeepTail M D right j (N + 1) (morseOuterDeepEntrance M right N) η K
        x ∈ Icc Q.entrance (Q.node 0) → D.localizer m (tailPhysicalRadius right x) ≠ 0 →
          N + 1 ≤ D.cellIndex m + 2 ∧ D.cellIndex m ≤ N + 1 + 2) ∧
      (∀ (right : Bool) (m : ℕ) (r : ℝ),
        r ∈ Icc (morseOuterCoreLeft M right N) (morseOuterFullCoreRight M right N) →
          D.localizer m r ≠ 0 → N ≤ D.cellIndex m + 2 ∧ D.cellIndex m ≤ N + 2)

theorem morseOuter_localizer_labels_of_low {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (N : ℕ) (hN : M.index + 3 ≤ N)
    (hlow : ∀ (right : Bool) (m : ℕ) (r : ℝ),
      outerOutwardRadius right (morseChainSeam M right (N - 1)) ≤ outerOutwardRadius right r →
        D.localizer m r ≠ 0 → M.index < D.cellIndex m) :
    MorseOuterLocalizerLabels M D N := by
  have hNi : M.index ≤ N := by omega
  have hNp : M.index ≤ N - 1 := by omega
  have hblock (right : Bool) (p m : ℕ) (hp : N - 1 ≤ p) {r : ℝ}
      (hr : r ∈ morseChainBlock M right p) (hθ : D.localizer m r ≠ 0) :
      p ≤ D.cellIndex m + 1 ∧ D.cellIndex m ≤ p + 1 := by
    have hpi : M.index ≤ p := hNp.trans hp
    have hafter : outerOutwardRadius right (morseChainSeam M right (N - 1)) ≤
        outerOutwardRadius right r :=
      ((morseRealized_outward_seam_strictMonoOn h right).monotoneOn hNp hpi hp).trans
        ((morseRealized_mem_block_iff_outward h right p hpi r).mp hr).1
    exact morseRealized_localizer_block_indices h right (hlow right m r hafter hθ) hpi hr hθ
  refine ⟨?_, ?_, ?_⟩
  · intro right j η K n m x
    dsimp only
    intro hx hθ
    rcases morsePhysicalDeepTail_edge_blocks h right j N hNi η K n x hx with hr | hr
    · have hb := hblock right (N + 1 + n) m (by omega) hr hθ
      omega
    · have hb := hblock right (N + 1 + n + 1) m (by omega) hr hθ
      omega
  · intro right j η K m x
    dsimp only
    intro hx hθ
    rcases lt_or_eq_of_le hx.2 with hlt | heq
    · rcases morsePhysicalDeepTail_initial_blocks h right j N hNi η K x ⟨hx.1, hlt⟩ with hr | hr
      · have hb := hblock right N m (by omega) hr hθ
        omega
      · have hb := hblock right (N + 1) m (by omega) hr hθ
        omega
    · have ho := morsePhysicalDeepTail_node_order h right j (N + 1)
        (hNi.trans (Nat.le_succ N)) (morseOuterDeepEntrance M right N) η K 0
      have hxedge : x ∈ Icc
          ((morsePhysicalDeepTail M D right j (N + 1) (morseOuterDeepEntrance M right N) η K).node 0)
          ((morsePhysicalDeepTail M D right j (N + 1) (morseOuterDeepEntrance M right N) η K).node (0 + 1)) :=
        ⟨heq.ge, heq.le.trans (ho.1.trans ho.2).le⟩
      rcases morsePhysicalDeepTail_edge_blocks h right j N hNi η K 0 x hxedge with hr | hr
      · have hb := hblock right (N + 1 + 0) m (by omega) hr hθ
        omega
      · have hb := hblock right (N + 1 + 0 + 1) m (by omega) hr hθ
        omega
  · intro right m r hr hθ
    rcases morseOuterFullCore_block_cover h right N (by omega) hr with hb | hb
    · have hi := hblock right (N - 1) m le_rfl hb hθ
      omega
    · have hi := hblock right N m (by omega) hb hθ
      omega

/-- One fixed-profile cutoff works on all three parts of the actual outer region. -/
theorem morseOuter_eventually_localizer_labels {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C) :
    ∀ᶠ N : ℕ in atTop, M.index + 3 ≤ N ∧ MorseOuterLocalizerLabels M D N := by
  have hlower := (tendsto_sub_atTop_nat 1).eventually
    (morseRealized_eventually_low_localizer_labels h)
  filter_upwards [hlower, eventually_ge_atTop (M.index + 3)] with N hlow hN
  exact ⟨hN, morseOuter_localizer_labels_of_low h N hN hlow⟩

/-- Common coefficient constants and common endpoints give one cutoff before
all height choices. Each conclusion still concerns the actual localizer of
that height choice; equality of the partitions is not assumed. -/
theorem morseOuter_eventually_uniform_localizer_labels
    (M : MorseChainData) (C : ℕ → ℝ) (family : (ℕ → ℝ) → ReferenceData)
    (hfamily : ∀ σ, (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) → MorseChainRealization M σ (family σ) C)
    (hends : ∀ σ τ, (family σ).a = (family τ).a ∧ (family σ).b = (family τ).b) :
    ∀ᶠ N : ℕ in atTop, M.index + 3 ≤ N ∧
      ∀ σ, (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) → MorseOuterLocalizerLabels M (family σ) N := by
  let σ₀ : ℕ → ℝ := fun _ => 1
  have hσ₀ : ∀ k, 1 ≤ σ₀ k ∧ σ₀ k ≤ 2 := fun _ => ⟨le_rfl, by norm_num [σ₀]⟩
  have h₀ := hfamily σ₀ hσ₀
  have hnear := (tendsto_sub_atTop_nat 1).eventually (morseRealized_eventually_label_distance h₀)
  filter_upwards [hnear, eventually_ge_atTop (M.index + 3)] with N hn hN
  refine ⟨hN, ?_⟩
  intro σ hσ
  apply morseOuter_localizer_labels_of_low (hfamily σ hσ) N hN
  intro right m r hafter hθ
  apply morseRealized_localizer_index_of_distance (hfamily σ hσ) right (N - 1) m ?_ hafter hθ
  have he := hends σ σ₀
  simpa only [he.1, he.2] using hn right

end ContinuousFlexibility.Radial
