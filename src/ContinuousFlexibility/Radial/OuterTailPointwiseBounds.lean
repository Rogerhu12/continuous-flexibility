module

public import ContinuousFlexibility.Radial.OuterPhysicalGaugeBounds
public import ContinuousFlexibility.Radial.OuterInitialResistanceBounds

/-!
# A common pointwise estimate including the initial interval

The initial interval is assigned the first tail label. Ordinary closed
edges retain their actual labels. This cover includes the entrance and
every node, and its Green bound uses the same constructed basis.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open scoped BigOperators
open ContinuousFlexibility.Statements

def OuterTailPoint (T : DeepTailData) (n : ℕ) (x : ℝ) : Prop :=
  (n = 0 ∧ x ∈ Icc T.entrance (T.node 0)) ∨
    x ∈ Icc (T.node n) (T.node (n + 1))

theorem outerTailPoint_mem {T : DeepTailData} (hT : DeepTailHypotheses T)
    {n : ℕ} {x : ℝ} (hx : OuterTailPoint T n x) : x ∈ Ico T.entrance T.endpoint := by
  rcases hx with ⟨_, hx⟩ | hx
  · exact ⟨hx.1, hx.2.trans_lt (deepTail_node_lt_endpoint hT 0)⟩
  · exact tailActualEdge_interval_subset hT n hx

theorem exists_outerTailPoint {T : DeepTailData} (hT : DeepTailHypotheses T)
    {x : ℝ} (hx : x ∈ Ico T.entrance T.endpoint) : ∃ n, OuterTailPoint T n x := by
  by_cases hfirst : x ≤ T.node 0
  · exact ⟨0, Or.inl ⟨rfl, hx.1, hfirst⟩⟩
  · have hx' : x ∈ Ico (T.node 0) T.endpoint := ⟨(lt_of_not_ge hfirst).le, hx.2⟩
    rw [← deepTail_iUnion_closed_edges hT] at hx'
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx'
    exact ⟨n, Or.inr hn⟩

theorem outer_tail_initialResistance_nonneg {T : DeepTailData}
    (hT : DeepTailHypotheses T) : 0 ≤ tailInitialResistance T := by
  rcases hT.2.2.2.1 with heq | hgap
  · simp only [tailInitialResistance, heq, intervalIntegral.integral_same, le_refl]
  · exact (tailInitialResistance_pos hT hgap.1).le

def outerTailPointWeight (T : DeepTailData) (n : ℕ) : ℝ :=
  tailFundamentalGreenBlockWeight T n + tailInitialResistance T

theorem outerTailPointWeight_one_le {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) : 1 ≤ outerTailPointWeight T n :=
  (tailFundamentalGreenBlockWeight_one_le hT n).trans
    (le_add_of_nonneg_right (outer_tail_initialResistance_nonneg hT))

theorem outer_tail_decay_product_nonneg {T : DeepTailData}
    (hT : DeepTailHypotheses T) (m n : ℕ) :
    0 ≤ ∏ k ∈ Finset.Ico m n, 8 / (T.Λ * tailMass T (k + 1) * tailResistance T k) :=
  Finset.prod_nonneg fun k _ => div_nonneg (by norm_num)
    (mul_pos (mul_pos hT.2.2.1 (tailMass_pos hT (k + 1))) (tailResistance_pos hT k)).le

theorem MorsePhysicalTailBasis.log_point_kernel_product
    {M : MorseChainData} {D : ReferenceData} {right : Bool} {j start : ℕ}
    {entrance η K : ℝ}
    (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K) {m n : ℕ} (hmn : m ≤ n) {x y : ℝ}
    (hx : OuterTailPoint (morsePhysicalDeepTail M D right j start entrance η K) m x)
    (hy : OuterTailPoint (morsePhysicalDeepTail M D right j start entrance η K) n y) :
    let T := morsePhysicalDeepTail M D right j start entrance η K
    |F.logQ (min x y) * F.logP (max x y)| ≤
      144 * outerTailPointWeight T m *
        ∏ k ∈ Finset.Ico m n, 8 / (T.Λ * tailMass T (k + 1) * tailResistance T k) := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  have hR := outer_tail_initialResistance_nonneg hT
  have hweight (k : ℕ) : tailFundamentalGreenBlockWeight T k ≤ outerTailPointWeight T k :=
    le_add_of_nonneg_right hR
  have h64 (k : ℕ) :
      64 * tailFundamentalGreenBlockWeight T k ≤ 144 * outerTailPointWeight T k := by
    have hp := tailFundamentalGreenBlockWeight_one_le hT k
    dsimp only [outerTailPointWeight]
    nlinarith only [hp, hR]
  have hmix (k : ℕ) {s t : ℝ} (hs : s ∈ Icc T.entrance (T.node 0))
      (ht : t ∈ Icc (T.node k) (T.node (k + 1))) :
      |F.logQ (min s t) * F.logP (max s t)| ≤
        144 * outerTailPointWeight T 0 *
          ∏ l ∈ Finset.Ico 0 k, 8 / (T.Λ * tailMass T (l + 1) * tailResistance T l) :=
    (F.log_initial_edge_kernel_bound hT hη hK k hs ht).trans
      (mul_le_mul_of_nonneg_right (h64 0) (outer_tail_decay_product_nonneg hT 0 k))
  rcases hx with ⟨rfl, hx⟩ | hx
  · rcases hy with ⟨rfl, hy⟩ | hy
    · have h := F.log_initial_kernel_bound hT hη hK hx hy
      have hp := tailFundamentalGreenBlockWeight_one_le hT 0
      simp only [Finset.Ico_self, Finset.prod_empty, mul_one]
      dsimp only [outerTailPointWeight]
      nlinarith only [h, hp, hR]
    · exact hmix n hx hy
  · rcases hy with ⟨hn, hy⟩ | hy
    · have hm : m = 0 := by omega
      subst m
      subst n
      simpa only [min_comm, max_comm] using hmix 0 hy hx
    · exact (outer_tail_kernel_product_bound hT hη hK F.P_log_system F.Q_log_system
        F.log_wronskian (F.log_node_green_bound hT hη hK) hmn hx hy).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hweight m) (by norm_num))
          (outer_tail_decay_product_nonneg hT m n))

/-- The initial-interval convention preserves the full cubic difference. -/
theorem MorsePhysicalTailBasis.log_point_kernel_envelope
    {M : MorseChainData} {D : ReferenceData} {right : Bool} {j start : ℕ}
    {entrance η K : ℝ}
    (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K) {C : ℝ} (hC : 0 ≤ C)
    (hden : ∀ k, exp (2 * ((start + k : ℕ) : ℝ) ^ 2 -
      C * (((start + k : ℕ) : ℝ) ^ (3 / 2 : ℝ) + (start + k : ℕ))) ≤
        (morsePhysicalDeepTail M D right j start entrance η K).Λ *
          tailMass (morsePhysicalDeepTail M D right j start entrance η K) (k + 1) *
          tailResistance (morsePhysicalDeepTail M D right j start entrance η K) k)
    {m n : ℕ} (hmn : m ≤ n) {x y : ℝ}
    (hx : OuterTailPoint (morsePhysicalDeepTail M D right j start entrance η K) m x)
    (hy : OuterTailPoint (morsePhysicalDeepTail M D right j start entrance η K) n y) :
    let T := morsePhysicalDeepTail M D right j start entrance η K
    |F.logQ (min x y) * F.logP (max x y)| ≤
      144 * outerTailPointWeight T m *
        (radialE (start + n) ^ outerPhysicalDecayCost C *
          exp (-|radialS (start + n) - radialS (start + m)|)) := by
  apply (F.log_point_kernel_product hT hη hK hmn hx hy).trans
  exact mul_le_mul_of_nonneg_left
    (outer_physical_decay_product_envelope hC start hden hmn)
    (mul_nonneg (by norm_num) (zero_le_one.trans (outerTailPointWeight_one_le hT m)))

end ContinuousFlexibility.Radial
