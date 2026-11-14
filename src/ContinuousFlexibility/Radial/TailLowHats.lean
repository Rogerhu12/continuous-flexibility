module

public import ContinuousFlexibility.Radial.TailSmoothResistanceStep
public import ContinuousFlexibility.Radial.TailMassResistanceData
public import ContinuousFlexibility.Radial.TailFormCore

/-!
# Actual smooth low-mode hats on the tail

One chosen smooth resistance step is shared by the two hats incident to
each gap. Consecutive hats are differences of these same steps; their sum
on a gap therefore has the exact affine interpolation formula.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def tailSmoothStepConstant : ℝ := exists_tailSmoothResistanceStep.choose

theorem tailSmoothStepConstant_pos : 0 < tailSmoothStepConstant :=
  exists_tailSmoothResistanceStep.choose_spec.1

/-- All fields describe the displayed function, including its actual
derivative and its actual weighted energy. -/
structure TailSmoothStep (p : ℝ → ℝ) (a b : ℝ) where
  fn : ℝ → ℝ
  smooth : ContDiff ℝ ∞ fn
  range : ∀ x, 0 ≤ fn x ∧ fn x ≤ 1
  left : ∀ x, x ≤ a → fn x = 0
  right : ∀ x, b ≤ x → fn x = 1
  left_germ : fn =ᶠ[𝓝 a] fun _ => 0
  right_germ : fn =ᶠ[𝓝 b] fun _ => 1
  deriv_support : tsupport (deriv fn) ⊆ Ioo a b
  energy : (∫ x in a..b, p x * deriv fn x ^ 2) ≤
    tailSmoothStepConstant / (∫ x in a..b, (p x)⁻¹)

def tailChooseSmoothStep (p : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hp : ContDiffOn ℝ ∞ p (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < p x) :
    TailSmoothStep p a b := by
  have he := exists_tailSmoothResistanceStep.choose_spec.2 p a b hab hp hpos
  exact ⟨he.choose, he.choose_spec.1, he.choose_spec.2.1, he.choose_spec.2.2.1,
    he.choose_spec.2.2.2.1, he.choose_spec.2.2.2.2.1, he.choose_spec.2.2.2.2.2.1,
    he.choose_spec.2.2.2.2.2.2.1, he.choose_spec.2.2.2.2.2.2.2⟩

theorem tail_step_difference_bounds {p : ℝ → ℝ} {a c b d : ℝ}
    (F : TailSmoothStep p a c) (G : TailSmoothStep p b d) (hcb : c ≤ b) (x : ℝ) :
    0 ≤ F.fn x - G.fn x ∧ F.fn x - G.fn x ≤ 1 := by
  have hF := F.range x
  have hG := G.range x
  constructor
  · by_cases hx : x ≤ b
    · rw [G.left x hx, sub_zero]
      exact hF.1
    · rw [F.right x (hcb.trans (le_of_not_ge hx))]
      linarith
  · linarith

theorem tail_step_difference_support {p : ℝ → ℝ} {a c b d : ℝ}
    (F : TailSmoothStep p a c) (G : TailSmoothStep p b d)
    (hac : a < c) (hcb : c ≤ b) (hbd : b < d) :
    tsupport (fun x => F.fn x - G.fn x) ⊆ Ioo a d := by
  have hab : a < b := hac.trans_le hcb
  have hcd : c < d := hcb.trans_lt hbd
  have hleft : (fun x => F.fn x - G.fn x) =ᶠ[𝓝 a] fun _ => (0 : ℝ) := by
    filter_upwards [F.left_germ, Iio_mem_nhds hab] with x hF hx
    rw [hF, G.left x hx.le, sub_self]
  have hright : (fun x => F.fn x - G.fn x) =ᶠ[𝓝 d] fun _ => (0 : ℝ) := by
    filter_upwards [G.right_germ, Ioi_mem_nhds hcd] with x hG hx
    rw [F.right x hx.le, hG, sub_self]
  have hs : Function.support (fun x => F.fn x - G.fn x) ⊆ Icc a d := by
    intro x hx
    constructor
    · by_contra hn
      have hxa := (lt_of_not_ge hn).le
      exact hx (by
        change F.fn x - G.fn x = 0
        rw [F.left x hxa, G.left x (hxa.trans hab.le), sub_self])
    · by_contra hn
      have hdx := (lt_of_not_ge hn).le
      exact hx (by
        change F.fn x - G.fn x = 0
        rw [F.right x (hcd.le.trans hdx), G.right x hdx, sub_self])
  have ht := closure_minimal hs isClosed_Icc
  intro x hx
  have hax := (ht hx).1
  have hxd := (ht hx).2
  constructor
  · apply lt_of_le_of_ne hax
    intro he
    subst x
    exact (notMem_tsupport_iff_eventuallyEq.mpr hleft) hx
  · apply lt_of_le_of_ne hxd
    intro he
    subst x
    exact (notMem_tsupport_iff_eventuallyEq.mpr hright) hx

theorem tail_step_difference_compact {p : ℝ → ℝ} {a c b d : ℝ}
    (F : TailSmoothStep p a c) (G : TailSmoothStep p b d)
    (hac : a < c) (hcb : c ≤ b) (hbd : b < d) :
    HasCompactSupport (fun x => F.fn x - G.fn x) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    ((tail_step_difference_support F G hac hcb hbd).trans Ioo_subset_Icc_self)

private theorem tail_low_segment_smooth {T : DeepTailData} (hT : DeepTailHypotheses T)
    {a b : ℝ} (ha : T.entrance ≤ a) (hb : b < T.endpoint) :
    ContDiffOn ℝ ∞ T.p (Icc a b) := by
  rcases hT with ⟨_, _, _, _, _, _, _, hp, _, _, _⟩
  exact hp.mono (fun x hx => ⟨ha.trans hx.1, hx.2.trans_lt hb⟩)

private theorem tail_low_segment_pos {T : DeepTailData} (hT : DeepTailHypotheses T)
    {a b : ℝ} (ha : T.entrance ≤ a) (hb : b < T.endpoint) :
    ∀ x ∈ Icc a b, 0 < T.p x := by
  rcases hT with ⟨_, _, _, _, _, _, _, _, hp, _, _⟩
  exact fun x hx => hp x ⟨ha.trans hx.1, hx.2.trans_lt hb⟩

def tailGapSmoothStep (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) :
    TailSmoothStep T.p (T.massEnd n) (T.node (n + 1)) :=
  tailChooseSmoothStep T.p _ _ (deepTail_massEnd_lt_succ_node hT n)
    (tail_low_segment_smooth hT
      ((deepTail_entrance_le_node hT n).trans (deepTail_node_lt_massEnd hT n).le)
      (deepTail_node_lt_endpoint hT (n + 1)))
    (tail_low_segment_pos hT
      ((deepTail_entrance_le_node hT n).trans (deepTail_node_lt_massEnd hT n).le)
      (deepTail_node_lt_endpoint hT (n + 1)))

def tailGapStep (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) : ℝ → ℝ :=
  (tailGapSmoothStep T hT n).fn

def tailEntrySmoothStep (T : DeepTailData) (hT : DeepTailHypotheses T)
    (h : T.entrance < T.node 0) : TailSmoothStep T.p T.entrance (T.node 0) :=
  tailChooseSmoothStep T.p _ _ h
    (tail_low_segment_smooth hT le_rfl (deepTail_node_lt_endpoint hT 0))
    (tail_low_segment_pos hT le_rfl (deepTail_node_lt_endpoint hT 0))

def tailEntryStep (T : DeepTailData) (hT : DeepTailHypotheses T) : ℝ → ℝ :=
  if h : T.entrance < T.node 0 then (tailEntrySmoothStep T hT h).fn else 0

def tailLowerStep (T : DeepTailData) (hT : DeepTailHypotheses T) : ℕ → ℝ → ℝ
  | 0 => tailEntryStep T hT
  | n + 1 => tailGapStep T hT n

def tailLowHat (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) : ℝ → ℝ :=
  if tailFirstMassIndex T ≤ n then fun x => tailLowerStep T hT n x - tailGapStep T hT n x
    else 0

theorem tailGapStep_smooth (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) :
    ContDiff ℝ ∞ (tailGapStep T hT n) := (tailGapSmoothStep T hT n).smooth

theorem tailGapStep_range (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) (x : ℝ) :
    0 ≤ tailGapStep T hT n x ∧ tailGapStep T hT n x ≤ 1 := (tailGapSmoothStep T hT n).range x

theorem tailGapStep_left (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ)
    {x : ℝ} (hx : x ≤ T.massEnd n) : tailGapStep T hT n x = 0 :=
  (tailGapSmoothStep T hT n).left x hx

theorem tailGapStep_right (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ)
    {x : ℝ} (hx : T.node (n + 1) ≤ x) : tailGapStep T hT n x = 1 :=
  (tailGapSmoothStep T hT n).right x hx

theorem tailGapStep_energy (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) :
    (∫ x in T.massEnd n..T.node (n + 1), T.p x * deriv (tailGapStep T hT n) x ^ 2) ≤
      tailSmoothStepConstant / tailResistance T n := (tailGapSmoothStep T hT n).energy

theorem tailGapStep_deriv_support (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) :
    tsupport (deriv (tailGapStep T hT n)) ⊆ Ioo (T.massEnd n) (T.node (n + 1)) :=
  (tailGapSmoothStep T hT n).deriv_support

theorem tailEntryStep_range (T : DeepTailData) (hT : DeepTailHypotheses T) (x : ℝ) :
    0 ≤ tailEntryStep T hT x ∧ tailEntryStep T hT x ≤ 1 := by
  unfold tailEntryStep
  split_ifs with h
  · exact (tailEntrySmoothStep T hT h).range x
  · exact ⟨le_rfl, zero_le_one⟩

theorem tailEntryStep_deriv_support (T : DeepTailData) (hT : DeepTailHypotheses T) :
    tsupport (deriv (tailEntryStep T hT)) ⊆ Ioo T.entrance (T.node 0) := by
  unfold tailEntryStep
  split_ifs with h
  · exact (tailEntrySmoothStep T hT h).deriv_support
  · simp only [deriv_zero, tsupport_zero, empty_subset]

theorem tailEntryStep_smooth (T : DeepTailData) (hT : DeepTailHypotheses T) :
    ContDiff ℝ ∞ (tailEntryStep T hT) := by
  unfold tailEntryStep
  split_ifs with h
  · exact (tailEntrySmoothStep T hT h).smooth
  · exact contDiff_const

theorem tailLowHat_smooth (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) :
    ContDiff ℝ ∞ (tailLowHat T hT n) := by
  unfold tailLowHat
  split_ifs
  · apply ContDiff.sub _ (tailGapStep_smooth T hT n)
    cases n with
    | zero => exact tailEntryStep_smooth T hT
    | succ n => exact tailGapStep_smooth T hT n
  · exact contDiff_const

theorem tail_active_zero_entry {T : DeepTailData} (hT : DeepTailHypotheses T)
    (hn : tailFirstMassIndex T ≤ 0) : T.entrance < T.node 0 := by
  by_contra h
  have he : T.node 0 = T.entrance := le_antisymm (le_of_not_gt h) hT.2.1
  rw [tailFirstMassIndex_eq_one he] at hn
  omega

/-- Every active hat is a difference of consecutive steps, with the same
right step that occurs in the following hat. -/
theorem tailLowHat_pair (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ)
    (hn : tailFirstMassIndex T ≤ n) :
    ∃ a : ℝ, ∃ F : TailSmoothStep T.p a (T.node n),
      T.entrance ≤ a ∧ a < T.node n ∧
      tailLowHat T hT n = fun x => F.fn x - tailGapStep T hT n x := by
  cases n with
  | zero =>
    have he := tail_active_zero_entry hT hn
    refine ⟨T.entrance, tailEntrySmoothStep T hT he, le_rfl, he, ?_⟩
    simp only [tailLowHat, if_pos hn, tailLowerStep, tailEntryStep, dif_pos he]
  | succ n =>
    refine ⟨T.massEnd n, tailGapSmoothStep T hT n,
      (deepTail_entrance_le_node hT n).trans (deepTail_node_lt_massEnd hT n).le,
      deepTail_massEnd_lt_succ_node hT n, ?_⟩
    simp only [tailLowHat, if_pos hn, tailLowerStep, tailGapStep]

theorem tailLowHat_range (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) (x : ℝ) :
    0 ≤ tailLowHat T hT n x ∧ tailLowHat T hT n x ≤ 1 := by
  by_cases hn : tailFirstMassIndex T ≤ n
  · obtain ⟨a, F, _, _, he⟩ := tailLowHat_pair T hT n hn
    rw [he]
    exact tail_step_difference_bounds F (tailGapSmoothStep T hT n)
      (deepTail_node_lt_massEnd hT n).le x
  · simp only [tailLowHat, if_neg hn, Pi.zero_apply, le_refl, zero_le_one, and_self]

theorem tailLowHat_support_truncation (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) :
    tsupport (tailLowHat T hT n) ⊆ Ioo T.entrance (T.node (n + 1)) := by
  by_cases hn : tailFirstMassIndex T ≤ n
  · obtain ⟨a, F, ha, han, he⟩ := tailLowHat_pair T hT n hn
    rw [he]
    have hs := tail_step_difference_support F (tailGapSmoothStep T hT n) han
      (deepTail_node_lt_massEnd hT n).le (deepTail_massEnd_lt_succ_node hT n)
    exact hs.trans (fun x hx => ⟨ha.trans_lt hx.1, hx.2⟩)
  · simp only [tailLowHat, if_neg hn, tsupport_zero, empty_subset]

theorem tailLowHat_support (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) :
    tsupport (tailLowHat T hT n) ⊆ Ioo T.entrance T.endpoint :=
  (tailLowHat_support_truncation T hT n).trans (fun x hx =>
    ⟨hx.1, hx.2.trans (deepTail_node_lt_endpoint hT (n + 1))⟩)

theorem tailLowHat_compact (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) :
    HasCompactSupport (tailLowHat T hT n) := by
  by_cases hn : tailFirstMassIndex T ≤ n
  · obtain ⟨a, F, _, han, he⟩ := tailLowHat_pair T hT n hn
    rw [he]
    exact tail_step_difference_compact F (tailGapSmoothStep T hT n) han
      (deepTail_node_lt_massEnd hT n).le (deepTail_massEnd_lt_succ_node hT n)
  · simpa only [tailLowHat, if_neg hn] using
      (HasCompactSupport.zero : HasCompactSupport (0 : ℝ → ℝ))

theorem tail_massEnd_strictMono {T : DeepTailData} (hT : DeepTailHypotheses T) :
    StrictMono T.massEnd :=
  strictMono_nat_of_lt_succ (fun n =>
    (deepTail_massEnd_lt_succ_node hT n).trans (deepTail_node_lt_massEnd hT (n + 1)))

theorem tailGapStep_mass (T : DeepTailData) (hT : DeepTailHypotheses T) (n m : ℕ)
    {x : ℝ} (hx : x ∈ Icc (T.node m) (T.massEnd m)) :
    tailGapStep T hT n x = if n < m then 1 else 0 := by
  by_cases hnm : n < m
  · rw [if_pos hnm]
    exact tailGapStep_right T hT n
      (((deepTail_node_strictMono hT).monotone (Nat.succ_le_of_lt hnm)).trans hx.1)
  · rw [if_neg hnm]
    exact tailGapStep_left T hT n
      (hx.2.trans ((tail_massEnd_strictMono hT).monotone (le_of_not_gt hnm)))

theorem tailLowerStep_mass (T : DeepTailData) (hT : DeepTailHypotheses T) (n m : ℕ)
    (hn : tailFirstMassIndex T ≤ n) {x : ℝ}
    (hx : x ∈ Icc (T.node m) (T.massEnd m)) :
    tailLowerStep T hT n x = if n ≤ m then 1 else 0 := by
  cases n with
  | zero =>
    have he := tail_active_zero_entry hT hn
    simp only [tailLowerStep, tailEntryStep, dif_pos he, Nat.zero_le, if_true]
    exact (tailEntrySmoothStep T hT he).right x
      (((deepTail_node_strictMono hT).monotone (Nat.zero_le m)).trans hx.1)
  | succ n =>
    change tailGapStep T hT n x = if n + 1 ≤ m then 1 else 0
    rw [tailGapStep_mass T hT n m hx]
    simp only [Nat.succ_le_iff]

theorem tailLowHat_mass (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ)
    (hn : tailFirstMassIndex T ≤ n) (m : ℕ) {x : ℝ}
    (hx : x ∈ Icc (T.node m) (T.massEnd m)) :
    tailLowHat T hT n x = if n = m then 1 else 0 := by
  simp only [tailLowHat, if_pos hn]
  rw [tailLowerStep_mass T hT n m hn hx, tailGapStep_mass T hT n m hx]
  split_ifs <;> first | omega | ring

theorem tailGapStep_gap (T : DeepTailData) (hT : DeepTailHypotheses T) (n m : ℕ)
    {x : ℝ} (hx : x ∈ Icc (T.massEnd m) (T.node (m + 1))) :
    tailGapStep T hT n x = if n < m then 1 else
      if n = m then tailGapStep T hT m x else 0 := by
  by_cases hnm : n < m
  · rw [if_pos hnm]
    exact tailGapStep_right T hT n
      ((((deepTail_node_strictMono hT).monotone (Nat.succ_le_of_lt hnm)).trans
        (deepTail_node_lt_massEnd hT m).le).trans hx.1)
  · rw [if_neg hnm]
    by_cases he : n = m
    · subst m
      rw [if_pos rfl]
    · rw [if_neg he]
      have hmn : m < n := by omega
      exact tailGapStep_left T hT n
        (hx.2.trans (((deepTail_node_strictMono hT).monotone
          (Nat.succ_le_of_lt hmn)).trans (deepTail_node_lt_massEnd hT n).le))

theorem tailLowHat_gap (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ)
    (hn : tailFirstMassIndex T ≤ n) (m : ℕ) {x : ℝ}
    (hx : x ∈ Icc (T.massEnd m) (T.node (m + 1))) :
    tailLowHat T hT n x =
      (if n = m then 1 - tailGapStep T hT m x else 0) +
      (if n = m + 1 then tailGapStep T hT m x else 0) := by
  simp only [tailLowHat, if_pos hn]
  cases n with
  | zero =>
    have he := tail_active_zero_entry hT hn
    have hentry : tailLowerStep T hT 0 x = 1 := by
      simp only [tailLowerStep, tailEntryStep, dif_pos he]
      exact (tailEntrySmoothStep T hT he).right x
        ((((deepTail_node_strictMono hT).monotone (Nat.zero_le m)).trans
          (deepTail_node_lt_massEnd hT m).le).trans hx.1)
    rw [hentry, tailGapStep_gap T hT 0 m hx]
    split_ifs <;> first | contradiction | omega | ring
  | succ n =>
    change tailGapStep T hT n x - tailGapStep T hT (n + 1) x = _
    rw [tailGapStep_gap T hT n m hx, tailGapStep_gap T hT (n + 1) m hx]
    split_ifs <;> first | omega | ring

theorem tailLowHat_initial (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ)
    (hn : tailFirstMassIndex T ≤ n) {x : ℝ}
    (hx : x ∈ Icc T.entrance (T.node 0)) :
    tailLowHat T hT n x = if n = 0 then tailEntryStep T hT x else 0 := by
  have hgap (k : ℕ) : tailGapStep T hT k x = 0 :=
    tailGapStep_left T hT k (hx.2.trans
      (((deepTail_node_strictMono hT).monotone (Nat.zero_le k)).trans
        (deepTail_node_lt_massEnd hT k).le))
  simp only [tailLowHat, if_pos hn, hgap]
  cases n with
  | zero => simp only [tailLowerStep, if_true, sub_zero]
  | succ n => simp only [tailLowerStep, hgap, Nat.succ_ne_zero, if_false, sub_self]

theorem tailLowHat_deriv_mass (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ)
    (hn : tailFirstMassIndex T ≤ n) (m : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (T.node m) (T.massEnd m)) : deriv (tailLowHat T hT n) x = 0 := by
  have he : tailLowHat T hT n =ᶠ[𝓝 x] (fun _ => if n = m then (1 : ℝ) else 0) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact tailLowHat_mass T hT n hn m ⟨hy.1.le, hy.2.le⟩
  simpa only [deriv_const] using he.deriv_eq

theorem tailLowHat_deriv_gap (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ)
    (hn : tailFirstMassIndex T ≤ n) (m : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (T.massEnd m) (T.node (m + 1))) :
    deriv (tailLowHat T hT n) x =
      (if n = m then -deriv (tailGapStep T hT m) x else 0) +
      (if n = m + 1 then deriv (tailGapStep T hT m) x else 0) := by
  have he : tailLowHat T hT n =ᶠ[𝓝 x] (fun y =>
      (if n = m then 1 - tailGapStep T hT m y else 0) +
      (if n = m + 1 then tailGapStep T hT m y else 0)) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact tailLowHat_gap T hT n hn m ⟨hy.1.le, hy.2.le⟩
  by_cases hnm : n = m
  · have hnnext : n ≠ m + 1 := by omega
    simp only [if_pos hnm, if_neg hnnext, add_zero] at he ⊢
    rw [he.deriv_eq]
    exact deriv_const_sub (f := tailGapStep T hT m) (1 : ℝ)
  · by_cases hnnext : n = m + 1
    · simp only [if_neg hnm, if_pos hnnext, zero_add] at he ⊢
      exact he.deriv_eq
    · simp only [if_neg hnm, if_neg hnnext, add_zero] at he ⊢
      simpa only [deriv_const] using he.deriv_eq

theorem tailLowHat_deriv_initial (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ)
    (hn : tailFirstMassIndex T ≤ n) {x : ℝ}
    (hx : x ∈ Ioo T.entrance (T.node 0)) :
    deriv (tailLowHat T hT n) x = if n = 0 then deriv (tailEntryStep T hT) x else 0 := by
  have he : tailLowHat T hT n =ᶠ[𝓝 x]
      (fun y => if n = 0 then tailEntryStep T hT y else 0) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact tailLowHat_initial T hT n hn ⟨hy.1.le, hy.2.le⟩
  by_cases hn0 : n = 0
  · simp only [if_pos hn0] at he ⊢
    exact he.deriv_eq
  · simp only [if_neg hn0] at he ⊢
    simpa only [deriv_const] using he.deriv_eq

theorem tailEntryStep_energy (T : DeepTailData) (hT : DeepTailHypotheses T)
    (he : T.entrance < T.node 0) :
    (∫ x in T.entrance..T.node 0, T.p x * deriv (tailEntryStep T hT) x ^ 2) ≤
      tailSmoothStepConstant / tailInitialResistance T := by
  simpa only [tailEntryStep, dif_pos he, tailInitialResistance] using
    (tailEntrySmoothStep T hT he).energy

end ContinuousFlexibility.Radial
