module

public import ContinuousFlexibility.Radial.MorseChainRadiusPlacement

/-!
# Local gluing on the actual outward partition

The half-open index selects exactly one piece. At every common boundary
the adjacent pieces agree on a neighborhood, so the actual glued
function agrees there with either piece. This is a local construction
below the finite accumulation radius, before the separate flatness proof.
-/

@[expose] public section

namespace ContinuousFlexibility.Radial

open Filter Set
open scoped ContDiff Topology

/-- Split two smooth germs at an actual finite cut. -/
noncomputable def morseGlueCut (c : ℝ) (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ c then f x else g x

theorem morseGlueCut_eventually_left {c x : ℝ} {f g : ℝ → ℝ}
    (hfg : f =ᶠ[𝓝 c] g) (hx : x ≤ c) :
    morseGlueCut c f g =ᶠ[𝓝 x] f := by
  rcases lt_or_eq_of_le hx with h | heq
  · filter_upwards [Iio_mem_nhds h] with y hy
    exact ite_eq_left (mem_Iio.mp hy).le
  · subst x
    filter_upwards [hfg] with y he
    by_cases hy : y ≤ c
    · exact ite_eq_left hy
    · exact (ite_eq_right hy).trans he.symm

theorem morseGlueCut_eventually_right {c x : ℝ} {f g : ℝ → ℝ}
    (hfg : f =ᶠ[𝓝 c] g) (hx : c ≤ x) :
    morseGlueCut c f g =ᶠ[𝓝 x] g := by
  rcases lt_or_eq_of_le hx with h | he
  · filter_upwards [Ioi_mem_nhds h] with y hy
    exact ite_eq_right (not_le_of_gt (mem_Ioi.mp hy))
  · subst x
    exact (morseGlueCut_eventually_left hfg le_rfl).trans hfg

theorem contDiff_morseGlueCut {c : ℝ} {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hfg : f =ᶠ[𝓝 c] g) :
    ContDiff ℝ ∞ (morseGlueCut c f g) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  rcases le_total x c with h | h
  · exact hf.contDiffAt.congr_of_eventuallyEq (morseGlueCut_eventually_left hfg h)
  · exact hg.contDiffAt.congr_of_eventuallyEq (morseGlueCut_eventually_right hfg h)

/-- Select the actual half-open outward block, continue the first smooth
piece inward, and use zero on the exterior of the accumulating end. -/
noncomputable def morseOutwardGlue (enter : ℕ → ℝ) (piece : ℕ → ℝ → ℝ) (x : ℝ) : ℝ := by
  classical
  exact if x < enter 0 then piece 0 x else
    if h : ∃ n, x ∈ Ico (enter n) (enter (n + 1)) then piece (Classical.choose h) x else 0

private theorem morse_outward_block_index_unique {enter : ℕ → ℝ} (hmono : StrictMono enter)
    {m n : ℕ} {x : ℝ} (hm : x ∈ Ico (enter m) (enter (m + 1)))
    (hn : x ∈ Ico (enter n) (enter (n + 1))) : m = n := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact (not_lt_of_ge ((hmono.monotone (Nat.succ_le_of_lt h)).trans hn.1)) hm.2
  · exact (not_lt_of_ge ((hmono.monotone (Nat.succ_le_of_lt h)).trans hm.1)) hn.2

theorem morse_outward_block_exists {enter : ℕ → ℝ} {endpoint x : ℝ}
    (hLim : Tendsto enter atTop (𝓝 endpoint)) (hx₀ : enter 0 ≤ x) (hx : x < endpoint) :
    ∃ n, x ∈ Ico (enter n) (enter (n + 1)) := by
  classical
  have hex : ∃ n, x < enter n :=
    (hLim.eventually (Ioi_mem_nhds hx)).exists
  have hfirst : x < enter (Nat.find hex) := Nat.find_spec hex
  have hn : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at hfirst
    exact (not_lt_of_ge hx₀) hfirst
  obtain ⟨n, hn'⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [hn'] at hfirst
  refine ⟨n, ⟨le_of_not_gt (Nat.find_min hex ?_), hfirst⟩⟩
  rw [hn']
  exact Nat.lt_succ_self n

theorem morseOutwardGlue_apply_block {enter : ℕ → ℝ} {piece : ℕ → ℝ → ℝ}
    (hmono : StrictMono enter) {n : ℕ} {x : ℝ} (hx : x ∈ Ico (enter n) (enter (n + 1))) :
    morseOutwardGlue enter piece x = piece n x := by
  classical
  have hHead : ¬ x < enter 0 := not_lt_of_ge ((hmono.monotone (Nat.zero_le n)).trans hx.1)
  let h : ∃ k, x ∈ Ico (enter k) (enter (k + 1)) := ⟨n, hx⟩
  unfold morseOutwardGlue
  rw [ite_eq_right hHead, dite_eq_left h]
  rw [morse_outward_block_index_unique hmono (Classical.choose_spec h) hx]

private theorem morseOutwardGlue_apply_inward {enter : ℕ → ℝ} {piece : ℕ → ℝ → ℝ}
    {x : ℝ} (hx : x < enter 0) : morseOutwardGlue enter piece x = piece 0 x := by
  simp only [morseOutwardGlue, ite_eq_left hx]

/-- The glued function has the full actual germ of each piece throughout
its closed block, including both boundaries. -/
theorem morseOutwardGlue_eventually_piece {enter : ℕ → ℝ} {piece : ℕ → ℝ → ℝ}
    (hmono : StrictMono enter)
    (hmatch : ∀ n, piece n =ᶠ[𝓝 (enter (n + 1))] piece (n + 1))
    {n : ℕ} {x : ℝ} (hx : x ∈ Icc (enter n) (enter (n + 1))) :
    morseOutwardGlue enter piece =ᶠ[𝓝 x] piece n := by
  rcases eq_or_lt_of_le hx.1 with he | hlo
  · subst x
    cases n with
    | zero =>
        have h0 := hmono (Nat.lt_succ_self 0)
        filter_upwards [Iio_mem_nhds h0] with y hy
        by_cases h : y < enter 0
        · exact morseOutwardGlue_apply_inward h
        · exact morseOutwardGlue_apply_block hmono ⟨le_of_not_gt h, hy⟩
    | succ n =>
        have h0 : enter n < enter (n + 1) := hmono (Nat.lt_succ_self n)
        have h1 : enter (n + 1) < enter (n + 1 + 1) := hmono (Nat.lt_succ_self (n + 1))
        filter_upwards [Ioo_mem_nhds h0 h1, hmatch n] with y hy hg
        by_cases h : y < enter (n + 1)
        · exact (morseOutwardGlue_apply_block hmono ⟨hy.1.le, h⟩).trans hg
        · exact morseOutwardGlue_apply_block hmono ⟨le_of_not_gt h, hy.2⟩
  · rcases eq_or_lt_of_le hx.2 with he | hhi
    · subst x
      have h0 : enter n < enter (n + 1) := hmono (Nat.lt_succ_self n)
      have h1 : enter (n + 1) < enter (n + 1 + 1) := hmono (Nat.lt_succ_self (n + 1))
      filter_upwards [Ioo_mem_nhds h0 h1, hmatch n] with y hy hg
      by_cases h : y < enter (n + 1)
      · exact morseOutwardGlue_apply_block hmono ⟨hy.1.le, h⟩
      · exact (morseOutwardGlue_apply_block hmono ⟨le_of_not_gt h, hy.2⟩).trans hg.symm
    · filter_upwards [Ioo_mem_nhds hlo hhi] with y hy
      exact morseOutwardGlue_apply_block hmono ⟨hy.1.le, hy.2⟩

theorem morseOutwardGlue_iteratedDeriv_eq {enter : ℕ → ℝ} {piece : ℕ → ℝ → ℝ}
    (hmono : StrictMono enter)
    (hmatch : ∀ n, piece n =ᶠ[𝓝 (enter (n + 1))] piece (n + 1))
    {n : ℕ} {x : ℝ} (hx : x ∈ Icc (enter n) (enter (n + 1))) (k : ℕ) :
    iteratedDeriv k (morseOutwardGlue enter piece) x = iteratedDeriv k (piece n) x :=
  (morseOutwardGlue_eventually_piece hmono hmatch hx).iteratedDeriv_eq k

theorem morseOutwardGlue_eq_zero_of_le {enter : ℕ → ℝ} {piece : ℕ → ℝ → ℝ}
    {endpoint x : ℝ} (hmono : StrictMono enter) (hLim : Tendsto enter atTop (𝓝 endpoint))
    (hx : endpoint ≤ x) : morseOutwardGlue enter piece x = 0 := by
  have hbound (n : ℕ) : enter n ≤ endpoint := by
    apply ge_of_tendsto hLim
    filter_upwards [eventually_ge_atTop n] with k hk
    exact hmono.monotone hk
  have hHead : ¬ x < enter 0 := not_lt_of_ge ((hbound 0).trans hx)
  have hNone : ¬ ∃ n, x ∈ Ico (enter n) (enter (n + 1)) := by
    rintro ⟨n, hn⟩
    exact (not_lt_of_ge ((hbound (n + 1)).trans hx)) hn.2
  simp only [morseOutwardGlue, ite_eq_right hHead, dite_eq_right hNone]

/-- The actual accumulating profile is smooth at every interior point;
no claim at the endpoint is made without derivative decay. -/
theorem contDiffOn_morseOutwardGlue {enter : ℕ → ℝ} {piece : ℕ → ℝ → ℝ} {endpoint : ℝ}
    (hmono : StrictMono enter) (hLim : Tendsto enter atTop (𝓝 endpoint))
    (hpiece : ∀ n, ContDiff ℝ ∞ (piece n))
    (hmatch : ∀ n, piece n =ᶠ[𝓝 (enter (n + 1))] piece (n + 1)) :
    ContDiffOn ℝ ∞ (morseOutwardGlue enter piece) (Iio endpoint) := by
  intro x hx
  by_cases h : x < enter 0
  · have he : morseOutwardGlue enter piece =ᶠ[𝓝 x] piece 0 := by
      filter_upwards [Iio_mem_nhds h] with y hy
      exact morseOutwardGlue_apply_inward hy
    exact ((hpiece 0).contDiffAt.congr_of_eventuallyEq he).contDiffWithinAt
  · obtain ⟨n, hn⟩ := morse_outward_block_exists hLim (le_of_not_gt h) hx
    have he := morseOutwardGlue_eventually_piece hmono hmatch
      (show x ∈ Icc (enter n) (enter (n + 1)) from ⟨hn.1, hn.2.le⟩)
    exact ((hpiece n).contDiffAt.congr_of_eventuallyEq he).contDiffWithinAt

/-- The local gluing theorem for alternating real model cells and joins.
A model and its following join determine one block; the common germs
make the countable construction independent of the endpoint convention. -/
theorem exists_morseOutwardGlue_models_joins {enter leave : ℕ → ℝ}
    {model join : ℕ → ℝ → ℝ} {endpoint : ℝ}
    (hmono : StrictMono enter) (hLim : Tendsto enter atTop (𝓝 endpoint))
    (horder : ∀ n, enter n < leave n ∧ leave n < enter (n + 1))
    (hmodel : ∀ n, ContDiff ℝ ∞ (model n)) (hjoin : ∀ n, ContDiff ℝ ∞ (join n))
    (hmeet : ∀ n, model n =ᶠ[𝓝 (leave n)] join n)
    (hnext : ∀ n, join n =ᶠ[𝓝 (enter (n + 1))] model (n + 1)) :
    ∃ w : ℝ → ℝ, ContDiffOn ℝ ∞ w (Iio endpoint) ∧
      (∀ x, endpoint ≤ x → w x = 0) ∧
      (∀ n, ∀ x ∈ Icc (enter n) (leave n), w =ᶠ[𝓝 x] model n) ∧
      (∀ n, ∀ x ∈ Icc (leave n) (enter (n + 1)), w =ᶠ[𝓝 x] join n) := by
  let piece (n : ℕ) := morseGlueCut (leave n) (model n) (join n)
  have hP (n : ℕ) : ContDiff ℝ ∞ (piece n) :=
    contDiff_morseGlueCut (hmodel n) (hjoin n) (hmeet n)
  have hG (n : ℕ) : piece n =ᶠ[𝓝 (enter (n + 1))] piece (n + 1) :=
    (morseGlueCut_eventually_right (hmeet n) (horder n).2.le).trans
      ((hnext n).trans (morseGlueCut_eventually_left (hmeet (n + 1)) (horder (n + 1)).1.le).symm)
  refine ⟨morseOutwardGlue enter piece, contDiffOn_morseOutwardGlue hmono hLim hP hG,
    fun x hx => morseOutwardGlue_eq_zero_of_le hmono hLim hx, ?_, ?_⟩
  · intro n x hx
    exact (morseOutwardGlue_eventually_piece hmono hG
      ⟨hx.1, hx.2.trans (horder n).2.le⟩).trans (morseGlueCut_eventually_left (hmeet n) hx.2)
  · intro n x hx
    exact (morseOutwardGlue_eventually_piece hmono hG
      ⟨(horder n).1.le.trans hx.1, hx.2⟩).trans (morseGlueCut_eventually_right (hmeet n) hx.1)

end ContinuousFlexibility.Radial
