module

public import ContinuousFlexibility.Radial.MorseChainEndpointDistances
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Data.Set.Card

/-!
# Genuine overlapping localizers for accumulating Morse cells

The transition at a seam lies in a small interval on both sides of it.
The differences of successive smooth steps form the actual partition
on the outward half, with at most two nonzero terms at any point.
-/

@[expose] public section

namespace ContinuousFlexibility.Radial

open Filter Real Set
open scoped BigOperators ContDiff Topology

noncomputable def morseSeamStep (s h : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  smoothTransition ((x - (s n - h n)) / (2 * h n))

noncomputable def morseSeamLocalizer (s h : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  morseSeamStep s h n x - morseSeamStep s h (n + 1) x

theorem contDiff_morseSeamStep (s h : ℕ → ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (morseSeamStep s h n) :=
  smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem contDiff_morseSeamLocalizer (s h : ℕ → ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (morseSeamLocalizer s h n) :=
  (contDiff_morseSeamStep s h n).sub (contDiff_morseSeamStep s h (n + 1))

theorem morseSeamStep_zero {s h : ℕ → ℝ} {n : ℕ} {x : ℝ}
    (hh : 0 < h n) (hx : x ≤ s n - h n) :
    morseSeamStep s h n x = 0 :=
  smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (by positivity))

theorem morseSeamStep_one {s h : ℕ → ℝ} {n : ℕ} {x : ℝ}
    (hh : 0 < h n) (hx : s n + h n ≤ x) :
    morseSeamStep s h n x = 1 := by
  apply smoothTransition.one_of_one_le
  apply (le_div_iff₀ (by positivity : 0 < 2 * h n)).mpr
  linarith only [hx]

theorem morseSeamLocalizer_nonneg {s h : ℕ → ℝ}
    (hh : ∀ n, 0 < h n) (hsep : ∀ n, s n + h n < s (n + 1) - h (n + 1))
    (n : ℕ) (x : ℝ) : 0 ≤ morseSeamLocalizer s h n x := by
  unfold morseSeamLocalizer
  by_cases hx : x ≤ s (n + 1) - h (n + 1)
  · rw [morseSeamStep_zero (hh (n + 1)) hx, sub_zero]
    exact smoothTransition.nonneg _
  · rw [morseSeamStep_one (hh n) ((hsep n).le.trans (le_of_lt (lt_of_not_ge hx)))]
    exact sub_nonneg.mpr (smoothTransition.le_one _)

theorem morseSeamLocalizer_support {s h : ℕ → ℝ}
    (hh : ∀ n, 0 < h n) (hsep : ∀ n, s n + h n < s (n + 1) - h (n + 1)) (n : ℕ) :
    Function.support (morseSeamLocalizer s h n) ⊆ Ioo (s n - h n) (s (n + 1) + h (n + 1)) := by
  intro x hx
  constructor
  · apply lt_of_not_ge
    intro hxL
    apply hx
    unfold morseSeamLocalizer
    have h' : x ≤ s (n + 1) - h (n + 1) := by linarith only [hxL, hh n, hsep n]
    rw [morseSeamStep_zero (hh n) hxL, morseSeamStep_zero (hh (n + 1)) h', sub_self]
  · apply lt_of_not_ge
    intro hxR
    apply hx
    unfold morseSeamLocalizer
    have h' : s n + h n ≤ x := by linarith only [hxR, hh (n + 1), hsep n]
    rw [morseSeamStep_one (hh n) h', morseSeamStep_one (hh (n + 1)) hxR, sub_self]

theorem morseSeamLocalizer_one {s h : ℕ → ℝ}
    (hh : ∀ n, 0 < h n) {n : ℕ} {x : ℝ}
    (hx : x ∈ Icc (s n + h n) (s (n + 1) - h (n + 1))) :
    morseSeamLocalizer s h n x = 1 := by
  unfold morseSeamLocalizer
  rw [morseSeamStep_one (hh n) hx.1, morseSeamStep_zero (hh (n + 1)) hx.2, sub_zero]

/-- Exactly the neighboring windows may contribute to an outward point. -/
theorem morseSeamLocalizer_finite_overlap {s h : ℕ → ℝ}
    (hh : ∀ n, 0 < h n) (hsep : ∀ n, s n + h n < s (n + 1) - h (n + 1)) (x : ℝ) :
    let U := {n : ℕ | morseSeamLocalizer s h n x ≠ 0}
    U.Finite ∧ U.ncard ≤ 2 := by
  classical
  let U := {n : ℕ | morseSeamLocalizer s h n x ≠ 0}
  change U.Finite ∧ U.ncard ≤ 2
  by_cases he : ∃ n, morseSeamLocalizer s h n x ≠ 0
  · let k := Nat.find he
    have hk : x ∈ Ioo (s k - h k) (s (k + 1) + h (k + 1)) :=
      morseSeamLocalizer_support hh hsep k (Nat.find_spec he)
    have hmono : Monotone (fun n => s n - h n) :=
      monotone_nat_of_le_succ (fun n => by linarith only [hh n, hsep n])
    have hSub : U ⊆ ({k, k + 1} : Set ℕ) := by
      intro n hn
      have hkn : k ≤ n := Nat.find_min' he hn
      have hn' := morseSeamLocalizer_support hh hsep n hn
      have hnk : n ≤ k + 1 := by
        by_contra h
        have h₂ : k + 1 + 1 ≤ n := by omega
        have h₃ := hmono h₂
        linarith only [hk.2, hn'.1, hsep (k + 1), h₃]
      have hnEq : n = k ∨ n = k + 1 := by omega
      simpa only [mem_insert_iff, mem_singleton_iff] using hnEq
    have hF : ({k, k + 1} : Set ℕ).Finite := (finite_singleton (k + 1)).insert k
    refine ⟨hF.subset hSub, (ncard_le_ncard hSub hF).trans ?_⟩
    rw [ncard_pair (by omega : k ≠ k + 1)]
  · have hU : U = ∅ := by
      ext n
      simp only [U, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h => he ⟨n, h⟩
    simp [hU]

private theorem morseSeamLocalizer_sum_range (s h : ℕ → ℝ) (x : ℝ) (k : ℕ) :
    (∑ n ∈ Finset.range k, morseSeamLocalizer s h n x) =
      morseSeamStep s h 0 x - morseSeamStep s h k x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      unfold morseSeamLocalizer
      ring

/-- Below the accumulation point, the actual series of localizers sums
to the first smooth step. That step is complemented by the middle piece
when two outward partitions are used. -/
theorem morseSeamLocalizer_tsum {s h : ℕ → ℝ} {endpoint : ℝ}
    (hh : ∀ n, 0 < h n) (hsep : ∀ n, s n + h n < s (n + 1) - h (n + 1))
    (hL : Tendsto (fun n => s n - h n) atTop (𝓝 endpoint))
    {x : ℝ} (hx : x < endpoint) :
    Summable (fun n => morseSeamLocalizer s h n x) ∧
      (∑' n, morseSeamLocalizer s h n x) = morseSeamStep s h 0 x := by
  have hF := (morseSeamLocalizer_finite_overlap hh hsep x).1
  have hS : Summable (fun n => morseSeamLocalizer s h n x) := summable_of_hasFiniteSupport hF
  have he : (fun _ : ℕ => morseSeamStep s h 0 x) =ᶠ[atTop]
      (fun k => ∑ n ∈ Finset.range k, morseSeamLocalizer s h n x) := by
    filter_upwards [hL.eventually (Ioi_mem_nhds hx)] with k hk
    rw [morseSeamLocalizer_sum_range, morseSeamStep_zero (hh k) (mem_Ioi.mp hk).le, sub_zero]
  exact ⟨hS, tendsto_nhds_unique hS.hasSum.tendsto_sum_nat (tendsto_const_nhds.congr' he)⟩

/-- At the first seam the neighboring inward span is the middle interval. -/
noncomputable def morseSeamPrevSpan (s : ℕ → ℝ) (middle : ℝ) : ℕ → ℝ
  | 0 => middle
  | n + 1 => s (n + 1) - s n

/-- The collar is one sixteenth of the least of the distances to both
ends and the two adjacent block lengths. -/
noncomputable def morseSeamWidth (a b middle : ℝ) (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  min (min (s n - a) (b - s n))
    (min (morseSeamPrevSpan s middle n) (s (n + 1) - s n)) / 16

theorem morseSeamWidth_bounds {a b middle : ℝ} {s : ℕ → ℝ}
    (hm : 0 < middle) (hs : StrictMono s) (hcore : ∀ n, s n ∈ Ioo a b) (n : ℕ) :
    let h := morseSeamWidth a b middle s n
    0 < h ∧ h ≤ (s n - a) / 16 ∧ h ≤ (b - s n) / 16 ∧
      h ≤ morseSeamPrevSpan s middle n / 16 ∧ h ≤ (s (n + 1) - s n) / 16 := by
  have hp : 0 < morseSeamPrevSpan s middle n := by
    cases n with
    | zero => exact hm
    | succ n => exact sub_pos.mpr (hs (Nat.lt_succ_self n))
  have hn : 0 < s (n + 1) - s n := sub_pos.mpr (hs (Nat.lt_succ_self n))
  have hL : 0 < s n - a := sub_pos.mpr (hcore n).1
  have hR : 0 < b - s n := sub_pos.mpr (hcore n).2
  refine ⟨div_pos (lt_min (lt_min hL hR) (lt_min hp hn)) (by norm_num), ?_, ?_, ?_, ?_⟩
  · exact div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _)) (by norm_num)
  · exact div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_right _ _)) (by norm_num)
  · exact div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num)
  · exact div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)

noncomputable def morseSeamWindow (s h : ℕ → ℝ) (n : ℕ) : Set ℝ :=
  Ioo (s n - h n) (s (n + 1) + h (n + 1))

noncomputable def morseSeamTraceCenter (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  (s n + s (n + 1)) / 2

noncomputable def morseSeamTraceWidth (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  (s (n + 1) - s n) / 8

/-- The actual small overlaps stay inside the core, preserve both end
distances, and contain separated intervals on which the localizer is one. -/
theorem morseSeamOverlap_geometry {a b middle : ℝ} {s : ℕ → ℝ}
    (hm : 0 < middle) (hs : StrictMono s) (hcore : ∀ n, s n ∈ Ioo a b)
    (hLim : Tendsto s atTop (𝓝 b)) :
    let h := morseSeamWidth a b middle s
    (∀ n, 0 < h n) ∧
    (∀ n, s n + h n < s (n + 1) - h (n + 1)) ∧
    (∀ n, Icc (s n) (s (n + 1)) ⊆ morseSeamWindow s h n) ∧
    (∀ n, morseSeamWindow s h n ⊆ Ioo a b) ∧
    (∀ n, s (n + 1) + h (n + 1) - (s n - h n) ≤ (9 / 8 : ℝ) * (s (n + 1) - s n)) ∧
    (∀ n x, x ∈ morseSeamWindow s h n →
      (15 / 16 : ℝ) * (s n - a) ≤ x - a ∧ x - a ≤ (17 / 16 : ℝ) * (s (n + 1) - a) ∧
      (15 / 16 : ℝ) * (b - s (n + 1)) ≤ b - x ∧ b - x ≤ (17 / 16 : ℝ) * (b - s n)) ∧
    (∀ n x, x ∈ Icc (morseSeamTraceCenter s n - morseSeamTraceWidth s n)
        (morseSeamTraceCenter s n + morseSeamTraceWidth s n) →
      x ∈ morseSeamWindow s h n ∧ morseSeamLocalizer s h n x = 1) ∧
    (∀ n, 0 < morseSeamTraceWidth s n) ∧
    Pairwise (fun m n : ℕ => Disjoint
      (Ioo (morseSeamTraceCenter s m - morseSeamTraceWidth s m)
        (morseSeamTraceCenter s m + morseSeamTraceWidth s m))
      (Ioo (morseSeamTraceCenter s n - morseSeamTraceWidth s n)
        (morseSeamTraceCenter s n + morseSeamTraceWidth s n))) ∧
    Tendsto (fun n => s n - h n) atTop (𝓝 b) := by
  let h := morseSeamWidth a b middle s
  have hh (n : ℕ) : 0 < h n := (morseSeamWidth_bounds hm hs hcore n).1
  have hL (n : ℕ) : h n ≤ (s n - a) / 16 := (morseSeamWidth_bounds hm hs hcore n).2.1
  have hR (n : ℕ) : h n ≤ (b - s n) / 16 := (morseSeamWidth_bounds hm hs hcore n).2.2.1
  have hOut (n : ℕ) : h n ≤ (s (n + 1) - s n) / 16 := (morseSeamWidth_bounds hm hs hcore n).2.2.2.2
  have hIn (n : ℕ) : h (n + 1) ≤ (s (n + 1) - s n) / 16 :=
    (morseSeamWidth_bounds hm hs hcore (n + 1)).2.2.2.1
  have hgap (n : ℕ) : 0 < s (n + 1) - s n := sub_pos.mpr (hs (Nat.lt_succ_self n))
  have hsep (n : ℕ) : s n + h n < s (n + 1) - h (n + 1) := by
    linarith only [hOut n, hIn n, hgap n]
  have hTrace (n : ℕ) : Icc (morseSeamTraceCenter s n - morseSeamTraceWidth s n)
      (morseSeamTraceCenter s n + morseSeamTraceWidth s n) ⊆
      Icc (s n + h n) (s (n + 1) - h (n + 1)) := by
    intro x hx
    change (s n + s (n + 1)) / 2 - (s (n + 1) - s n) / 8 ≤ x ∧
      x ≤ (s n + s (n + 1)) / 2 + (s (n + 1) - s n) / 8 at hx
    exact ⟨by linarith only [hx.1, hOut n, hgap n],
      by linarith only [hx.2, hIn n, hgap n]⟩
  have hTraceInside (n : ℕ) : Ioo (morseSeamTraceCenter s n - morseSeamTraceWidth s n)
      (morseSeamTraceCenter s n + morseSeamTraceWidth s n) ⊆ Ioo (s n) (s (n + 1)) := by
    intro x hx
    have hxx := hTrace n (Ioo_subset_Icc_self hx)
    exact ⟨by linarith only [hxx.1, hh n], by linarith only [hxx.2, hh (n + 1)]⟩
  refine ⟨hh, hsep, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n x hx
    exact ⟨by linarith only [hx.1, hh n], by linarith only [hx.2, hh (n + 1)]⟩
  · intro n x hx
    have hx' : x ∈ Ioo (s n - h n) (s (n + 1) + h (n + 1)) := hx
    exact ⟨by linarith only [hx'.1, hL n, (hcore n).1],
      by linarith only [hx'.2, hR (n + 1), (hcore (n + 1)).2]⟩
  · intro n
    linarith only [hOut n, hIn n]
  · intro n x hx
    have hx' : x ∈ Ioo (s n - h n) (s (n + 1) + h (n + 1)) := hx
    exact ⟨by linarith only [hx'.1, hL n],
      by linarith only [hx'.2, hL (n + 1)],
      by linarith only [hx'.2, hR (n + 1)],
      by linarith only [hx'.1, hR n]⟩
  · intro n x hx
    have hxx := hTrace n hx
    exact ⟨⟨by linarith only [hxx.1, hh n], by linarith only [hxx.2, hh (n + 1)]⟩,
      morseSeamLocalizer_one hh hxx⟩
  · intro n
    exact div_pos (hgap n) (by norm_num)
  · intro m n hne
    apply disjoint_left.mpr
    intro x hm' hn'
    have hx₁ := hTraceInside m hm'
    have hx₂ := hTraceInside n hn'
    rcases lt_or_gt_of_ne hne with hmn | hnm
    · exact (not_lt_of_ge ((hs.monotone (Nat.succ_le_of_lt hmn)).trans hx₂.1.le)) hx₁.2
    · exact (not_lt_of_ge ((hs.monotone (Nat.succ_le_of_lt hnm)).trans hx₁.1.le)) hx₂.2
  · have hLow : Tendsto (fun n => s n - (b - s n) / 16) atTop (𝓝 b) := by
      simpa only [sub_self, zero_div, sub_zero] using
        hLim.sub (((tendsto_const_nhds (x := b)).sub hLim).div_const (16 : ℝ))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hLow hLim
      (fun n => sub_le_sub_left (hR n) _) (fun n => sub_le_self _ (hh n).le)

/-- The middle localizer is the actual remainder after the two outward
half-partitions. Its support crosses each of the two entrance seams. -/
noncomputable def morseMiddleLocalizer (sL hL sR hR : ℕ → ℝ) (x : ℝ) : ℝ :=
  1 - morseSeamStep sL hL 0 (-x) - morseSeamStep sR hR 0 x

theorem contDiff_morseMiddleLocalizer (sL hL sR hR : ℕ → ℝ) :
    ContDiff ℝ ∞ (morseMiddleLocalizer sL hL sR hR) :=
  (contDiff_const.sub ((contDiff_morseSeamStep sL hL 0).comp contDiff_id.neg)).sub
    (contDiff_morseSeamStep sR hR 0)

theorem morseMiddleLocalizer_nonneg {sL hL sR hR : ℕ → ℝ}
    (hhL : 0 < hL 0) (hhR : 0 < hR 0)
    (hsep : -(sL 0 - hL 0) ≤ sR 0 - hR 0) (x : ℝ) :
    0 ≤ morseMiddleLocalizer sL hL sR hR x := by
  unfold morseMiddleLocalizer
  by_cases hx : x ≤ sR 0 - hR 0
  · rw [morseSeamStep_zero hhR hx, sub_zero]
    exact sub_nonneg.mpr (smoothTransition.le_one _)
  · have hx' : -x ≤ sL 0 - hL 0 := by linarith only [lt_of_not_ge hx, hsep]
    rw [morseSeamStep_zero hhL hx', sub_zero]
    exact sub_nonneg.mpr (smoothTransition.le_one _)

theorem morseMiddleLocalizer_support {sL hL sR hR : ℕ → ℝ}
    (hhL : 0 < hL 0) (hhR : 0 < hR 0)
    (hsep : -(sL 0 - hL 0) ≤ sR 0 - hR 0) :
    Function.support (morseMiddleLocalizer sL hL sR hR) ⊆
      Ioo (-(sL 0 + hL 0)) (sR 0 + hR 0) := by
  intro x hx
  constructor
  · apply lt_of_not_ge
    intro h
    apply hx
    unfold morseMiddleLocalizer
    have hLo : sL 0 + hL 0 ≤ -x := by linarith only [h]
    have hRz : x ≤ sR 0 - hR 0 := by linarith only [h, hhL, hsep]
    rw [morseSeamStep_one hhL hLo, morseSeamStep_zero hhR hRz, sub_self, sub_zero]
  · apply lt_of_not_ge
    intro h
    apply hx
    unfold morseMiddleLocalizer
    have hLz : -x ≤ sL 0 - hL 0 := by linarith only [h, hhR, hsep]
    rw [morseSeamStep_zero hhL hLz, morseSeamStep_one hhR h, sub_zero, sub_self]

/-- On the physical interval the middle localizer and the two outward
families give an actual partition of unity. The left side is reflected;
its indexing and nonnegative terms are retained. -/
theorem morseMiddleLocalizer_add_tsum {a b : ℝ} {sL hL sR hR : ℕ → ℝ}
    (hhL : ∀ n, 0 < hL n) (hhR : ∀ n, 0 < hR n)
    (hsepL : ∀ n, sL n + hL n < sL (n + 1) - hL (n + 1))
    (hsepR : ∀ n, sR n + hR n < sR (n + 1) - hR (n + 1))
    (hLimL : Tendsto (fun n => sL n - hL n) atTop (𝓝 (-a)))
    (hLimR : Tendsto (fun n => sR n - hR n) atTop (𝓝 b))
    {x : ℝ} (hx : x ∈ Ioo a b) :
    Summable (fun n => morseSeamLocalizer sL hL n (-x)) ∧
    Summable (fun n => morseSeamLocalizer sR hR n x) ∧
    morseMiddleLocalizer sL hL sR hR x + (∑' n, morseSeamLocalizer sL hL n (-x)) +
      (∑' n, morseSeamLocalizer sR hR n x) = 1 := by
  obtain ⟨hLs, hLsum⟩ := morseSeamLocalizer_tsum hhL hsepL hLimL (neg_lt_neg hx.1)
  obtain ⟨hRs, hRsum⟩ := morseSeamLocalizer_tsum hhR hsepR hLimR hx.2
  refine ⟨hLs, hRs, ?_⟩
  rw [hLsum, hRsum, morseMiddleLocalizer]
  ring

end ContinuousFlexibility.Radial
