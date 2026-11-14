module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Order.ProjIcc

/-!
# Actual solutions of a linear equation on a finite interval

The local Picard theorem has a time of existence independent of the initial
state for a bounded linear field. Joining finitely many such solutions gives
an actual solution on every compact interval. All derivatives below are
two-sided, including at the joins and the two ends of the requested interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Metric
open scoped NNReal Topology

set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Join two solutions with the same state at their common endpoint. -/
theorem exists_ode_join {F : ℝ → E → E} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    {f g : ℝ → E}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (F t (f t)) t)
    (hg : ∀ t ∈ Icc b c, HasDerivAt g (F t (g t)) t)
    (heq : f b = g b) :
    ∃ u : ℝ → E, EqOn u f (Icc a b) ∧ EqOn u g (Icc b c) ∧
      ∀ t ∈ Icc a c, HasDerivAt u (F t (u t)) t := by
  let u : ℝ → E := fun t => if t ≤ b then f t else g t
  have hleft (t : ℝ) (ht : t ≤ b) : u t = f t := by simp [u, ht]
  have hright (t : ℝ) (ht : b ≤ t) : u t = g t := by
    rcases ht.eq_or_lt with h | h
    · subst t; simp [u, heq]
    · simp [u, not_le.mpr h]
  refine ⟨u, fun t ht => hleft t ht.2, fun t ht => hright t ht.1, ?_⟩
  intro t ht
  rcases lt_trichotomy t b with hlt | he | hgt
  · rw [hleft t hlt.le]
    apply (hf t ⟨ht.1, hlt.le⟩).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hlt] with s hs
    exact hleft s hs.le
  · subst t
    have hl : HasDerivWithinAt u (F b (f b)) (Iic b) b :=
      (hf b ⟨hab, le_rfl⟩).hasDerivWithinAt.congr
        (fun s hs => hleft s hs) (hleft b le_rfl)
    have hr : HasDerivWithinAt u (F b (f b)) (Ici b) b := by
      rw [heq]
      exact (hg b ⟨le_rfl, hbc⟩).hasDerivWithinAt.congr
        (fun s hs => hright s hs) (hright b le_rfl)
    rw [hleft b le_rfl]
    apply (hl.union hr).hasDerivAt
    have hs : Iic b ∪ Ici b = (univ : Set ℝ) := by
      ext s
      simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
      exact le_total s b
    rw [hs]
    exact Filter.univ_mem
  · rw [hright t hgt.le]
    apply (hg t ⟨hgt.le, ht.2⟩).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hgt] with s hs
    exact hright s hs.le

/-- A uniform local time for a bounded continuous linear field. -/
theorem exists_bounded_linear_ode_local (A : ℝ → E →L[ℝ] E) (hA : Continuous A)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) {δ : ℝ} (hδ : 0 < δ)
    (hsmall : 4 * (K : ℝ) * δ ≤ 1) (c : ℝ) (x : E) :
    ∃ f : ℝ → E, f c = x ∧
      ∀ t ∈ Icc (c - δ) (c + δ), HasDerivAt f (A t (f t)) t := by
  let r : ℝ≥0 := ⟨‖x‖ + 1, by positivity⟩
  let c₀ : Icc (c - 2 * δ) (c + 2 * δ) := ⟨c, by constructor <;> linarith⟩
  have hPL : IsPicardLindelof (fun t y => A t y) c₀ x r 0 (2 * K * r) K := by
    constructor
    · intro t _
      apply LipschitzWith.lipschitzOnWith
      apply LipschitzWith.of_dist_le_mul
      intro y z
      rw [dist_eq_norm, dist_eq_norm, ← map_sub]
      exact ((A t).le_opNorm (y - z)).trans
        (mul_le_mul_of_nonneg_right (hK t) (norm_nonneg _))
    · intro y _
      exact (hA.clm_apply continuous_const).continuousOn
    · intro t _ y hy
      have hdist : ‖y - x‖ ≤ (r : ℝ) := by
        simpa only [mem_closedBall, dist_eq_norm] using hy
      have hyn : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
        simpa only [sub_add_cancel] using norm_add_le (y - x) x
      have hxr : ‖x‖ ≤ (r : ℝ) := by
        change ‖x‖ ≤ ‖x‖ + 1
        linarith
      calc
        ‖A t y‖ ≤ (K : ℝ) * ‖y‖ :=
          ((A t).le_opNorm y).trans (mul_le_mul_of_nonneg_right (hK t) (norm_nonneg y))
        _ ≤ (K : ℝ) * (2 * r) := mul_le_mul_of_nonneg_left (by linarith) K.2
        _ = ((2 * K * r : ℝ≥0) : ℝ) := by simp only [NNReal.coe_mul, NNReal.coe_ofNat]; ring
    · have hmax : max (c + 2 * δ - c) (c - (c - 2 * δ)) = 2 * δ := by
        have h₁ : c + 2 * δ - c = 2 * δ := by ring
        have h₂ : c - (c - 2 * δ) = 2 * δ := by ring
        rw [h₁, h₂, max_self]
      change ((2 * K * r : ℝ≥0) : ℝ) *
        max (c + 2 * δ - c) (c - (c - 2 * δ)) ≤ (r : ℝ) - (0 : ℝ≥0)
      rw [hmax]
      simp only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_zero, sub_zero]
      calc
        2 * (K : ℝ) * (r : ℝ) * (2 * δ) = (4 * (K : ℝ) * δ) * (r : ℝ) := by ring
        _ ≤ 1 * (r : ℝ) := mul_le_mul_of_nonneg_right hsmall r.2
        _ = (r : ℝ) := one_mul _
  obtain ⟨f, hfc, hf⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨f, hfc, fun t ht => ?_⟩
  have ht' : t ∈ Icc (c - 2 * δ) (c + 2 * δ) := by
    constructor <;> linarith [ht.1, ht.2]
  exact (hf t ht').hasDerivAt (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))

/-- Finitely many uniform local steps give the forward solution. -/
theorem exists_bounded_linear_ode_steps (A : ℝ → E →L[ℝ] E) (hA : Continuous A)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) {δ : ℝ} (hδ : 0 < δ)
    (hsmall : 4 * (K : ℝ) * δ ≤ 1) (c : ℝ) (x : E) (N : ℕ) :
    ∃ f : ℝ → E, f c = x ∧
      ∀ t ∈ Icc c (c + (N : ℝ) * δ), HasDerivAt f (A t (f t)) t := by
  induction N with
  | zero =>
    obtain ⟨f, hfc, hf⟩ := exists_bounded_linear_ode_local A hA K hK hδ hsmall c x
    refine ⟨f, hfc, fun t ht => hf t ?_⟩
    simp only [Nat.cast_zero, zero_mul, add_zero, mem_Icc] at ht
    constructor <;> linarith [ht.1, ht.2]
  | succ N ih =>
    obtain ⟨f, hfc, hf⟩ := ih
    let b := c + (N : ℝ) * δ
    have hcb : c ≤ b := by
      dsimp [b]
      linarith [mul_nonneg (Nat.cast_nonneg N) hδ.le]
    obtain ⟨g, hgb, hg⟩ :=
      exists_bounded_linear_ode_local A hA K hK hδ hsmall b (f b)
    have hbg : ∀ t ∈ Icc b (b + δ), HasDerivAt g (A t (g t)) t :=
      fun t ht => hg t ⟨by linarith [ht.1], ht.2⟩
    obtain ⟨u, huf, _, hu⟩ := exists_ode_join hcb (by linarith : b ≤ b + δ) hf hbg hgb.symm
    refine ⟨u, (huf ⟨le_rfl, hcb⟩).trans hfc, fun t ht => hu t ?_⟩
    have hend : c + ((N + 1 : ℕ) : ℝ) * δ = b + δ := by
      simp only [Nat.cast_add, Nat.cast_one, b]
      ring
    rwa [← hend]

/-- A bounded continuous linear field has an actual solution through any
initial state on every finite interval. -/
theorem exists_bounded_linear_ode (A : ℝ → E →L[ℝ] E) (hA : Continuous A)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) (a b c : ℝ) (x : E) :
    ∃ f : ℝ → E, f c = x ∧
      ∀ t ∈ Icc a b, HasDerivAt f (A t (f t)) t := by
  let δ : ℝ := (4 * ((K : ℝ) + 1))⁻¹
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : 4 * (K : ℝ) * δ ≤ 1 := by
    dsimp [δ]
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity : 0 < 4 * ((K : ℝ) + 1))]
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((max (c - a) (b - c)) / δ)
  have hspan : max (c - a) (b - c) < (N : ℝ) * δ := (div_lt_iff₀ hδ).mp hN
  obtain ⟨f, hfc, hf⟩ := exists_bounded_linear_ode_steps A hA K hK hδ hsmall c x N
  let B : ℝ → E →L[ℝ] E := fun t => -A (-t)
  have hB : Continuous B := (hA.comp continuous_neg).neg
  have hBK (t : ℝ) : ‖B t‖ ≤ (K : ℝ) := by simpa only [B, norm_neg] using hK (-t)
  obtain ⟨g, hgc, hg⟩ := exists_bounded_linear_ode_steps B hB K hBK hδ hsmall (-c) x N
  let g₀ : ℝ → E := fun t => g (-t)
  have hg₀ (t : ℝ) (ht : t ∈ Icc (c - (N : ℝ) * δ) c) :
      HasDerivAt g₀ (A t (g₀ t)) t := by
    have hm : -t ∈ Icc (-c) (-c + (N : ℝ) * δ) := by
      constructor <;> linarith [ht.1, ht.2]
    change HasDerivAt (g ∘ Neg.neg) (A t (g (-t))) t
    simpa only [B, neg_neg, ContinuousLinearMap.neg_apply, neg_smul, one_smul] using
      (hg (-t) hm).scomp t (hasDerivAt_neg t)
  have hnδ : 0 ≤ (N : ℝ) * δ := mul_nonneg (Nat.cast_nonneg N) hδ.le
  obtain ⟨u, hug, _, hu⟩ := exists_ode_join
    (by linarith : c - (N : ℝ) * δ ≤ c)
    (by linarith : c ≤ c + (N : ℝ) * δ) hg₀ hf (hgc.trans hfc.symm)
  refine ⟨u, (hug ⟨by linarith, le_rfl⟩).trans hgc, fun t ht => hu t ?_⟩
  have hca := (le_max_left (c - a) (b - c)).trans_lt hspan
  have hbc := (le_max_right (c - a) (b - c)).trans_lt hspan
  constructor <;> linarith [ht.1, ht.2]

/-- Clamping the coefficient outside a compact interval removes the global
boundedness hypothesis without changing the equation on that interval. -/
theorem exists_linear_ode_on_Icc {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (hA : ContinuousOn A (Icc a b)) (c : ℝ) (x : E) :
    ∃ f : ℝ → E, f c = x ∧
      ∀ t ∈ Icc a b, HasDerivAt f (A t (f t)) t := by
  let A₀ : ℝ → E →L[ℝ] E := IccExtend hab (fun t : Icc a b => A t)
  have hA₀ : Continuous A₀ := hA.domRestrict.Icc_extend'
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  let K : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hK (t : ℝ) : ‖A₀ t‖ ≤ (K : ℝ) := by
    rw [show A₀ t = A (max a (min b t)) from IccExtend_apply hab _ t]
    exact (hC _ ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩).trans (le_max_left _ _)
  obtain ⟨f, hfc, hf⟩ := exists_bounded_linear_ode A₀ hA₀ K hK a b c x
  refine ⟨f, hfc, fun t ht => ?_⟩
  have hEq : A₀ t = A t := IccExtend_of_mem hab _ ht
  simpa only [hEq] using hf t ht

/-- Uniqueness on a closed interval, including initial states at either end. -/
theorem linear_ode_unique_on_Icc {a b c : ℝ} (A : ℝ → E →L[ℝ] E)
    (hA : ContinuousOn A (Icc a b)) (hc : c ∈ Icc a b) {f g : ℝ → E}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (A t (f t)) t)
    (hg : ∀ t ∈ Icc a b, HasDerivAt g (A t (g t)) t)
    (heq : f c = g c) : EqOn f g (Icc a b) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  let K : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hLip (t : ℝ) (ht : t ∈ Icc a b) : LipschitzOnWith K (A t) (univ : Set E) := by
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro y z
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact ((A t).le_opNorm (y - z)).trans
      (mul_le_mul_of_nonneg_right ((hC t ht).trans (le_max_left _ _)) (norm_nonneg _))
  intro t ht
  rcases le_total t c with htc | hct
  · have hsub : Icc t c ⊆ Icc a b := fun s hs => ⟨ht.1.trans hs.1, hs.2.trans hc.2⟩
    exact ODE_solution_unique_of_mem_Icc_left
      (s := fun _ => univ)
      (fun s hs => hLip s (hsub (Ioc_subset_Icc_self hs)))
      (HasDerivAt.continuousOn (fun s hs => hf s (hsub hs)))
      (fun s hs => (hf s (hsub (Ioc_subset_Icc_self hs))).hasDerivWithinAt)
      (fun _ _ => mem_univ _)
      (HasDerivAt.continuousOn (fun s hs => hg s (hsub hs)))
      (fun s hs => (hg s (hsub (Ioc_subset_Icc_self hs))).hasDerivWithinAt)
      (fun _ _ => mem_univ _) heq ⟨le_rfl, htc⟩
  · have hsub : Icc c t ⊆ Icc a b := fun s hs => ⟨hc.1.trans hs.1, hs.2.trans ht.2⟩
    exact ODE_solution_unique_of_mem_Icc_right
      (s := fun _ => univ)
      (fun s hs => hLip s (hsub (Ico_subset_Icc_self hs)))
      (HasDerivAt.continuousOn (fun s hs => hf s (hsub hs)))
      (fun s hs => (hf s (hsub (Ico_subset_Icc_self hs))).hasDerivWithinAt)
      (fun _ _ => mem_univ _)
      (HasDerivAt.continuousOn (fun s hs => hg s (hsub hs)))
      (fun s hs => (hg s (hsub (Ico_subset_Icc_self hs))).hasDerivWithinAt)
      (fun _ _ => mem_univ _) heq ⟨hct, le_rfl⟩

end ContinuousFlexibility.Analysis
