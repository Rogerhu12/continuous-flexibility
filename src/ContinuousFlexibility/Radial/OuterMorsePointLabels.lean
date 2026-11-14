module

public import ContinuousFlexibility.Radial.MorseChainLocalGluing
public import ContinuousFlexibility.Radial.OuterLocalizerCutoff
public import ContinuousFlexibility.Radial.OuterTailPointwiseBounds
public import ContinuousFlexibility.Radial.OuterTransitionCoordinates

/-!
# Actual physical labels on the whole outer interval

The finite core has label `N`. The initial deep interval and the first
closed node edge have label `N+1`; every later edge retains its absolute
Morse label. The cover uses the actual node limit and coordinate map,
without numerical deep-tail hypotheses. A specified nonzero localizer
has physical label within two of any label assigned to its point.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

/-- The true logarithmic tail has the initial/edge cover purely from its
geometrical accumulation, independently of its mass-resistance estimates. -/
theorem morsePhysicalDeepTail_exists_outerTailPoint
    {M : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization M σ D C) (right : Bool) (j start : ℕ)
    (entrance η K : ℝ) {x : ℝ}
    (hx : x ∈ Ico
      (morsePhysicalDeepTail M D right j start entrance η K).entrance
      (morsePhysicalDeepTail M D right j start entrance η K).endpoint) :
    ∃ k, OuterTailPoint (morsePhysicalDeepTail M D right j start entrance η K) k x := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  by_cases hfirst : x ≤ T.node 0
  · exact ⟨0, Or.inl ⟨rfl, hx.1, hfirst⟩⟩
  · obtain ⟨k, hk⟩ := morse_outward_block_exists
      (morsePhysicalDeepTail_nodes_tendsto h right j start entrance η K)
      (lt_of_not_ge hfirst).le hx.2
    exact ⟨k, Or.inr ⟨hk.1, hk.2.le⟩⟩

/-- A position label in the actual increasing outward radial coordinate.
The middle entry is retained in the interface used by the transition
operator; for `N > M.index` the core endpoints are the ordinary ones. -/
def MorseOuterPoint (M : MorseChainData) (D : ReferenceData) (entry : ℝ)
    (right : Bool) (j N : ℕ) (η K : ℝ) (p : ℕ) (r : ℝ) : Prop :=
  (p = N ∧ r ∈ Icc (morseTransitionOutwardLeft M entry right N)
    (morseTransitionOutwardRight M entry right N)) ∨
    ∃ k x, p = N + 1 + k ∧
      OuterTailPoint
        (morsePhysicalDeepTail M D right j (N + 1) (morseOuterDeepEntrance M right N) η K) k x ∧
      r = outerOutwardLogRadius right x

theorem morseOuterPoint_label_ge
    {M : MorseChainData} {D : ReferenceData} {entry η K r : ℝ}
    {right : Bool} {j N p : ℕ} (hp : MorseOuterPoint M D entry right j N η K p r) :
    N ≤ p := by
  rcases hp with ⟨rfl, _⟩ | ⟨k, x, hp, _, _⟩
  · exact le_rfl
  · omega

/-- Every actual outward point, including the regular entrance, receives
a core or deep position label. -/
theorem exists_morseOuterPoint
    {M : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization M σ D C) (right : Bool) (j N : ℕ)
    (hN : M.index ≤ N) (entry η K : ℝ) {r : ℝ}
    (hr : r ∈ Ico (morseTransitionOutwardLeft M entry right N)
      (outerOutwardRadius right (tailPhysicalEndpoint D right))) :
    ∃ p, MorseOuterPoint M D entry right j N η K p r := by
  by_cases hcore : r ≤ morseTransitionOutwardRight M entry right N
  · exact ⟨N, Or.inl ⟨rfl, hr.1, hcore⟩⟩
  · have htail : r ∈ Ico (outerOutwardRadius right (morseOuterDeepEntrance M right N))
        (outerOutwardRadius right (tailPhysicalEndpoint D right)) := by
      rw [← morseTransitionOutwardRight_eq M entry right N]
      exact ⟨(lt_of_not_ge hcore).le, hr.2⟩
    have hentry : 0 < morseOuterDeepEntrance M right N :=
      h.geometry.1.trans (morseOuterDeepEntrance_mem_core h right N hN).1
    have hcoord := outerTail_outward_log_mem h.geometry right (t := r) hentry
      (by simpa only [outerOutwardRadius_eq_sign] using htail)
    obtain ⟨k, hk⟩ := morsePhysicalDeepTail_exists_outerTailPoint h right j (N + 1)
      (morseOuterDeepEntrance M right N) η K hcoord.2
    refine ⟨N + 1 + k, Or.inr ⟨k, tailPhysicalLog right (outerTailSign right * r),
      rfl, hk, ?_⟩⟩
    rw [outerOutwardLogRadius, tailPhysicalRadius_log right hcoord.1,
      ← outerOutwardRadius_eq_sign right r, outerOutwardRadius_twice]

/-- The reverse support bridge uses the fixed localizer `m` and its actual
physical index, in the same outward coordinate as the whole Green kernel. -/
theorem morseOuterPoint_localizer_labels
    {M : MorseChainData} {D : ReferenceData} {entry η K r : ℝ}
    {right : Bool} {j N p m : ℕ} (hN : M.index < N)
    (hlabels : MorseOuterLocalizerLabels M D N)
    (hp : MorseOuterPoint M D entry right j N η K p r)
    (hθ : D.localizer m (outerOutwardRadius right r) ≠ 0) :
    p ≤ D.cellIndex m + 2 ∧ D.cellIndex m ≤ p + 2 := by
  rcases hp with ⟨hpp, hr⟩ | ⟨k, x, rfl, hx, rfl⟩
  · subst p
    have hne : N ≠ M.index := ne_of_gt hN
    have hrad : outerOutwardRadius right r ∈
        Icc (morseOuterCoreLeft M right N) (morseOuterFullCoreRight M right N) := by
      apply (outerOutwardRadius_mem_core_interval right _ _ r).mpr
      simpa only [morseTransitionOutwardLeft, morseTransitionOutwardRight,
        morseTransitionCoreLeft, morseTransitionCoreRight, if_neg hne] using hr
    exact hlabels.2.2 right m (outerOutwardRadius right r) hrad hθ
  · have hθ' : D.localizer m (tailPhysicalRadius right x) ≠ 0 := by
      simpa only [outerOutwardLogRadius, outerOutwardRadius_twice] using hθ
    rcases hx with ⟨rfl, hx⟩ | hx
    · simpa only [Nat.add_zero] using hlabels.2.1 right j η K m x hx hθ'
    · exact hlabels.1 right j η K k m x hx hθ'

/-- Every contributing localizer has a positive physical index once the
uniform cutoff is at least three cells beyond the original chain index. -/
theorem morseOuterPoint_localizer_pos
    {M : MorseChainData} {D : ReferenceData} {entry η K r : ℝ}
    {right : Bool} {j N p m : ℕ} (hN : M.index + 3 ≤ N)
    (hlabels : MorseOuterLocalizerLabels M D N)
    (hp : MorseOuterPoint M D entry right j N η K p r)
    (hθ : D.localizer m (outerOutwardRadius right r) ≠ 0) :
    1 ≤ D.cellIndex m := by
  have hlow := morseOuterPoint_label_ge hp
  have hnear := (morseOuterPoint_localizer_labels (by omega : M.index < N) hlabels hp hθ).1
  omega

end ContinuousFlexibility.Radial
