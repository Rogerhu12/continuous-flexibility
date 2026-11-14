module

public import ContinuousFlexibility.Radial.MatchingTraceCalculus

/-!
# Combining the two physical outer representatives

The open inner interval is zero.  The two supplied side representatives
remain unchanged on the half-closed outer intervals, with arbitrary
within regularity and the original one-sided matching derivatives.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def matchedOuterSideGlue (left right : ℝ) (uL uR : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ left then uL x else if right ≤ x then uR x else 0

theorem matchedOuterSideGlue_of_le {left right x : ℝ} (uL uR : ℝ → ℝ)
    (hx : x ≤ left) : matchedOuterSideGlue left right uL uR x = uL x := by
  simp only [matchedOuterSideGlue, if_pos hx]

theorem matchedOuterSideGlue_of_ge {left right x : ℝ} (hgap : left < right)
    (uL uR : ℝ → ℝ) (hx : right ≤ x) :
    matchedOuterSideGlue left right uL uR x = uR x := by
  simp only [matchedOuterSideGlue, if_neg (not_le.mpr (hgap.trans_le hx)), if_pos hx]

theorem matchedOuterSideGlue_inner {left right x : ℝ} (uL uR : ℝ → ℝ)
    (hx : x ∈ Ioo left right) : matchedOuterSideGlue left right uL uR x = 0 := by
  simp only [matchedOuterSideGlue, if_neg (not_le.mpr hx.1), if_neg (not_le.mpr hx.2)]

theorem matchedOuterSideGlue_eventuallyEq_left {left right x : ℝ}
    (uL uR : ℝ → ℝ) (hx : x < left) :
    matchedOuterSideGlue left right uL uR =ᶠ[𝓝 x] uL := by
  filter_upwards [Iio_mem_nhds hx] with y hy
  exact matchedOuterSideGlue_of_le uL uR hy.le

theorem matchedOuterSideGlue_eventuallyEq_right {left right x : ℝ}
    (hgap : left < right) (uL uR : ℝ → ℝ) (hx : right < x) :
    matchedOuterSideGlue left right uL uR =ᶠ[𝓝 x] uR := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact matchedOuterSideGlue_of_ge hgap uL uR hy.le

/-- This single result applies to both frozen C1 graphs and C2 columns. -/
theorem matchedOuterSideGlue_contDiffOn {a left right b : ℝ} {k : ℕ∞ω}
    (hgap : left < right) {uL uR : ℝ → ℝ}
    (hL : ContDiffOn ℝ k uL (Ioc a left))
    (hR : ContDiffOn ℝ k uR (Ico right b)) :
    ContDiffOn ℝ k (matchedOuterSideGlue left right uL uR)
      (Ioc a left ∪ Ico right b) := by
  intro x hx
  rcases hx with hx | hx
  · have hs : Ioc a left ∈ 𝓝[Ioc a left ∪ Ico right b] x := by
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (hx.2.trans_lt hgap)),
        self_mem_nhdsWithin] with y hyr hy
      rcases hy with hy | hy
      · exact hy
      · exact False.elim ((not_le_of_gt hyr) hy.1)
    apply ((hL x hx).mono_of_mem_nhdsWithin hs).congr_of_eventuallyEq
    · filter_upwards [hs] with y hy
      exact matchedOuterSideGlue_of_le uL uR hy.2
    · exact matchedOuterSideGlue_of_le uL uR hx.2
  · have hs : Ico right b ∈ 𝓝[Ioc a left ∪ Ico right b] x := by
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (hgap.trans_le hx.1)),
        self_mem_nhdsWithin] with y hyl hy
      rcases hy with hy | hy
      · exact False.elim ((not_le_of_gt hyl) hy.2)
      · exact hy
    apply ((hR x hx).mono_of_mem_nhdsWithin hs).congr_of_eventuallyEq
    · filter_upwards [hs] with y hy
      exact matchedOuterSideGlue_of_ge hgap uL uR hy.1
    · exact matchedOuterSideGlue_of_ge hgap uL uR hx.1

theorem matchedOuterSideGlue_derivWithin_left {a left right b : ℝ}
    (ha : a < left) (hgap : left < right) (hb : right < b)
    (uL uR : ℝ → ℝ) :
    derivWithin (matchedOuterSideGlue left right uL uR)
        (closure (Ioo a left ∪ Ioo right b)) left =
      derivWithin uL (Ioc a left) left := by
  have hs : closure (Ioo a left ∪ Ioo right b) =ᶠ[𝓝 left] Ioc a left := by
    rw [closure_union, closure_Ioo ha.ne, closure_Ioo hb.ne]
    filter_upwards [Ioo_mem_nhds ha hgap] with x hx
    apply propext
    constructor
    · rintro (h | h)
      · exact ⟨hx.1, h.2⟩
      · exact False.elim ((not_le_of_gt hx.2) h.1)
    · intro h
      exact Or.inl ⟨h.1.le, h.2⟩
  calc
    _ = derivWithin (matchedOuterSideGlue left right uL uR) (Ioc a left) left :=
      derivWithin_congr_set hs
    _ = _ := derivWithin_congr
      (fun x hx => matchedOuterSideGlue_of_le uL uR hx.2)
      (matchedOuterSideGlue_of_le uL uR le_rfl)

theorem matchedOuterSideGlue_derivWithin_right {a left right b : ℝ}
    (ha : a < left) (hgap : left < right) (hb : right < b)
    (uL uR : ℝ → ℝ) :
    derivWithin (matchedOuterSideGlue left right uL uR)
        (closure (Ioo a left ∪ Ioo right b)) right =
      derivWithin uR (Ico right b) right := by
  have hs : closure (Ioo a left ∪ Ioo right b) =ᶠ[𝓝 right] Ico right b := by
    rw [closure_union, closure_Ioo ha.ne, closure_Ioo hb.ne]
    filter_upwards [Ioo_mem_nhds hgap hb] with x hx
    apply propext
    constructor
    · rintro (h | h)
      · exact False.elim ((not_le_of_gt hx.1) h.2)
      · exact ⟨h.1, hx.2⟩
    · intro h
      exact Or.inr ⟨h.1, h.2.le⟩
  calc
    _ = derivWithin (matchedOuterSideGlue left right uL uR) (Ico right b) right :=
      derivWithin_congr_set hs
    _ = _ := derivWithin_congr
      (fun x hx => matchedOuterSideGlue_of_ge hgap uL uR hx.1)
      (matchedOuterSideGlue_of_ge hgap uL uR le_rfl)

/-- The actual Hilbert representative is obtained from the two restricted
representatives and the zero inner component. -/
theorem matchedOuterSideGlue_representative {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (hm : M.innerLeft < M.innerRight) {f uL uR : ℝ → ℝ}
    (hL : f =ᵐ[(radialHilbertMeasure D).restrict (Ioo D.a M.innerLeft)] uL)
    (hR : f =ᵐ[(radialHilbertMeasure D).restrict (Ioo M.innerRight D.b)] uR)
    (hI : f =ᵐ[(radialHilbertMeasure D).restrict (Ioo M.innerLeft M.innerRight)]
      fun _ => 0) :
    f =ᵐ[radialHilbertMeasure D] matchedOuterSideGlue M.innerLeft M.innerRight uL uR := by
  filter_upwards [ae_imp_of_ae_restrict hL, ae_imp_of_ae_restrict hR,
    ae_imp_of_ae_restrict hI, matching_ae_inner_or_outer hD M] with x hxL hxR hxI hx
  rcases hx with hx | (hx | hx)
  · rw [matchedOuterSideGlue_inner uL uR hx, hxI hx]
  · rw [matchedOuterSideGlue_of_le uL uR hx.2.le, hxL hx]
  · rw [matchedOuterSideGlue_of_ge hm uL uR hx.1.le, hxR hx]

theorem matchedOuterSideGlue_matching_derivWithin_left {D : ReferenceData}
    {M : RadialMatchingData D} (ha : D.a < M.innerLeft)
    (hm : M.innerLeft < M.innerRight) (hb : M.innerRight < D.b) (uL uR : ℝ → ℝ) :
    derivWithin (matchedOuterSideGlue M.innerLeft M.innerRight uL uR)
        (closure (matchingOuterRegion D M)) M.innerLeft =
      derivWithin uL (Ioc D.a M.innerLeft) M.innerLeft :=
  matchedOuterSideGlue_derivWithin_left ha hm hb uL uR

theorem matchedOuterSideGlue_matching_derivWithin_right {D : ReferenceData}
    {M : RadialMatchingData D} (ha : D.a < M.innerLeft)
    (hm : M.innerLeft < M.innerRight) (hb : M.innerRight < D.b) (uL uR : ℝ → ℝ) :
    derivWithin (matchedOuterSideGlue M.innerLeft M.innerRight uL uR)
        (closure (matchingOuterRegion D M)) M.innerRight =
      derivWithin uR (Ico M.innerRight D.b) M.innerRight :=
  matchedOuterSideGlue_derivWithin_right ha hm hb uL uR

end ContinuousFlexibility.Radial
