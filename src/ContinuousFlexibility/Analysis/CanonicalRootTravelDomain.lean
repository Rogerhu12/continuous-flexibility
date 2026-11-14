import ContinuousFlexibility.Analysis.CanonicalStoredTravelCoordinates

/-!
# A quantitative travel criterion for the correct moving half

The true glued first integrals distinguish the two halves, including
their actual common cut. A point whose travel from one outer root is
strictly smaller than the cut travel must belong to that root's open
half. This criterion can be applied on a state-independent root band;
it does not infer a uniform band from pointwise boundary continuity.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

def canonicalGluedRootTravel (S : PhysicalSpacesData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (rightEnd : Bool) (p : PolarPoint) : ℝ :=
  let t := (canonicalGluedAiryIntegral S K z m 1 p -
    canonicalGluedAiryIntegral S K z m (-1) p) / 2
  if rightEnd then 2 * airyTravelPrimitive (K.cutRadius m) - t else t

theorem canonicalGluedAiryIntegral_on_cut
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (σ θ : ℝ) :
    canonicalGluedAiryIntegral S K z m σ (canonicalCutPoint S K z m θ) =
      θ + σ * airyTravelPrimitive (K.cutRadius m) := by
  classical
  have hn : canonicalCutPoint S K z m θ ∉
      physicalPieceOpen S K z (K.cutPair m).1 := by
    intro hp
    have hu : canonicalCutPoint S K z m θ ∈
        physicalPieceOpen S K z (K.cutPair m).1 ∪
          physicalPieceOpen S K z (K.cutPair m).2 := Or.inl hp
    rw [(hB.1.2 z hz hs m).2.2.2.1] at hu
    exact hu.2 (mem_range_self θ)
  have he : canonicalGluedAiryIntegral S K z m σ (canonicalCutPoint S K z m θ) =
      airyFirstIntegral (K.chart z (K.cutPair m).2) (-σ)
        (canonicalCutPoint S K z m θ) + 2 * σ * airyTravelPrimitive (K.cutRadius m) :=
    piecewise_eq_of_notMem _ _ _ hn
  have hcut : K.chart z (K.cutPair m).2 (canonicalCutPoint S K z m θ) =
      (K.cutRadius m, θ) := (canonicalCut_closed_and_chart hA hB hz hs m true θ).2
  rw [he]
  simp only [airyFirstIntegral, hcut]
  ring

private theorem airyTravelPrimitive_le_of_nonneg_le
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    airyTravelPrimitive x ≤ airyTravelPrimitive y := by
  unfold airyTravelPrimitive
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hx hxy (by norm_num : (0 : ℝ) ≤ 3 / 2)) (by norm_num)

/-- Travel below the common cut travel forces membership in the correct
actual open half. The cut itself is excluded by its exact trace value. -/
theorem canonicalCutPair_mem_own_half_of_rootTravel_lt
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (rightEnd : Bool) {p : PolarPoint}
    (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
    (hsmall : canonicalGluedRootTravel S K z m rightEnd p <
      airyTravelPrimitive (K.cutRadius m)) :
    p ∈ physicalPieceOpen S K z
      (if rightEnd then (K.cutPair m).2 else (K.cutPair m).1) := by
  have hcover := (hB.1.2 z hz hs m).2.2.2.1
  have hdisjoint := (hB.1.2 z hz hs m).2.2.1
  have hnotCut : p ∉ Set.range (canonicalCutPoint S K z m) := by
    rintro ⟨θ, rfl⟩
    have hV := canonicalGluedAiryIntegral_on_cut hA hB hz hs m 1 θ
    have hU := canonicalGluedAiryIntegral_on_cut hA hB hz hs m (-1) θ
    simp only [canonicalGluedRootTravel, hV, hU] at hsmall
    cases rightEnd <;>
      simp only [Bool.false_eq_true, ite_false, ite_true] at hsmall <;>
      linarith only [hsmall]
  have hwhere : p ∈ physicalPieceOpen S K z (K.cutPair m).1 ∪
      physicalPieceOpen S K z (K.cutPair m).2 := by
    rw [hcover]
    exact ⟨hp, hnotCut⟩
  have hupper (side : Bool)
      (hside : p ∈ physicalPieceOpen S K z
        (if side then (K.cutPair m).2 else (K.cutPair m).1)) :
      airyTravelPrimitive
        (K.chart z (if side then (K.cutPair m).2 else (K.cutPair m).1) p).1 ≤
          airyTravelPrimitive (K.cutRadius m) := by
    let i := if side then (K.cutPair m).2 else (K.cutPair m).1
    obtain ⟨_, _, _, _, _, _, hl₀, hl₁, hr₀, hr₁⟩ := hB.1.1 m
    have hl : K.left i = 0 := by cases side <;> assumption
    have hr : K.right i = K.cutRadius m := by cases side <;> assumption
    have hq := (hA.charts z hz hs i).1 hside
    have hqpos : 0 < (K.chart z i p).1 := by simpa only [hl] using hq.1.1
    have hqright : (K.chart z i p).1 < K.cutRadius m := by
      simpa only [hr] using hq.1.2
    exact airyTravelPrimitive_le_of_nonneg_le hqpos.le hqright.le
  cases rightEnd with
  | false =>
      rcases hwhere with hleft | hright
      · exact hleft
      · have hv := (canonicalCutPair_chartValues_of_gluedIntegrals m true hdisjoint hright).2
        have hu := hupper true hright
        simp only [canonicalGluedRootTravel, Bool.false_eq_true, ite_false] at hsmall
        simp only [ite_true] at hv hu
        linarith only [hv, hu, hsmall]
  | true =>
      rcases hwhere with hleft | hright
      · have hv := (canonicalCutPair_chartValues_of_gluedIntegrals m false hdisjoint hleft).2
        have hu := hupper false hleft
        simp only [canonicalGluedRootTravel, ite_true] at hsmall
        simp only [Bool.false_eq_true, ite_false] at hv hu
        linarith only [hv, hu, hsmall]
      · exact hright

end ContinuousFlexibility.Analysis
