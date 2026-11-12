import ContinuousFlexibility.Analysis.N07aAngularPieceCover
import ContinuousFlexibility.Analysis.N07aCurrentPhysicalGeometry

/-!
# The actual middle cut is a null curve

The inverse chart is differentiable on the entire canonical boundary, so
its image of a vertical null line is null. Negative reference pieces are
identified with their original component pairs using the reference
partition and the control geometry, without identifying current halves
with fixed rectangles.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

theorem n07a_currentCutPoint_mem_closed
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (k : ℕ) (θ : ℝ) :
    canonicalCutPoint S K z k θ ∈ physicalPieceClosed S K z (K.cutPair k).1 ∧
      canonicalCutPoint S K z k θ ∈ physicalPieceClosed S K z (K.cutPair k).2 := by
  obtain ⟨_, _, _, _, _, hR, hl, hr, hRl, hRr⟩ := h04.2.1.1.1 k
  have hleft : (K.cutRadius k, θ) ∈ canonicalClosed S K (K.cutPair k).1 := by
    exact ⟨⟨by simpa only [hl] using hR.le, by rw [hRl]⟩, mem_univ _⟩
  have hright : (K.cutRadius k, θ) ∈ canonicalClosed S K (K.cutPair k).2 := by
    exact ⟨⟨by simpa only [hr] using hR.le, by rw [hRr]⟩, mem_univ _⟩
  refine ⟨(h04.1.boundary z hz hs (K.cutPair k).1).2.1 hleft, ?_⟩
  rw [← (h04.2.1.1.2 z hz hs k).1 θ]
  exact (h04.1.boundary z hz hs (K.cutPair k).2).2.1 hright

theorem n07a_currentCut_volume_zero
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (k : ℕ) :
    volume (Set.range (canonicalCutPoint S K z k)) = 0 := by
  let : (volume : Measure PolarPoint).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  let A : Set PolarPoint := {K.cutRadius k} ×ˢ (univ : Set ℝ)
  have hA : volume A = 0 := by
    simp only [A, Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, zero_mul]
  have hsub : A ⊆ canonicalClosed S K (K.cutPair k).1 := by
    obtain ⟨_, _, _, _, _, hR, hl, _, hRl, _⟩ := h04.2.1.1.1 k
    rintro ⟨r, θ⟩ ⟨hr, _⟩
    have he : r = K.cutRadius k := hr
    subst r
    exact ⟨⟨by simpa only [hl] using hR.le, by rw [hRl]⟩, mem_univ _⟩
  have hd : DifferentiableOn ℝ (K.inverseChart z (K.cutPair k).1) A := by
    intro p hp
    exact ((n04b_inverseChart_contDiffAt_closed h04.1 hz hs (K.cutPair k).1
      (hsub hp)).differentiableAt (by simp)).differentiableWithinAt
  have he : Set.range (canonicalCutPoint S K z k) =
      K.inverseChart z (K.cutPair k).1 '' A := by
    ext p
    constructor
    · rintro ⟨θ, rfl⟩
      exact ⟨(K.cutRadius k, θ), ⟨rfl, mem_univ _⟩, rfl⟩
    · rintro ⟨⟨r, θ⟩, ⟨hr, _⟩, rfl⟩
      have he : r = K.cutRadius k := hr
      subst r
      exact ⟨θ, rfl⟩
  rw [he]
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (volume : Measure PolarPoint) hd hA

/-- Every negative reference interval is one of the two intervals of its
original negative component. This uses the original control cover. -/
theorem n07a_negative_referencePiece_cutPair
    (h04 : N04Properties D T S C L K base loss ε)
    (hcontrol : controlGeometryConditions D S C)
    (m : ℕ) (hm : K.positive m = false) :
    ∃ k, m = (K.cutPair k).1 ∨ m = (K.cutPair k).2 := by
  let r := (K.physicalLeft m + K.physicalRight m) / 2
  have hlen := (h04.1.referenceBounds m).1
  have hrm : r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) := by
    dsimp only [r]
    constructor <;> linarith
  obtain ⟨k, hrk⟩ := hcontrol.2.2.2.2.1 r
    ((h04.1.referenceBounds m).2.2 hrm) (h04.1.referenceNegative m hm r hrm)
  obtain ⟨_, _, hl, hr, hmid, _, _, _, _, _⟩ := h04.2.1.1.1 k
  have heq {i : ℕ} {x : ℝ}
      (hxm : x ∈ Ioo (K.physicalLeft m) (K.physicalRight m))
      (hxi : x ∈ Ioo (K.physicalLeft i) (K.physicalRight i)) : m = i := by
    by_contra hne
    exact Set.disjoint_left.mp (n07a_physicalPieces_pairwise_disjoint h04 hne) hxm hxi
  refine ⟨k, ?_⟩
  by_cases hrc : r ≤ K.physicalRight (K.cutPair k).1
  · let x := (max (K.physicalLeft m) (C.left k) + r) / 2
    have hmax : max (K.physicalLeft m) (C.left k) < r := max_lt hrm.1 hrk.1
    have hmx : max (K.physicalLeft m) (C.left k) < x := by
      dsimp only [x]
      linarith
    have hxr : x < r := by dsimp only [x]; linarith
    have hxm : x ∈ Ioo (K.physicalLeft m) (K.physicalRight m) :=
      ⟨(le_max_left _ _).trans_lt hmx, hxr.trans hrm.2⟩
    have hxi : x ∈ Ioo (K.physicalLeft (K.cutPair k).1)
        (K.physicalRight (K.cutPair k).1) := by
      rw [hl]
      exact ⟨(le_max_right _ _).trans_lt hmx, hxr.trans_le hrc⟩
    exact Or.inl (heq hxm hxi)
  · apply Or.inr
    apply heq hrm
    rw [← hmid, hr]
    exact ⟨lt_of_not_ge hrc, hrk.2⟩

theorem n07a_referenceCutPiece_subset_component
    (h04 : N04Properties D T S C L K base loss ε)
    {k m : ℕ} (hm : m = (K.cutPair k).1 ∨ m = (K.cutPair k).2) :
    referencePhysicalPieceOpen S K m ⊆
      Ioo (C.left k) (C.right k) ×ˢ (univ : Set ℝ) := by
  obtain ⟨_, _, hl, hr, hmid, _, _, _, _, _⟩ := h04.2.1.1.1 k
  have hleft := (h04.1.referenceBounds (K.cutPair k).1).1
  have hright := (h04.1.referenceBounds (K.cutPair k).2).1
  rcases hm with rfl | rfl
  · intro p hp
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩
    · simpa only [hl] using hp.1.1
    · have hgap : K.physicalRight (K.cutPair k).1 < K.physicalRight (K.cutPair k).2 := by
        simpa only [hmid] using hright
      have h := hp.1.2.trans hgap
      simpa only [hr] using h
  · intro p hp
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩
    · have hgap : K.physicalLeft (K.cutPair k).1 < K.physicalLeft (K.cutPair k).2 := by
        simpa only [hmid] using hleft
      have h := hgap.trans hp.1.1
      simpa only [hl] using h
    · simpa only [hr] using hp.1.2

end ContinuousFlexibility.Analysis
