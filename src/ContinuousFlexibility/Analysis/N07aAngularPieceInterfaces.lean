import ContinuousFlexibility.Analysis.N07aAngularPieceCover

/-!
# Every actual interior interface has its two adjacent pieces

The a.e. cover and the proved local finiteness imply an everywhere cover
by the closed physical intervals. A point outside their open interiors
therefore has one interval ending there and one starting there. The two
sides use the same elementary finite-cover lemma, with reflection.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory CanonicalGeometry

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

theorem n07a_physicalClosedPieces_cover
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base loss ε)
    (hjets : ReferenceJets D T S C L K)
    {r : ℝ} (hr : r ∈ Ioo D.a D.b) :
    ∃ m, r ∈ Icc (K.physicalLeft m) (K.physicalRight m) := by
  let l : ℝ := (D.a + r) / 2
  let s : ℝ := (r + D.b) / 2
  have hal : D.a < l := by dsimp only [l]; linarith [hr.1]
  have hlr : l < r := by dsimp only [l]; linarith [hr.1]
  have hrs : r < s := by dsimp only [s]; linarith [hr.2]
  have hsb : s < D.b := by dsimp only [s]; linarith [hr.2]
  let F : Set ℕ := {m | (Icc l s ∩ Icc (K.physicalLeft m) (K.physicalRight m)).Nonempty}
  have hF : F.Finite := n07a_physicalClosedPieces_finite_inter_compact hD hT h04 hjets
    isCompact_Icc (fun _ hx => ⟨hal.trans_le hx.1, hx.2.trans_lt hsb⟩)
  let A : Set ℝ := ⋃ m ∈ F, Icc (K.physicalLeft m) (K.physicalRight m)
  have hAc : IsClosed A := hF.isClosed_biUnion fun _ _ => isClosed_Icc
  have hrA : r ∈ A := by
    by_contra hrA
    obtain ⟨E, hE, hcover⟩ := h04.1.referencePartition
    have hOE : Ioo l s \ A ⊆ E := by
      intro x hx
      by_contra hxE
      obtain ⟨m, hxm, _⟩ := hcover x
        ⟨⟨hal.trans hx.1.1, hx.1.2.trans hsb⟩, hxE⟩
      have hmF : m ∈ F := ⟨x, Ioo_subset_Icc_self hx.1, Ioo_subset_Icc_self hxm⟩
      exact hx.2 (mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨hmF, Ioo_subset_Icc_self hxm⟩⟩)
    have hzero := measure_mono_null hOE hE
    exact ((isOpen_Ioo.sdiff hAc).measure_ne_zero volume ⟨r, ⟨hlr, hrs⟩, hrA⟩) hzero
  rcases mem_iUnion.mp hrA with ⟨m, hm⟩
  rcases mem_iUnion.mp hm with ⟨_, hrm⟩
  exact ⟨m, hrm⟩

theorem n07a_finite_interval_right_neighbor {ι : Type*} {left right : ι → ℝ}
    {x y : ℝ} (hxy : x < y) (hlen : ∀ i, left i < right i)
    (hcover : ∀ q ∈ Ioo x y, ∃ i, q ∈ Icc (left i) (right i))
    (hfinite : Set.Finite {i | (Icc x y ∩ Icc (left i) (right i)).Nonempty})
    (hnot : ∀ i, x ∉ Ioo (left i) (right i)) :
    ∃ i, left i = x ∧ x < right i := by
  let F : Set ι := {i | (Icc x y ∩ Icc (left i) (right i)).Nonempty ∧ x ≤ left i}
  have hF : F.Finite := hfinite.subset (fun _ hi => hi.1)
  let A : Set ℝ := ⋃ i ∈ F, Icc (left i) (right i)
  have hAc : IsClosed A := hF.isClosed_biUnion fun _ _ => isClosed_Icc
  have hsub : Ioo x y ⊆ A := by
    intro q hq
    obtain ⟨i, hqi⟩ := hcover q hq
    have hxi : x ≤ left i := by
      by_contra hx
      exact hnot i ⟨lt_of_not_ge hx, hq.1.trans_le hqi.2⟩
    have hi : i ∈ F := ⟨⟨q, Ioo_subset_Icc_self hq, hqi⟩, hxi⟩
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hqi⟩⟩
  have hx : x ∈ closure (Ioo x y) := by
    rw [closure_Ioo hxy.ne]
    exact ⟨le_rfl, hxy.le⟩
  have hxA : x ∈ A := by
    have h := closure_mono hsub hx
    rwa [hAc.closure_eq] at h
  rcases mem_iUnion.mp hxA with ⟨i, hi⟩
  rcases mem_iUnion.mp hi with ⟨hiF, hxi⟩
  have he : left i = x := le_antisymm hxi.1 hiF.2
  exact ⟨i, he, he ▸ hlen i⟩

/-- No extra interfaces or an assumed trace cover are needed: every
non-interior point of the annulus has the original left and right pieces. -/
theorem n07a_physicalPieces_adjacent_at_boundary
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base loss ε)
    (hjets : ReferenceJets D T S C L K)
    {r : ℝ} (hr : r ∈ Ioo D.a D.b)
    (hnot : ∀ m, r ∉ Ioo (K.physicalLeft m) (K.physicalRight m)) :
    ∃ i j, i ≠ j ∧ K.physicalRight i = r ∧ K.physicalLeft j = r := by
  let l : ℝ := (D.a + r) / 2
  let s : ℝ := (r + D.b) / 2
  have hal : D.a < l := by dsimp only [l]; linarith [hr.1]
  have hlr : l < r := by dsimp only [l]; linarith [hr.1]
  have hrs : r < s := by dsimp only [s]; linarith [hr.2]
  have hsb : s < D.b := by dsimp only [s]; linarith [hr.2]
  have hright := n07a_finite_interval_right_neighbor hrs
    (fun m => (h04.1.referenceBounds m).1)
    (fun q hq => n07a_physicalClosedPieces_cover hD hT h04 hjets
      ⟨hr.1.trans hq.1, hq.2.trans hsb⟩)
    (n07a_physicalClosedPieces_finite_inter_compact hD hT h04 hjets isCompact_Icc
      (fun _ hx => ⟨hr.1.trans_le hx.1, hx.2.trans_lt hsb⟩)) hnot
  have hfinite : Set.Finite {m | (Icc (-r) (-l) ∩
      Icc (-K.physicalRight m) (-K.physicalLeft m)).Nonempty} := by
    apply (n07a_physicalClosedPieces_finite_inter_compact hD hT h04 hjets isCompact_Icc
      (show Icc l r ⊆ Ioo D.a D.b from
        fun _ hx => ⟨hal.trans_le hx.1, hx.2.trans_lt hr.2⟩)).subset
    rintro m ⟨q, hq, hm⟩
    exact ⟨-q, ⟨by linarith [hq.2], by linarith [hq.1]⟩,
      ⟨by linarith [hm.2], by linarith [hm.1]⟩⟩
  have hleft := n07a_finite_interval_right_neighbor (neg_lt_neg hlr)
    (left := fun m => -K.physicalRight m) (right := fun m => -K.physicalLeft m)
    (fun m => neg_lt_neg (h04.1.referenceBounds m).1)
    (fun q hq => by
      obtain ⟨m, hm⟩ := n07a_physicalClosedPieces_cover hD hT h04 hjets
        (show -q ∈ Ioo D.a D.b from ⟨by linarith [hq.2], by linarith [hq.1]⟩)
      exact ⟨m, ⟨by linarith [hm.2], by linarith [hm.1]⟩⟩)
    hfinite (fun m hm => hnot m ⟨by linarith [hm.2], by linarith [hm.1]⟩)
  obtain ⟨i, hi, _⟩ := hleft
  obtain ⟨j, hj, _⟩ := hright
  have hi' : K.physicalRight i = r := neg_injective hi
  refine ⟨i, j, ?_, hi', hj⟩
  intro hij
  subst j
  have hlen := (h04.1.referenceBounds i).1
  linarith

end ContinuousFlexibility.Statements
