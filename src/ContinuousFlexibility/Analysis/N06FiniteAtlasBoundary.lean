import ContinuousFlexibility.Analysis.N06FinitePhysicalPartition
import ContinuousFlexibility.Analysis.N06NaturalPieceFiniteness
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Order.Interval.Set.Disjoint

/-!
# Endpoint cancellation in the reference atlas index order

The a.e. interval cover and compact finiteness force genuine adjacent
pieces on both sides of every interior endpoint. Disjointness makes each
neighbor unique. Reindexing right endpoints by their actual left neighbors
then cancels a finite boundary sum from the two-sided boundary identities.

The final theorem applies this construction to the original N04 reference
interval metadata. These intervals supply an index order, not the shape of
the current moving physical domains. No extra interval partition or
vanishing total boundary sum is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology BigOperators

/-- A closed set containing almost every point of an open interval
contains both actual endpoints as well. -/
theorem n06_closed_contains_interval_of_ae
    {a b x : ℝ} {F : Set ℝ} (hab : a < b) (hF : IsClosed F)
    (hcover : ∀ᵐ t ∂volume, t ∈ Ioo a b → t ∈ F)
    (hx : x ∈ Icc a b) : x ∈ F := by
  have hzero : volume (Ioo a b \ F) = 0 := by
    apply measure_mono_null ?_ (ae_iff.mp hcover)
    intro t ht h
    exact ht.2 (h ht.1)
  have hempty : Ioo a b \ F = ∅ :=
    (isOpen_Ioo.inter hF.isOpen_compl).eq_empty_of_measure_zero hzero
  have hsub : Ioo a b ⊆ F := by
    intro t ht
    by_contra hn
    have hm : t ∈ Ioo a b \ F := ⟨ht, hn⟩
    rw [hempty] at hm
    exact hm
  apply closure_minimal hsub hF
  simpa only [closure_Ioo hab.ne] using hx

/-- A finite a.e. interval cover reaches an interior point from each
side with actual closed interval values. The two pieces may coincide
when the point lies in the interior of one piece. -/
theorem n06_finite_intervals_twoSided_cover
    {ι : Type*} (I : Finset ι) (l r : ι → ℝ) {a b t : ℝ}
    (hcover : ∀ᵐ x ∂volume, x ∈ Ioo a b → ∃ i ∈ I, x ∈ Ioo (l i) (r i))
    (ht : t ∈ Ioo a b) :
    (∃ i ∈ I, l i < t ∧ t ≤ r i) ∧
      (∃ j ∈ I, l j ≤ t ∧ t < r j) := by
  classical
  let IL := I.filter (fun i => l i < t)
  let IR := I.filter (fun i => t < r i)
  have hleft : ∀ᵐ x ∂volume, x ∈ Ioo a t →
      x ∈ ⋃ i ∈ IL, Icc (l i) (r i) := by
    filter_upwards [hcover] with x hx hxt
    obtain ⟨i, hi, hxi⟩ := hx ⟨hxt.1, hxt.2.trans ht.2⟩
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hxi.1.trans hxt.2⟩,
      Ioo_subset_Icc_self hxi⟩
  have hright : ∀ᵐ x ∂volume, x ∈ Ioo t b →
      x ∈ ⋃ i ∈ IR, Icc (l i) (r i) := by
    filter_upwards [hcover] with x hx hxt
    obtain ⟨i, hi, hxi⟩ := hx ⟨ht.1.trans hxt.1, hxt.2⟩
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hxt.1.trans hxi.2⟩,
      Ioo_subset_Icc_self hxi⟩
  have hlclosed : IsClosed (⋃ i ∈ IL, Icc (l i) (r i)) :=
    isClosed_biUnion_finset (fun _ _ => isClosed_Icc)
  have hrclosed : IsClosed (⋃ i ∈ IR, Icc (l i) (r i)) :=
    isClosed_biUnion_finset (fun _ _ => isClosed_Icc)
  obtain ⟨i, hi, hti⟩ := mem_iUnion₂.mp
    (n06_closed_contains_interval_of_ae ht.1 hlclosed hleft ⟨ht.1.le, le_rfl⟩)
  obtain ⟨j, hj, htj⟩ := mem_iUnion₂.mp
    (n06_closed_contains_interval_of_ae ht.2 hrclosed hright ⟨le_rfl, ht.2.le⟩)
  exact ⟨⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2, hti.2⟩,
    ⟨j, (Finset.mem_filter.mp hj).1, htj.1, (Finset.mem_filter.mp hj).2⟩⟩

/-- The actual right endpoints of pairwise disjoint nonempty intervals
are distinct, just as their left endpoints are. -/
theorem n06_disjoint_intervals_right_injective {ι : Type*} {l r : ι → ℝ}
    (hlr : ∀ i, l i < r i)
    (hdisjoint : Pairwise (fun i j => Disjoint (Ioo (l i) (r i)) (Ioo (l j) (r j)))) :
    Function.Injective r := by
  intro i j hij
  by_contra hne
  have hsmall : max (l i) (l j) < r i :=
    max_lt (hlr i) ((hlr j).trans_le hij.symm.le)
  obtain ⟨x, hx, hxr⟩ := exists_between hsmall
  exact Set.disjoint_left.mp (hdisjoint hne)
    ⟨(le_max_left _ _).trans_lt hx, hxr⟩
    ⟨(le_max_right _ _).trans_lt hx, hxr.trans_le hij.le⟩

/-- Every interior right endpoint has one actual right-hand neighbor;
the a.e. cover rules out even a single unfilled gap. -/
theorem n06_finite_intervals_right_neighbor
    {ι : Type*} (I : Finset ι) (l r : ι → ℝ) {a b : ℝ}
    (hlr : ∀ i, l i < r i)
    (hdisjoint : Pairwise (fun i j => Disjoint (Ioo (l i) (r i)) (Ioo (l j) (r j))))
    (hcover : ∀ᵐ x ∂volume, x ∈ Ioo a b → ∃ i ∈ I, x ∈ Ioo (l i) (r i))
    (i : ι) (ht : r i ∈ Ioo a b) :
    ∃! j, j ∈ I ∧ l j = r i := by
  obtain ⟨j, hj, hlj, hrj⟩ := (n06_finite_intervals_twoSided_cover I l r hcover ht).2
  have hij : i ≠ j := by
    intro he
    subst j
    exact (lt_irrefl _ hrj)
  have hd := (Ioo_disjoint_Ioo.mp (hdisjoint hij))
  rw [min_eq_left hrj.le] at hd
  have hri : r i ≤ l j := by
    rcases le_max_iff.mp hd with h | h
    · exact False.elim ((not_le_of_gt (hlr i)) h)
    · exact h
  have he : l j = r i := le_antisymm hlj hri
  refine ⟨j, ⟨hj, he⟩, ?_⟩
  intro k hk
  exact n06_disjoint_intervals_left_injective hlr hdisjoint (hk.2.trans he.symm)

/-- The same finite cover supplies the unique actual left-hand neighbor
of every interior left endpoint. -/
theorem n06_finite_intervals_left_neighbor
    {ι : Type*} (I : Finset ι) (l r : ι → ℝ) {a b : ℝ}
    (hlr : ∀ i, l i < r i)
    (hdisjoint : Pairwise (fun i j => Disjoint (Ioo (l i) (r i)) (Ioo (l j) (r j))))
    (hcover : ∀ᵐ x ∂volume, x ∈ Ioo a b → ∃ i ∈ I, x ∈ Ioo (l i) (r i))
    (j : ι) (ht : l j ∈ Ioo a b) :
    ∃! i, i ∈ I ∧ r i = l j := by
  obtain ⟨i, hi, hli, hri⟩ := (n06_finite_intervals_twoSided_cover I l r hcover ht).1
  have hij : i ≠ j := by
    intro he
    subst i
    exact (lt_irrefl _ hli)
  have hd := (Ioo_disjoint_Ioo.mp (hdisjoint hij))
  rw [max_eq_right hli.le] at hd
  have hril : r i ≤ l j := by
    rcases min_le_iff.mp hd with h | h
    · exact h
    · exact False.elim ((not_le_of_gt (hlr j)) h)
  have he : r i = l j := le_antisymm hril hri
  refine ⟨i, ⟨hi, he⟩, ?_⟩
  intro k hk
  exact n06_disjoint_intervals_right_injective hlr hdisjoint (hk.2.trans he.symm)

/-- Actual matching of the two boundary values, together with their
vanishing outside the test window, cancels the entire finite sum. The
neighbors and their bijection are proved from the cover above. -/
theorem n06_finite_atlas_boundary_sum
    {ι G : Type*} [AddCommGroup G]
    (I : Finset ι) (l r : ι → ℝ) {a b : ℝ}
    (hlr : ∀ i, l i < r i)
    (hdisjoint : Pairwise (fun i j => Disjoint (Ioo (l i) (r i)) (Ioo (l j) (r j))))
    (hcover : ∀ᵐ x ∂volume, x ∈ Ioo a b → ∃ i ∈ I, x ∈ Ioo (l i) (r i))
    (BL BR : ι → G)
    (hmatch : ∀ i ∈ I, ∀ j ∈ I, r i = l j → BR i = BL j)
    (hLzero : ∀ i ∈ I, l i ∉ Ioo a b → BL i = 0)
    (hRzero : ∀ i ∈ I, r i ∉ Ioo a b → BR i = 0) :
    (∑ i ∈ I, (BR i - BL i)) = 0 := by
  classical
  let IR := I.filter (fun i => r i ∈ Ioo a b)
  let IL := I.filter (fun i => l i ∈ Ioo a b)
  have hnext : ∀ i ∈ IR, ∃ j ∈ IL, l j = r i := by
    intro i hi
    obtain ⟨j, hj, _⟩ := n06_finite_intervals_right_neighbor I l r hlr hdisjoint hcover i
      (Finset.mem_filter.mp hi).2
    have hjwindow : l j ∈ Ioo a b := by
      rw [hj.2]
      exact (Finset.mem_filter.mp hi).2
    exact ⟨j, Finset.mem_filter.mpr ⟨hj.1, hjwindow⟩, hj.2⟩
  choose neighbor hnext_mem hnext_eq using hnext
  have hbij : (∑ i ∈ IR, BR i) = ∑ j ∈ IL, BL j := by
    apply Finset.sum_bij neighbor hnext_mem
    · intro i hi j hj he
      apply n06_disjoint_intervals_right_injective hlr hdisjoint
      exact (hnext_eq i hi).symm.trans ((congrArg l he).trans (hnext_eq j hj))
    · intro j hj
      obtain ⟨i, hi, _⟩ := n06_finite_intervals_left_neighbor I l r hlr hdisjoint hcover j
        (Finset.mem_filter.mp hj).2
      have hiwindow : r i ∈ Ioo a b := by
        rw [hi.2]
        exact (Finset.mem_filter.mp hj).2
      have hiR : i ∈ IR := Finset.mem_filter.mpr ⟨hi.1, hiwindow⟩
      refine ⟨i, hiR, ?_⟩
      exact n06_disjoint_intervals_left_injective hlr hdisjoint
        ((hnext_eq i hiR).trans hi.2)
    · intro i hi
      exact hmatch i (Finset.mem_filter.mp hi).1 (neighbor i hi)
        (Finset.mem_filter.mp (hnext_mem i hi)).1 (hnext_eq i hi).symm
  have hsumR : (∑ i ∈ IR, BR i) = ∑ i ∈ I, BR i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hn
    apply hRzero i hi
    intro ht
    exact hn (Finset.mem_filter.mpr ⟨hi, ht⟩)
  have hsumL : (∑ i ∈ IL, BL i) = ∑ i ∈ I, BL i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hn
    apply hLzero i hi
    intro ht
    exact hn (Finset.mem_filter.mpr ⟨hi, ht⟩)
  rw [Finset.sum_sub_distrib, ← hsumR, ← hsumL, hbij, sub_self]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- The N04 reference a.e. cover restricts to the precise finite collection
of reference intervals meeting a compact radial window. -/
theorem n06_finitePhysicalWindow_cover_ae
    (h04 : N04Properties D T S C L K base loss ε)
    {a b : ℝ} (hwindow : Icc a b ⊆ radialCore D)
    (hfinite : {m : ℕ |
      (Ioo (K.physicalLeft m) (K.physicalRight m) ∩ Icc a b).Nonempty}.Finite) :
    ∀ᵐ r ∂volume, r ∈ Ioo a b → ∃ m ∈ hfinite.toFinset,
      r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) := by
  obtain ⟨E, hE, hcover⟩ := h04.1.referencePartition
  have havoid : ∀ᵐ r ∂volume, r ∉ E := by
    apply ae_iff.mpr
    exact measure_mono_null (fun _ hr => Classical.not_not.mp hr) hE
  filter_upwards [havoid] with r hr hri
  obtain ⟨m, hm, _⟩ := hcover r ⟨hwindow (Ioo_subset_Icc_self hri), hr⟩
  exact ⟨m, hfinite.mem_toFinset.mpr ⟨r, hm, Ioo_subset_Icc_self hri⟩, hm⟩

/-- A finite set of reference intervals has a vanishing boundary sum
whenever its rows match on adjacent indices. The reference cover supplies
those indices and their uniqueness; no current rectangular domain is used. -/
theorem n06_finitePhysicalWindow_boundary_sum
    {G : Type*} [AddCommGroup G]
    (h04 : N04Properties D T S C L K base loss ε)
    {a b : ℝ} (hwindow : Icc a b ⊆ radialCore D)
    (hfinite : {m : ℕ |
      (Ioo (K.physicalLeft m) (K.physicalRight m) ∩ Icc a b).Nonempty}.Finite)
    (BL BR : ℕ → G)
    (hmatch : ∀ i ∈ hfinite.toFinset, ∀ j ∈ hfinite.toFinset,
      K.physicalRight i = K.physicalLeft j → BR i = BL j)
    (hLzero : ∀ i ∈ hfinite.toFinset, K.physicalLeft i ∉ Ioo a b → BL i = 0)
    (hRzero : ∀ i ∈ hfinite.toFinset, K.physicalRight i ∉ Ioo a b → BR i = 0) :
    (∑ i ∈ hfinite.toFinset, (BR i - BL i)) = 0 :=
  n06_finite_atlas_boundary_sum hfinite.toFinset K.physicalLeft K.physicalRight
    (fun i => (h04.1.referenceBounds i).1) (n06_physicalPiece_pairwiseDisjoint h04)
    (n06_finitePhysicalWindow_cover_ae h04 hwindow hfinite) BL BR hmatch hLzero hRzero

/-- Compact finiteness is obtained from the original accumulating profile
and controlled reference atlas, so the collection is not an additional
partition supplied to the cancellation theorem. -/
theorem n06_controlledPhysicalWindow_boundary_sum
    {G : Type*} [AddCommGroup G]
    (hD : IsAccumulatingProfile D)
    (hcoords : N05ControlledReferenceCoordinates D S C K)
    (h04 : N04Properties D T S C L K base loss ε)
    {a b : ℝ} (hwindow : Icc a b ⊆ radialCore D) :
    ∃ I : Finset ℕ,
      (∀ m, m ∈ I ↔ (Ioo (K.physicalLeft m) (K.physicalRight m) ∩ Icc a b).Nonempty) ∧
      ∀ BL BR : ℕ → G,
        (∀ i ∈ I, ∀ j ∈ I, K.physicalRight i = K.physicalLeft j → BR i = BL j) →
        (∀ i ∈ I, K.physicalLeft i ∉ Ioo a b → BL i = 0) →
        (∀ i ∈ I, K.physicalRight i ∉ Ioo a b → BR i = 0) →
        (∑ i ∈ I, (BR i - BL i)) = 0 := by
  classical
  have hfinite := n06_controlledReferencePieces_finite_on_compact hD hcoords isCompact_Icc hwindow
  exact ⟨hfinite.toFinset, fun _ => hfinite.mem_toFinset, fun BL BR hmatch hL hR =>
    n06_finitePhysicalWindow_boundary_sum h04 hwindow hfinite BL BR hmatch hL hR⟩

end ContinuousFlexibility.Statements
