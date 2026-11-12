import ContinuousFlexibility.Analysis.N06FinitePhysicalPartition

/-!
# A finite support envelope containing both halves of every cut

Reference intervals are used only as indices. The envelope adds both
indices of every original negative component meeting the support window.
It contains all actual current pieces meeting that window, uniformly in
the admitted state, and is saturated under the genuine cut pairing.

The additional indices do not alter physical/canonical test pairings:
when an actual current piece misses the physical support, both actual
canonical test transforms vanish throughout its open cylinder.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- The reference interval indices meeting a radial window. -/
def n06ReferenceSupportPieces (K : CanonicalData S) (J : Set ℝ) : Set ℕ :=
  {m | (Ioo (K.physicalLeft m) (K.physicalRight m) ∩ J).Nonempty}

/-- Original negative components whose closures meet the same window. -/
def n06ControlSupportComponents (C : NonlinearGeometryData S) (J : Set ℝ) : Set ℕ :=
  {n | (Icc (C.left n) (C.right n) ∩ J).Nonempty}

/-- A state-independent finite envelope. A component contributes both
cut halves, regardless of the current position of its middle curve. -/
def n06CutSaturatedSupport (C : NonlinearGeometryData S) (K : CanonicalData S)
    (J : Set ℝ) : Set ℕ :=
  n06ReferenceSupportPieces K J ∪
    ((fun n => (K.cutPair n).1) '' n06ControlSupportComponents C J ∪
      (fun n => (K.cutPair n).2) '' n06ControlSupportComponents C J)

/-- All indices in the envelope are finite by the original profile,
control components, and controlled reference coordinates. -/
theorem n06_cutSaturatedSupport_finite
    (hD : IsAccumulatingProfile D) (hC : controlGeometryConditions D S C)
    (hcoords : N05ControlledReferenceCoordinates D S C K)
    {J : Set ℝ} (hJ : IsCompact J) (hJD : J ⊆ radialCore D) :
    (n06CutSaturatedSupport C K J).Finite := by
  have href : (n06ReferenceSupportPieces K J).Finite :=
    n06_controlledReferencePieces_finite_on_compact hD hcoords hJ hJD
  have hcomponents : (n06ControlSupportComponents C J).Finite :=
    n06_controlComponents_finite_on_compact hD.choose_spec.1 hC hJ hJD
  exact href.union ((hcomponents.image (fun n => (K.cutPair n).1)).union
    (hcomponents.image (fun n => (K.cutPair n).2)))

private theorem n06_referenceCutHalf_interval_subset_component
    (h04 : N04Properties D T S C L K base loss ε)
    {n i : ℕ} (hi : i = (K.cutPair n).1 ∨ i = (K.cutPair n).2) :
    Ioo (K.physicalLeft i) (K.physicalRight i) ⊆ Ioo (C.left n) (C.right n) := by
  have hsub : Icc (K.physicalLeft i) (K.physicalRight i) ⊆
      Icc (C.left n) (C.right n) := by
    rcases hi with rfl | rfl
    · exact (n06_cutHalf_closed_subset_component h04 n).1
    · exact (n06_cutHalf_closed_subset_component h04 n).2
  have hlo : C.left n ≤ K.physicalLeft i :=
    (hsub ⟨le_rfl, (h04.1.referenceBounds i).1.le⟩).1
  have hhi : K.physicalRight i ≤ C.right n :=
    (hsub ⟨(h04.1.referenceBounds i).1.le, le_rfl⟩).2
  exact fun _ hx => ⟨hlo.trans_lt hx.1, hx.2.trans_le hhi⟩

/-- A reference half cannot belong to two different original negative
components. This follows from their genuine disjoint open intervals. -/
theorem n06_cutHalf_component_eq
    (hC : controlGeometryConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    {n k i : ℕ}
    (hn : i = (K.cutPair n).1 ∨ i = (K.cutPair n).2)
    (hk : i = (K.cutPair k).1 ∨ i = (K.cutPair k).2) : n = k := by
  by_contra hne
  obtain ⟨r, hr⟩ := Set.nonempty_Ioo.mpr (h04.1.referenceBounds i).1
  exact Set.disjoint_left.mp (hC.2.2.1 n k hne)
    (n06_referenceCutHalf_interval_subset_component h04 hn hr)
    (n06_referenceCutHalf_interval_subset_component h04 hk hr)

/-- Each cut half belongs to the envelope exactly when its original
closed component meets the window. This also handles duplicate image
witnesses in the two finite image sets. -/
theorem n06_mem_cutSaturatedSupport_cutHalf_iff
    (hC : controlGeometryConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    {J : Set ℝ} {n i : ℕ}
    (hi : i = (K.cutPair n).1 ∨ i = (K.cutPair n).2) :
    i ∈ n06CutSaturatedSupport C K J ↔ n ∈ n06ControlSupportComponents C J := by
  constructor
  · intro hm
    rcases hm with href | hleft | hright
    · obtain ⟨r, hr, hrJ⟩ := href
      exact ⟨r, Ioo_subset_Icc_self
        (n06_referenceCutHalf_interval_subset_component h04 hi hr), hrJ⟩
    · obtain ⟨k, hk, hki⟩ := hleft
      have he : k = n := n06_cutHalf_component_eq hC h04 (Or.inl hki.symm) hi
      simpa only [he] using hk
    · obtain ⟨k, hk, hki⟩ := hright
      have he : k = n := n06_cutHalf_component_eq hC h04 (Or.inr hki.symm) hi
      simpa only [he] using hk
  · intro hn
    rcases hi with rfl | rfl
    · exact Or.inr (Or.inl ⟨n, hn, rfl⟩)
    · exact Or.inr (Or.inr ⟨n, hn, rfl⟩)

/-- No artificial cut is left unpaired in this envelope. -/
theorem n06_cutSaturatedSupport_pair_iff
    (hC : controlGeometryConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (J : Set ℝ) (n : ℕ) :
    (K.cutPair n).1 ∈ n06CutSaturatedSupport C K J ↔
      (K.cutPair n).2 ∈ n06CutSaturatedSupport C K J :=
  (n06_mem_cutSaturatedSupport_cutHalf_iff hC h04 (J := J) (n := n)
    (i := (K.cutPair n).1) (Or.inl rfl)).trans
    (n06_mem_cutSaturatedSupport_cutHalf_iff hC h04 (J := J) (n := n)
      (i := (K.cutPair n).2) (Or.inr rfl)).symm

/-- Every actual current piece meeting the physical support belongs to
the same reference/component envelope. The proof uses the actual planar
component inclusion, not a fixed current radial cut. -/
theorem n06_physicalSupportPieces_subset_cutSaturatedSupport
    (hC : controlGeometryConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (J : Set ℝ) :
    n06PhysicalSupportPieces K z J ⊆ n06CutSaturatedSupport C K J := by
  intro m hm
  obtain ⟨p, hp, hpJ⟩ := hm
  cases hpositive : K.positive m with
  | true =>
      have hdomain := (h04.1.domains z hz hs m).2.2.2.2.2.1 hpositive
      rw [hdomain] at hp
      exact Or.inl ⟨p.1, hp.1, hpJ.1⟩
  | false =>
      obtain ⟨n, hn⟩ := n06_negativePiece_is_cutHalf h04 hC hpositive
      have hpc : p ∈ Ioo (C.left n) (C.right n) ×ˢ (univ : Set ℝ) := by
        rcases hn with hleft | hright
        · rw [hleft] at hp
          exact (n06_currentCutHalf_subset_component h04 hz hs n).1 hp
        · rw [hright] at hp
          exact (n06_currentCutHalf_subset_component h04 hz hs n).2 hp
      apply (n06_mem_cutSaturatedSupport_cutHalf_iff hC h04 hn).2
      exact ⟨p.1, Ioo_subset_Icc_self hpc.1, hpJ.1⟩

/-- The reference indices are included without modifying their meaning. -/
theorem n06_referenceSupportPieces_subset_cutSaturatedSupport (J : Set ℝ) :
    n06ReferenceSupportPieces K J ⊆ n06CutSaturatedSupport C K J :=
  fun _ hm => Or.inl hm

/-- A physical test vanishing off its original support has both actual
canonical transforms identically zero on every current piece missing
that support. No regularity of the test or of a represented field is needed. -/
theorem n06_canonicalTransforms_zero_off_physicalSupport
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {J : Set ℝ} {φ : PolarPoint → ℝ}
    (hzero : ∀ r, r ∉ J → ∀ θ, φ (r, θ) = 0)
    {m : ℕ} (hm : m ∉ n06PhysicalSupportPieces K z J) :
    EqOn (canonicalHeight S K z m φ) (fun _ => 0) (canonicalOpen S K m) ∧
      EqOn (canonicalSource S K z m φ) (fun _ => 0) (canonicalOpen S K m) := by
  have htest (p : PolarPoint) (hp : p ∈ canonicalOpen S K m) :
      φ (K.inverseChart z m p) = 0 := by
    have hx := (h04.1.charts z hz hs m).2.1 hp
    have hxJ : (K.inverseChart z m p).1 ∉ J := by
      intro hJ
      exact hm ⟨K.inverseChart z m p, hx, hJ, mem_univ _⟩
    exact hzero _ hxJ _
  constructor
  · intro p hp
    simp only [canonicalHeight, htest p hp, zero_div]
  · intro p hp
    simp only [canonicalSource, htest p hp, mul_zero, zero_div]

/-- In particular every extra piece contributes zero to either actual
canonical pairing, before any integrability assumptions are imposed. -/
theorem n06_canonicalPairings_zero_off_physicalSupport
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {J : Set ℝ} {φ : PolarPoint → ℝ}
    (hzero : ∀ r, r ∉ J → ∀ θ, φ (r, θ) = 0)
    {m : ℕ} (hm : m ∉ n06PhysicalSupportPieces K z J) (W : PolarPoint → ℝ) :
    (∫ p, W p * canonicalHeight S K z m φ p ∂canonicalMeasure S K m) = 0 ∧
      (∫ p, W p * canonicalSource S K z m φ p ∂canonicalMeasure S K m) = 0 := by
  have hztest := n06_canonicalTransforms_zero_off_physicalSupport h04 hz hs hzero hm
  have hH : (fun p => W p * canonicalHeight S K z m φ p) =ᵐ[canonicalMeasure S K m]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    rw [hztest.1 ⟨hp.1, mem_univ _⟩, mul_zero]
  have hS : (fun p => W p * canonicalSource S K z m φ p) =ᵐ[canonicalMeasure S K m]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    rw [hztest.2 ⟨hp.1, mem_univ _⟩, mul_zero]
  exact ⟨(integral_congr_ae hH).trans (by simp),
    (integral_congr_ae hS).trans (by simp)⟩

/-- Enlarging the actual support set to any finite envelope changes
neither pairing. This is the exact zero-padding step used by cut-saturated
Green sums, with the original canonical measure and original test. -/
theorem n06_canonicalPairing_sums_eq_of_support_subset
    (h04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {J : Set ℝ}
    (hfinite : (n06PhysicalSupportPieces K z J).Finite)
    (I : Finset ℕ) (hsub : ∀ m ∈ n06PhysicalSupportPieces K z J, m ∈ I)
    (W : ℕ → PolarPoint → ℝ) {φ : PolarPoint → ℝ}
    (hzero : ∀ r, r ∉ J → ∀ θ, φ (r, θ) = 0) :
    (∑ m ∈ hfinite.toFinset,
      ∫ p, W m p * canonicalHeight S K z m φ p ∂canonicalMeasure S K m) =
        (∑ m ∈ I, ∫ p, W m p * canonicalHeight S K z m φ p ∂canonicalMeasure S K m) ∧
    (∑ m ∈ hfinite.toFinset,
      ∫ p, W m p * canonicalSource S K z m φ p ∂canonicalMeasure S K m) =
        (∑ m ∈ I, ∫ p, W m p * canonicalSource S K z m φ p ∂canonicalMeasure S K m) := by
  classical
  have hsub' : hfinite.toFinset ⊆ I := fun m hm => hsub m (hfinite.mem_toFinset.mp hm)
  constructor
  · apply Finset.sum_subset hsub'
    intro m _ hm
    exact (n06_canonicalPairings_zero_off_physicalSupport h04 hz hs hzero
      (fun h => hm (hfinite.mem_toFinset.mpr h)) (W m)).1
  · apply Finset.sum_subset hsub'
    intro m _ hm
    exact (n06_canonicalPairings_zero_off_physicalSupport h04 hz hs hzero
      (fun h => hm (hfinite.mem_toFinset.mpr h)) (W m)).2

end ContinuousFlexibility.Statements
