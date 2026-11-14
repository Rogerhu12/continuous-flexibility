import ContinuousFlexibility.Analysis.N04PositiveComponents
import ContinuousFlexibility.Analysis.IntervalWeakPrimitive

/-!
# Compact normalization support inside positive components

A compact subset of the positive region meets each component in a compact
set, even if the component touches an ambient endpoint. Each such set has
two nested interior interval buffers. The construction is entirely at the
reference state and is selected before any perturbed state.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

theorem n04PositiveComponent_closure_inter_region_subset
    {a b : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (i : N04PositiveComponent a b f) :
    closure i.val ∩ n04PositiveRegion a b f ⊆ i.val := by
  intro r hr
  obtain ⟨j, hrj, _⟩ := (n04PositiveComponent_existsUnique_mem_iff r).mpr hr.2
  obtain ⟨x, hxj, hxi⟩ := mem_closure_iff_nhds.mp hr.1 j.val
    ((n04PositiveComponent_isOpen hf j).mem_nhds hrj)
  have hij : i = j := Subtype.ext
    ((n04PositiveComponent_eq_component i hxi).trans
      (n04PositiveComponent_eq_component j hxj).symm)
  simpa only [hij] using hrj

theorem n04PositiveComponent_compact_inter
    {a b : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    {K : Set ℝ} (hK : IsCompact K) (hKP : K ⊆ n04PositiveRegion a b f)
    (i : N04PositiveComponent a b f) : IsCompact (K ∩ i.val) := by
  have he : K ∩ closure i.val = K ∩ i.val := by
    apply Subset.antisymm
    · intro r hr
      exact ⟨hr.1, n04PositiveComponent_closure_inter_region_subset hf i ⟨hr.2, hKP hr.1⟩⟩
    · exact fun _ hr => ⟨hr.1, subset_closure hr.2⟩
  rw [← he]
  exact hK.of_isClosed_subset (hK.isClosed.inter isClosed_closure) inter_subset_left

theorem n04PositiveComponent_exists_normalization_buffer
    {a b : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    {K : Set ℝ} (hK : IsCompact K) (hKP : K ⊆ n04PositiveRegion a b f)
    (i : N04PositiveComponent a b f) :
    ∃ c nL nR d : ℝ,
      n04PositiveLeft i < c ∧ c < nL ∧ nL < nR ∧ nR < d ∧ d < n04PositiveRight i ∧
        K ∩ i.val ⊆ Ioo nL nR := by
  have hab := (n04PositiveComponent_bounds hf i).2.1
  have hsub : K ∩ i.val ⊆ Ioo (n04PositiveLeft i) (n04PositiveRight i) := by
    intro r hr
    simpa only [n04PositiveComponent_eq_Ioo hf i] using hr.2
  obtain ⟨nL, nR, hl, hn, hr, hs⟩ := interval_compact_subset_Ioo hab
    (n04PositiveComponent_compact_inter hf hK hKP i) hsub
  obtain ⟨c, hc, hcn⟩ := exists_between hl
  obtain ⟨d, hnd, hd⟩ := exists_between hr
  exact ⟨c, nL, nR, d, hc, hcn, hn, hnd, hd, hs⟩

/-- Reference-only nested buffers; the central interval becomes one
positive piece and the smaller interval carries the normalization. -/
structure N04PositiveNormalizationBuffer
    (a b : ℝ) (f : ℝ → ℝ) (K : Set ℝ) where
  centerLeft : N04PositiveComponent a b f → ℝ
  normalizationLeft : N04PositiveComponent a b f → ℝ
  normalizationRight : N04PositiveComponent a b f → ℝ
  centerRight : N04PositiveComponent a b f → ℝ
  ordered : ∀ i,
    n04PositiveLeft i < centerLeft i ∧ centerLeft i < normalizationLeft i ∧
      normalizationLeft i < normalizationRight i ∧
      normalizationRight i < centerRight i ∧ centerRight i < n04PositiveRight i
  support : ∀ i, K ∩ i.val ⊆ Ioo (normalizationLeft i) (normalizationRight i)

theorem n04PositiveNormalizationBuffer_nonempty
    {a b : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    {K : Set ℝ} (hK : IsCompact K) (hKP : K ⊆ n04PositiveRegion a b f) :
    Nonempty (N04PositiveNormalizationBuffer a b f K) := by
  choose c nL nR d hc hcn hn hnd hd hs using
    n04PositiveComponent_exists_normalization_buffer hf hK hKP
  exact ⟨⟨c, nL, nR, d, fun i => ⟨hc i, hcn i, hn i, hnd i, hd i⟩, hs⟩⟩

def N04PositiveNormalizationBuffer.region
    {a b : ℝ} {f : ℝ → ℝ} {K : Set ℝ}
    (B : N04PositiveNormalizationBuffer a b f K) : Set ℝ :=
  ⋃ i, Ioo (B.normalizationLeft i) (B.normalizationRight i)

theorem N04PositiveNormalizationBuffer.region_isOpen
    {a b : ℝ} {f : ℝ → ℝ} {K : Set ℝ}
    (B : N04PositiveNormalizationBuffer a b f K) : IsOpen B.region :=
  isOpen_iUnion (fun _ => isOpen_Ioo)

theorem N04PositiveNormalizationBuffer.support_subset_region
    {a b : ℝ} {f : ℝ → ℝ} {K : Set ℝ}
    (B : N04PositiveNormalizationBuffer a b f K)
    (hKP : K ⊆ n04PositiveRegion a b f) : K ⊆ B.region := by
  intro r hr
  obtain ⟨i, hi, _⟩ := (n04PositiveComponent_existsUnique_mem_iff r).mpr (hKP hr)
  exact mem_iUnion.mpr ⟨i, B.support i ⟨hr, hi⟩⟩

theorem N04PositiveNormalizationBuffer.region_subset_positive
    {a b : ℝ} {f : ℝ → ℝ} {K : Set ℝ}
    (B : N04PositiveNormalizationBuffer a b f K) (hf : Continuous f) :
    B.region ⊆ n04PositiveRegion a b f := by
  intro r hr
  obtain ⟨i, hi⟩ := mem_iUnion.mp hr
  have ho := B.ordered i
  have hri : r ∈ i.val := (n04PositiveComponent_mem_iff hf i).mpr
    ⟨(ho.1.trans ho.2.1).trans hi.1,
      hi.2.trans (ho.2.2.2.1.trans ho.2.2.2.2)⟩
  exact n04PositiveComponent_subset i hri

end ContinuousFlexibility.Analysis
