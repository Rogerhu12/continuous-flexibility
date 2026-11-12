import ContinuousFlexibility.Analysis.N01aPartitionGrouping
import ContinuousFlexibility.Analysis.N01aReferenceCoarseningBasic

/-!
# Partition and trace properties of the grouped cells

Finite fibers preserve smooth localizers, the partition of unity and the
overlap bound. One original sampling collar is retained in each group.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped BigOperators ContDiff

variable (D : ReferenceData) (p : ℕ → ℝ)
  (hproper : ∀ N : ℕ, {i | D.cellIndex i ≤ N}.Finite)

theorem n01aCoarseReference_coarsening :
    N01aReferenceCoarsening D (n01aCoarseReference D p hproper)
      (n01aCellGrouping D p hproper) where
  finite_fibers := n01aCellGrouping_fiber_finite D p hproper
  a_eq := rfl
  b_eq := rfl
  w_eq := rfl
  phi_eq := rfl
  chi_eq := rfl
  chiLeft_eq := rfl
  index_eq := n01aCellGroupIndex_grouping D p hproper
  localizer_eq := fun _ _ => rfl

theorem n01aCoarseReference_profileGeometry (hD : RadialProfileGeometry D) :
    RadialProfileGeometry (n01aCoarseReference D p hproper) := hD

theorem n01aCoarseReference_radialPartition (hD : RadialPartition D) :
    RadialPartition (n01aCoarseReference D p hproper) := by
  classical
  let σ := n01aCellGrouping D p hproper
  let hσ := n01aCellGrouping_fiber_finite D p hproper
  rcases hD with ⟨hsmooth, hnonneg, hsupport, hcore, hsum, B, hB⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, B, ?_⟩
  · intro j
    exact ContDiff.sum (fun i _ => hsmooth i)
  · intro j r
    exact n01aCoarseLocalizer_nonneg σ hσ D.localizer hnonneg j r
  · intro j r hr
    have hne : (∑ i ∈ n01aCoarseningFiber σ hσ j, D.localizer i r) ≠ 0 :=
      Function.mem_support.mp hr
    by_contra hout
    apply hne
    apply Finset.sum_eq_zero
    intro i hi
    by_contra hnot
    apply hout
    exact (n01aCoarseReference_mem_cell D p hproper j r).mpr
      ⟨i, (mem_n01aCoarseningFiber σ hσ i j).mp hi,
        hsupport i (Function.mem_support.mpr hnot)⟩
  · intro j r hr
    obtain ⟨i, _, hi⟩ := (n01aCoarseReference_mem_cell D p hproper j r).mp hr
    exact hcore i hi
  · intro r hr
    obtain ⟨hs, ht⟩ := hsum r hr
    refine ⟨(n01a_summable_fiber_sum_iff σ hσ (fun i => D.localizer i r)
      (fun i => hnonneg i r)).mpr hs, ?_⟩
    exact (n01a_tsum_coarsening_fiber_sum σ hσ hs).trans ht
  · intro r
    have hsub : {j | (n01aCoarseReference D p hproper).localizer j r ≠ 0} ⊆
        σ '' {i | D.localizer i r ≠ 0} := by
      intro j hj
      by_contra hout
      apply hj
      apply Finset.sum_eq_zero
      intro i hi
      by_contra hn
      exact hout ⟨i, hn, (mem_n01aCoarseningFiber σ hσ i j).mp hi⟩
    have himage := (hB r).1.image σ
    exact ⟨himage.subset hsub,
      (Set.ncard_le_ncard hsub himage).trans
        ((Set.ncard_image_le (hB r).1).trans (hB r).2)⟩

theorem n01aCoarseReference_locallyFiniteCells
    (hD : ∀ K : Set ℝ, IsCompact K → K ⊆ radialCore D →
      {i | (D.cells i ∩ K).Nonempty}.Finite) :
    ∀ K : Set ℝ, IsCompact K → K ⊆ radialCore (n01aCoarseReference D p hproper) →
      {j | ((n01aCoarseReference D p hproper).cells j ∩ K).Nonempty}.Finite := by
  intro K hK hcore
  apply ((hD K hK hcore).image (n01aCellGrouping D p hproper)).subset
  intro j hj
  obtain ⟨r, hr, hrK⟩ := hj
  obtain ⟨i, hij, hi⟩ := (n01aCoarseReference_mem_cell D p hproper j r).mp hr
  exact ⟨i, ⟨r, hi, hrK⟩, hij⟩

theorem n01aCoarseReference_traceScaffold (hD : RadialTraceScaffold D) :
    RadialTraceScaffold (n01aCoarseReference D p hproper) := by
  rcases hD with ⟨c, w, K, hK, hcell, hdisj⟩
  let rep := n01aCellRepresentative D p hproper
  have hrep (j : ℕ) : n01aCellGrouping D p hproper (rep j) = j :=
    n01aCellRepresentative_spec D p hproper j
  refine ⟨fun j => c (rep j), fun j => w (rep j), K, hK, ?_, ?_⟩
  · intro j
    have hsub : D.cells (rep j) ⊆ (n01aCoarseReference D p hproper).cells j := by
      simpa only [hrep] using n01aCoarseReference_cell_subset D p hproper (rep j)
    refine ⟨hsub (hcell (rep j)).1, (hcell (rep j)).2.1, ?_,
      (hcell (rep j)).2.2.2.trans hsub⟩
    rw [n01aCoarseReference_cellIndex D p hproper (rep j) j (hrep j)]
    exact (hcell (rep j)).2.2.1
  · intro i j hij
    exact hdisj ((n01aCellRepresentative_injective D p hproper).ne hij)

theorem n01aCoarseReference_naturalKernels (hD : RadialNaturalKernels D) :
    RadialNaturalKernels (n01aCoarseReference D p hproper) := hD

theorem n01aCoarseReference_trueBorder (hD : RadialTrueBorder D) :
    RadialTrueBorder (n01aCoarseReference D p hproper) := hD

theorem n01aCoarseReference_returnMargins (hD : RadialReturnMargins D) :
    RadialReturnMargins (n01aCoarseReference D p hproper) := by
  refine ⟨hD.1, ?_⟩
  obtain ⟨C, hC, hret⟩ := hD.2
  refine ⟨C, hC, ?_⟩
  intro l h hcomponent
  obtain ⟨hiq, m, hcell, c, hc, hbound, hsin⟩ := hret l h hcomponent
  refine ⟨hiq, n01aCellGrouping D p hproper m,
    hcell.trans (n01aCoarseReference_cell_subset D p hproper m), c, hc, ?_, hsin⟩
  rw [n01aCoarseReference_cellIndex D p hproper m _ rfl]
  exact hbound

end ContinuousFlexibility.Statements
