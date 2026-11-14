module

public import ContinuousFlexibility.Radial.R11bWeightEmbedding
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Recovering physical local L² from radial cell data

The partition reconstructs the actual field on each compact radial set using
only finitely many cells.  Thus the local MemLp conditions imply local physical
L² membership, without making any assumption about signs or measurability of
the unlocalized representative.  Continuous left-tail terms can then be added
back to recover an output field.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open ContinuousFlexibility.Statements

theorem r11b_radialPhysicalMeasure_finite (D : ReferenceData) :
    radialPhysicalMeasure D Set.univ < ⊤ := by
  unfold radialPhysicalMeasure
  rw [Measure.restrict_apply_univ]
  exact (measure_mono (Set.prod_mono Ioo_subset_Icc_self Ioc_subset_Icc_self)).trans_lt
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top

/-- Every continuous field has finite physical L² norm on the bounded annulus. -/
theorem r11b_continuous_memLp {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : Continuous f) : MemLp f 2 (radialPhysicalMeasure D) := by
  let K : Set PolarPoint := Icc D.a D.b ×ˢ Icc (0 : ℝ) (2 * Real.pi)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  letI : IsFiniteMeasure (radialPhysicalMeasure D) :=
    ⟨r11b_radialPhysicalMeasure_finite D⟩
  obtain ⟨M, hM⟩ := hK.bddAbove_image hf.norm.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable M
  have hstrip : ∀ᵐ x ∂radialPhysicalMeasure D,
      x ∈ radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi) :=
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
  exact hstrip.mono fun x hx =>
    hM ⟨x, ⟨Ioo_subset_Icc_self hx.1, Ioc_subset_Icc_self hx.2⟩, rfl⟩

/-- A compact cell cover reconstructs the partition by a finite sum. -/
theorem r11b_partition_finset_on {D : ReferenceData} (hpart : RadialPartition D)
    {K : Set ℝ} (hKcore : K ⊆ radialCore D)
    (hfinite : Set.Finite {m : ℕ | (D.cells m ∩ K).Nonempty}) :
    ∃ s : Finset ℕ, ∀ r ∈ K, (∑ m ∈ s, D.localizer m r) = 1 := by
  classical
  rcases hpart with ⟨_, _, hsupp, _, hsum, _⟩
  let s : Finset ℕ := hfinite.toFinset
  have hzero : ∀ r ∈ K, ∀ m ∉ s, D.localizer m r = 0 := by
    intro r hr m hm
    by_contra hne
    have hrm : r ∈ D.cells m := hsupp m hne
    have hmem : m ∈ s := hfinite.mem_toFinset.mpr ⟨r, hrm, hr⟩
    exact hm hmem
  refine ⟨s, fun r hr => ?_⟩
  calc (∑ m ∈ s, D.localizer m r) = ∑' m, D.localizer m r :=
      (tsum_eq_sum (s := s) (fun m hm => hzero r hr m hm)).symm
    _ = 1 := (hsum r (hKcore hr)).2

/-- Local physical L² membership follows from the actual localized fields. -/
theorem r11b_cell_memLp_on_compact {D : ReferenceData} (hpart : RadialPartition D)
    {K : Set ℝ} (hK : IsCompact K) (hKcore : K ⊆ radialCore D)
    (hfinite : Set.Finite {m : ℕ | (D.cells m ∩ K).Nonempty})
    {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f) :
    MemLp f 2 ((radialPhysicalMeasure D).restrict (K ×ˢ (Set.univ : Set ℝ))) := by
  classical
  obtain ⟨s, hsum⟩ := r11b_partition_finset_on hpart hKcore hfinite
  have hfiniteLp : MemLp (fun x : PolarPoint => ∑ m ∈ s, D.localizer m x.1 * f x) 2
      ((radialPhysicalMeasure D).restrict (K ×ˢ (Set.univ : Set ℝ))) :=
    memLp_finsetSum s (fun m _ => MemLp.mono_measure Measure.restrict_le_self (hf m))
  apply MemLp.ae_eq _ hfiniteLp
  filter_upwards [ae_restrict_mem (hK.isClosed.measurableSet.prod MeasurableSet.univ)] with x hx
  calc (∑ m ∈ s, D.localizer m x.1 * f x) =
        (∑ m ∈ s, D.localizer m x.1) * f x := (Finset.sum_mul s _ _).symm
    _ = f x := by rw [hsum x.1 hx.1, one_mul]

theorem r11b_cell_memLp_on_compact_of_profile {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {K : Set ℝ} (hK : IsCompact K)
    (hKcore : K ⊆ radialCore D) {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f) :
    MemLp f 2 ((radialPhysicalMeasure D).restrict (K ×ˢ (Set.univ : Set ℝ))) := by
  obtain ⟨C, _, hpart, _, _, _, hcompact, _⟩ := hD
  exact r11b_cell_memLp_on_compact hpart hK hKcore (hcompact K hK hKcore) hf

theorem r11b_source_memLp_on_compact {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {K : Set ℝ} (hK : IsCompact K)
    (hKcore : K ⊆ radialCore D) {γ M : ℝ} {F : RadialSource}
    (hF : SourceMember D γ M F) :
    MemLp F.1 2 ((radialPhysicalMeasure D).restrict (K ×ˢ (Set.univ : Set ℝ))) :=
  r11b_cell_memLp_on_compact_of_profile hD hK hKcore hF.1

theorem r11b_sourceDerivative_memLp_on_compact {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {K : Set ℝ} (hK : IsCompact K)
    (hKcore : K ⊆ radialCore D) {γ M : ℝ} {fθ : PolarPoint → ℝ}
    (hfθ : SourceDerivativeMember D γ M fθ) :
    MemLp fθ 2 ((radialPhysicalMeasure D).restrict (K ×ˢ (Set.univ : Set ℝ))) :=
  r11b_cell_memLp_on_compact_of_profile hD hK hKcore hfθ.1

/-- Recovering an output adds back the same smooth left-tail term. -/
theorem r11b_output_memLp_on_compact {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {K : Set ℝ} (hK : IsCompact K) (hKcore : K ⊆ radialCore D)
    {γ M : ℝ} {U : RadialUnknown} (hU : OutputMember D γ M U) :
    MemLp U.1 2 ((radialPhysicalMeasure D).restrict (K ×ˢ (Set.univ : Set ℝ))) := by
  obtain ⟨aL, hU⟩ := hU
  have hrem := r11b_cell_memLp_on_compact_of_profile hD hK hKcore hU.1
  have hleft : Continuous (fun x : PolarPoint => aL * D.chiLeft x.1) :=
    continuous_const.mul (hborder.2.2.2.2.1.continuous.comp continuous_fst)
  have hleftLp := MemLp.mono_measure
    (μ := radialPhysicalMeasure D)
    (ν := (radialPhysicalMeasure D).restrict (K ×ˢ (Set.univ : Set ℝ)))
    Measure.restrict_le_self (r11b_continuous_memLp hleft)
  apply MemLp.ae_eq _ (hrem.add hleftLp)
  exact Filter.Eventually.of_forall fun x =>
    sub_add_cancel (U.1 x) (aL * D.chiLeft x.1)

end ContinuousFlexibility.Radial
