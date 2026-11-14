module

public import ContinuousFlexibility.Radial.MatchedPhysicalCellOperators
public import ContinuousFlexibility.Radial.MatchedPartitionReconstruction

/-!
# Physical inputs for the actual block reconstruction

The input in cell m is chi_m f divided by the actual square partition.
Its norm costs one uniform overlap factor relative to chi_m f. Applying
the genuine density conversion and cell map gives precisely the modal
partition piece. The resulting finite block applications converge to the
existing operator, including one separate scalar border contribution.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ENNReal
open ContinuousFlexibility.Statements

theorem matchedPhysical_localized_memLp {D : ReferenceData}
    (hP : RadialPartition D) (m : ℕ) (f : MatchedPhysicalL2 D) :
    MemLp (fun r => D.localizer m r * f r) 2 (volume.restrict (radialCore D)) := by
  apply (Lp.memLp f).of_le
    ((hP.1 m).continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  filter_upwards with r
  simp only [Pi.mul_apply]
  rw [norm_mul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (matchedRadialLocalizer_abs_le_one hP m r)
    (norm_nonneg (f r))).trans_eq (one_mul _)

theorem matchedPartitionReciprocal_memLp_top {D : ReferenceData}
    (hP : RadialPartition D) :
    MemLp (fun r => (matchedPartitionSquare D r)⁻¹) ∞
      (volume.restrict (radialCore D)) := by
  obtain ⟨B, _, hB⟩ := exists_matchedPartitionSquare_inv_bound hP
  apply memLp_top_of_bound
    (matchedPartitionSquare_measurable hP).inv.aestronglyMeasurable B
  filter_upwards [ae_restrict_mem (show MeasurableSet (radialCore D) from measurableSet_Ioo)]
    with r hr
  simp only [Pi.inv_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg
    (inv_nonneg.mpr (matchedPartitionSquare_nonneg D r))]
  exact hB r hr

theorem matchedPhysicalPartitionInput_memLp {D : ReferenceData}
    (hP : RadialPartition D) (m : ℕ) (f : MatchedPhysicalL2 D) :
    MemLp (fun r => D.localizer m r * f r / matchedPartitionSquare D r) 2
      (volume.restrict (radialCore D)) := by
  have hh : MemLp (fun r =>
      (matchedPartitionSquare D r)⁻¹ * (D.localizer m r * f r)) 2
      (volume.restrict (radialCore D)) :=
    (matchedPartitionReciprocal_memLp_top hP).fun_mul
      (matchedPhysical_localized_memLp hP m f)
  apply (memLp_congr_ae ?_).mp hh
  filter_upwards with r
  change (matchedPartitionSquare D r)⁻¹ * (D.localizer m r * f r) =
    D.localizer m r * f r / matchedPartitionSquare D r
  rw [div_eq_mul_inv]
  ring

def matchedPhysicalPartitionInput (D : ReferenceData) (hP : RadialPartition D)
    (m : ℕ) (f : MatchedPhysicalL2 D) : MatchedPhysicalL2 D :=
  (matchedPhysicalPartitionInput_memLp hP m f).toLp
    (fun r => D.localizer m r * f r / matchedPartitionSquare D r)

theorem matchedPhysicalPartitionInput_ae (D : ReferenceData)
    (hP : RadialPartition D) (m : ℕ) (f : MatchedPhysicalL2 D) :
    (matchedPhysicalPartitionInput D hP m f : ℝ → ℝ)
      =ᵐ[volume.restrict (radialCore D)]
        fun r => D.localizer m r * f r / matchedPartitionSquare D r :=
  (matchedPhysicalPartitionInput_memLp hP m f).coeFn_toLp

theorem matchedPhysicalPartitionInput_norm_sq_le {D : ReferenceData}
    (hP : RadialPartition D) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ r ∈ radialCore D, (matchedPartitionSquare D r)⁻¹ ≤ B)
    (m : ℕ) (f : MatchedPhysicalL2 D) :
    ‖matchedPhysicalPartitionInput D hP m f‖ ^ 2 ≤
      B ^ 2 * ∫ r, (D.localizer m r * f r) ^ 2 ∂volume.restrict (radialCore D) := by
  have he :
      ‖matchedPhysicalPartitionInput D hP m f‖ ^ 2 =
        ∫ r, (D.localizer m r * f r / matchedPartitionSquare D r) ^ 2
          ∂volume.restrict (radialCore D) := by
    rw [matchedL2_norm_sq]
    apply integral_congr_ae
    filter_upwards [matchedPhysicalPartitionInput_ae D hP m f] with r hr
    rw [hr]
  rw [he, ← integral_const_mul]
  apply integral_mono_ae (matchedPhysicalPartitionInput_memLp hP m f).integrable_sq
    ((matchedPhysical_localized_memLp hP m f).integrable_sq.const_mul (B ^ 2))
  filter_upwards [ae_restrict_mem (show MeasurableSet (radialCore D) from measurableSet_Ioo)]
    with r hr
  have hs : (matchedPartitionSquare D r)⁻¹ ^ 2 ≤ B ^ 2 :=
    (sq_le_sq₀ (inv_nonneg.mpr (matchedPartitionSquare_nonneg D r)) hB).mpr (hbound r hr)
  change (D.localizer m r * f r / matchedPartitionSquare D r) ^ 2 ≤
    B ^ 2 * (D.localizer m r * f r) ^ 2
  rw [div_eq_mul_inv, mul_pow]
  exact (mul_le_mul_of_nonneg_left hs (sq_nonneg _)).trans_eq (mul_comm _ _)

def matchedPhysicalSourceCell (D : ReferenceData)
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D) (m : ℕ) :
    MatchedPhysicalL2 D →L[ℝ] RadialModePair D :=
  matchedModeCell D hP m ∘L matchedPhysicalSourceFactor D hD hP m

def matchedPhysicalOutputCell (D : ReferenceData)
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D) (k : ℕ) :
    RadialModePair D →L[ℝ] MatchedPhysicalL2 D :=
  matchedPhysicalFieldFactor D hD hP k ∘L matchedModeCell D hP k

/-- Regrouping is checked with abstract maps, before any density multiplier
or its integrability proof is substituted. -/
private theorem matchedPhysical_comp_regroup
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (R : H →L[ℝ] E) (A G B : H →L[ℝ] H) (S : E →L[ℝ] H) :
    R ∘L (A ∘L G ∘L B) ∘L S =
      (R ∘L A) ∘L G ∘L (B ∘L S) := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

theorem matchedPhysicalCellBlock_eq (D : ReferenceData)
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (G : RadialModePair D →L[ℝ] RadialModePair D) (k m : ℕ) :
    matchedPhysicalCellBlock D hD hP G k m =
      matchedPhysicalOutputCell D hD hP k ∘L G ∘L
        matchedPhysicalSourceCell D hD hP m := by
  exact matchedPhysical_comp_regroup
    (matchedPhysicalFieldFactor D hD hP k) (matchedModeCell D hP k) G
    (matchedModeCell D hP m) (matchedPhysicalSourceFactor D hD hP m)

theorem matchedPhysicalPartitionInput_source {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (f : MatchedPhysicalL2 D) (u : RadialModeL2 D)
    (hu : (u : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (fun r => -f r / matchingDensity D r)) (m : ℕ) :
    matchedPhysicalSourceCell D hD hP m (matchedPhysicalPartitionInput D hP m f) =
      (matchedModePartitionPiece D hD hP m u, 0) := by
  apply Prod.ext
  · apply Lp.ext
    have hf := (radialHilbertMeasure_ae_iff hD).mpr
      (matchedPhysicalPartitionInput_ae D hP m f)
    filter_upwards [matchedPhysicalCellSource_ae hD hP m
      (matchedPhysicalPartitionInput D hP m f),
      matchedModePartitionPiece_ae D hD hP m u, hf, hu]
      with r hsource hpiece hinput hu'
    change (matchedModeCell D hP m
      (matchedPhysicalSourceFactor D hD hP m
        (matchedPhysicalPartitionInput D hP m f))).1 r =
      matchedModePartitionPiece D hD hP m u r
    rw [hsource, hpiece, hinput, hu']
    simp only [matchedPartitionCoefficient, div_eq_mul_inv]
    ring
  · rfl

/-- Application to the normalized physical cell inputs converges in the
actual target norm, with the border scalar included exactly once. -/
theorem matchedPhysicalPartition_apply_tendsto {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : RadialModePair D →L[ℝ] E)
    (f : MatchedPhysicalL2 D) (u : RadialModeL2 D) (t : ℝ)
    (hu : (u : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (fun r => -f r / matchingDensity D r)) :
    Tendsto (fun N =>
      (∑ m ∈ Finset.range N,
        R (matchedPhysicalSourceCell D hD hP m (matchedPhysicalPartitionInput D hP m f))) +
          t • R (0, 1))
      atTop (𝓝 (R (u, t))) := by
  have hN (N : ℕ) :
      (∑ m ∈ Finset.range N,
        R (matchedPhysicalSourceCell D hD hP m (matchedPhysicalPartitionInput D hP m f))) +
        t • R (0, 1) =
      R ((∑ m ∈ Finset.range N, matchedModePartitionPiece D hD hP m u), t) := by
    simp_rw [matchedPhysicalPartitionInput_source hD hP f u hu]
    calc
      (∑ m ∈ Finset.range N, R (matchedModePartitionPiece D hD hP m u, 0)) +
          t • R (0, 1) =
        R (∑ m ∈ Finset.range N, (matchedModePartitionPiece D hD hP m u, 0)) +
          R (t • (0, 1)) := by rw [map_sum, map_smul]
      _ = R ((∑ m ∈ Finset.range N, (matchedModePartitionPiece D hD hP m u, 0)) +
          t • (0, 1)) := (map_add R _ _).symm
      _ = _ := by
        apply congrArg R
        apply Prod.ext
        · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, smul_zero, add_zero]
        · simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, smul_eq_mul,
            mul_one, Finset.sum_const_zero, zero_add]
  have he :
      (fun N =>
        (∑ m ∈ Finset.range N,
          R (matchedPhysicalSourceCell D hD hP m (matchedPhysicalPartitionInput D hP m f))) +
            t • R (0, 1)) =
      (fun N => R ((∑ m ∈ Finset.range N, matchedModePartitionPiece D hD hP m u), t)) :=
    funext hN
  rw [he]
  exact (R.continuous.tendsto (u, t)).comp
    (matchedModePartition_pair_tendsto D hD hP (u, t))

end ContinuousFlexibility.Radial
