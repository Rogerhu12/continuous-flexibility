import ContinuousFlexibility.Radial.ReferenceWeightedProduct
import ContinuousFlexibility.Radial.ReferenceRadialMeasureComparison
import ContinuousFlexibility.Radial.MatchedPhysicalPartition

/-!
# Actual radial weighted norms and physical partition inputs

The cell energies here are integrals for the existing weighted radial
measure. Their sum is exactly its squared L² norm. This identifies the
numeric sequence used in the Schur test with the physical source norm.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ENNReal
open ContinuousFlexibility.Statements

def matchedRadialWeight (D : ReferenceData) (γ M : ℝ) (m : ℕ) : ℝ :=
  Real.exp (M * radialQ (D.cellIndex m) + γ * radialS (D.cellIndex m))

theorem matchedRadialWeight_pos (D : ReferenceData) (γ M : ℝ) (m : ℕ) :
    0 < matchedRadialWeight D γ M m := Real.exp_pos _

theorem matchedRadialWeight_sq (D : ReferenceData) (γ M : ℝ) (m : ℕ) :
    matchedRadialWeight D γ M m ^ 2 =
      Real.exp (2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) := by
  unfold matchedRadialWeight
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

def matchedRadialCellSquare (D : ReferenceData) (γ M : ℝ) (f : ℝ → ℝ) (m : ℕ) : ℝ :=
  matchedRadialWeight D γ M m ^ 2 *
    ∫ r, (D.localizer m r * f r) ^ 2 ∂volume.restrict (radialCore D)

theorem matchedRadialCellSquare_nonneg (D : ReferenceData) (γ M : ℝ)
    (f : ℝ → ℝ) (m : ℕ) : 0 ≤ matchedRadialCellSquare D γ M f m :=
  mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => sq_nonneg _))

theorem matchedRadialCellDensity_mul_sq (D : ReferenceData) (γ M : ℝ)
    (m : ℕ) (f : ℝ → ℝ) (r : ℝ) :
    (referenceRadialCellDensity D γ M m r).toReal * f r ^ 2 =
      matchedRadialWeight D γ M m ^ 2 * (D.localizer m r * f r) ^ 2 := by
  unfold referenceRadialCellDensity
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)),
    matchedRadialWeight_sq]
  ring

theorem matchedRadialCell_integral_sq {D : ReferenceData}
    (hP : RadialPartition D) (γ M : ℝ) (m : ℕ) (f : ℝ → ℝ) :
    (∫ r, f r ^ 2 ∂referenceRadialWeightedCellMeasure D γ M m) =
      matchedRadialCellSquare D γ M f m := by
  unfold referenceRadialWeightedCellMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (referenceRadialCellDensity_measurable hP γ M m)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [smul_eq_mul, matchedRadialCellDensity_mul_sq]
  exact integral_const_mul _ _

theorem matchedRadialCell_integrable_sq {D : ReferenceData}
    (hP : RadialPartition D) (γ M : ℝ) (m : ℕ) {f : ℝ → ℝ}
    (hf : MemLp (fun r => D.localizer m r * f r) 2
      (volume.restrict (radialCore D))) :
    Integrable (fun r => f r ^ 2) (referenceRadialWeightedCellMeasure D γ M m) := by
  unfold referenceRadialWeightedCellMeasure
  rw [integrable_withDensity_iff_integrable_smul'
    (referenceRadialCellDensity_measurable hP γ M m)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simpa only [smul_eq_mul, matchedRadialCellDensity_mul_sq] using
    hf.integrable_sq.const_mul (matchedRadialWeight D γ M m ^ 2)

theorem matchedRadialWeighted_ae_iff {D : ReferenceData}
    (hP : RadialPartition D) (γ M : ℝ) {p : ℝ → Prop} :
    (∀ᵐ r ∂referenceRadialWeightedMeasure D γ M, p r) ↔
      ∀ᵐ r ∂volume.restrict (radialCore D), p r := by
  constructor
  · intro h
    have hc := Measure.ae_sum_iff.mp h
    have hall : ∀ᵐ r ∂volume.restrict (radialCore D), ∀ m,
        referenceRadialCellDensity D γ M m r ≠ 0 → p r :=
      ae_all_iff.mpr (fun m =>
        (ae_withDensity_iff (referenceRadialCellDensity_measurable hP γ M m)).mp (hc m))
    filter_upwards [hall,
      ae_restrict_mem (show MeasurableSet (radialCore D) from measurableSet_Ioo)]
      with r hr hcore
    obtain ⟨m, hm⟩ := hP.exists_localizer_ne_zero hcore
    apply hr m
    exact ne_of_gt (ENNReal.ofReal_pos.mpr
      (mul_pos (Real.exp_pos _) (sq_pos_of_ne_zero hm)))
  · intro h
    apply Measure.ae_sum_iff.mpr
    intro m
    apply (ae_withDensity_iff (referenceRadialCellDensity_measurable hP γ M m)).mpr
    exact h.mono (fun _ hp _ => hp)

theorem matchedRadial_absolutelyContinuous_weighted {D : ReferenceData}
    (hP : RadialPartition D) (γ M : ℝ) :
    volume.restrict (radialCore D) ≪ referenceRadialWeightedMeasure D γ M := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hs0
  have hn : ∀ᵐ r ∂referenceRadialWeightedMeasure D γ M, r ∉ s := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hs0
  have hp := (matchedRadialWeighted_ae_iff hP γ M).mp hn
  simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hp

theorem matchedRadial_aestronglyMeasurable_weighted {D : ReferenceData}
    {f : ℝ → ℝ} (hf : AEStronglyMeasurable f (volume.restrict (radialCore D)))
    (γ M : ℝ) : AEStronglyMeasurable f (referenceRadialWeightedMeasure D γ M) := by
  apply aestronglyMeasurable_sum_measure_iff.mpr
  intro m
  exact hf.mono_ac (withDensity_absolutelyContinuous _ _)

theorem matchedRadial_localized_memLp_of_weighted {D : ReferenceData}
    (hP : RadialPartition D) {γ M : ℝ} {f : ℝ → ℝ}
    (hf : MemLp f 2 (referenceRadialWeightedMeasure D γ M)) (m : ℕ) :
    MemLp (fun r => D.localizer m r * f r) 2
      (volume.restrict (radialCore D)) := by
  have hfm := hf.aestronglyMeasurable.mono_ac
    (matchedRadial_absolutelyContinuous_weighted hP γ M)
  apply (memLp_two_iff_integrable_sq
    ((hP.1 m).continuous.aestronglyMeasurable.mul hfm)).mpr
  have hi : Integrable (fun r => f r ^ 2)
      (referenceRadialWeightedCellMeasure D γ M m) :=
    hf.integrable_sq.mono_measure (Measure.le_sum (referenceRadialWeightedCellMeasure D γ M) m)
  have hh := (integrable_withDensity_iff_integrable_smul'
    (referenceRadialCellDensity_measurable hP γ M m)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hi
  have hs := hh.const_mul (matchedRadialWeight D γ M m ^ 2)⁻¹
  simpa only [smul_eq_mul, matchedRadialCellDensity_mul_sq, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero 2 (matchedRadialWeight_pos D γ M m).ne'), one_mul] using hs

theorem matchedRadialCellSquare_summable {D : ReferenceData}
    (hP : RadialPartition D) {γ M : ℝ} {f : ℝ → ℝ}
    (hf : MemLp f 2 (referenceRadialWeightedMeasure D γ M)) :
    Summable (matchedRadialCellSquare D γ M f) := by
  have hs := hf.integrable_sq.summable_integral
  simpa only [Real.norm_of_nonneg (sq_nonneg _), matchedRadialCell_integral_sq hP] using hs

theorem matchedRadial_memLp_of_cellSquare_summable {D : ReferenceData}
    (hP : RadialPartition D) {γ M : ℝ} {f : ℝ → ℝ}
    (hm : AEStronglyMeasurable f (volume.restrict (radialCore D)))
    (hl : ∀ m, MemLp (fun r => D.localizer m r * f r) 2
      (volume.restrict (radialCore D)))
    (hs : Summable (matchedRadialCellSquare D γ M f)) :
    MemLp f 2 (referenceRadialWeightedMeasure D γ M) := by
  apply (memLp_two_iff_integrable_sq
    (matchedRadial_aestronglyMeasurable_weighted hm γ M)).mpr
  apply integrable_sum_measure (fun m => matchedRadialCell_integrable_sq hP γ M m (hl m))
  simpa only [Real.norm_of_nonneg (sq_nonneg _), matchedRadialCell_integral_sq hP] using hs

theorem matchedRadialWeighted_integral_sq {D : ReferenceData}
    (hP : RadialPartition D) {γ M : ℝ} {f : ℝ → ℝ}
    (hf : MemLp f 2 (referenceRadialWeightedMeasure D γ M)) :
    (∫ r, f r ^ 2 ∂referenceRadialWeightedMeasure D γ M) =
      ∑' m, matchedRadialCellSquare D γ M f m := by
  unfold referenceRadialWeightedMeasure
  rw [integral_sum_measure hf.integrable_sq]
  exact tsum_congr (fun m => matchedRadialCell_integral_sq hP γ M m f)

/-- Nonnegative source exponents control ordinary radial L² as well. -/
theorem matchedPhysical_memLp_of_weighted {D : ReferenceData}
    (hP : RadialPartition D) {γ M : ℝ} (hγ : 0 ≤ γ) (hM : 0 ≤ M)
    {f : ℝ → ℝ} (hf : MemLp f 2 (referenceRadialWeightedMeasure D γ M)) :
    MemLp f 2 (volume.restrict (radialCore D)) := by
  obtain ⟨B, _, hcmp⟩ := referenceRadial_withDensity_le_weighted hP
  have hc := hcmp γ M 1 (fun _ => 1) zero_le_one (fun _ _ => zero_le_one)
    (fun m _r _hr => by
      rw [one_mul]
      apply Real.one_le_exp_iff.mpr
      have hq := radialQ_nonneg (D.cellIndex m)
      have hS : 0 ≤ radialS (D.cellIndex m) := by unfold radialS; positivity
      positivity)
  simp only [ENNReal.ofReal_one, Measure.withDensity_one, one_mul] at hc
  exact hf.of_measure_le_smul (by simp) hc

theorem matchedPhysicalPartition_weighted_sq {D : ReferenceData}
    (hP : RadialPartition D) {B γ M : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ r ∈ radialCore D, (matchedPartitionSquare D r)⁻¹ ≤ B)
    (f : MatchedPhysicalL2 D)
    (hf : MemLp (f : ℝ → ℝ) 2 (referenceRadialWeightedMeasure D γ M)) :
    Summable (fun m =>
      (matchedRadialWeight D γ M m * ‖matchedPhysicalPartitionInput D hP m f‖) ^ 2) ∧
      (∑' m,
        (matchedRadialWeight D γ M m * ‖matchedPhysicalPartitionInput D hP m f‖) ^ 2) ≤
        B ^ 2 * ∫ r, f r ^ 2 ∂referenceRadialWeightedMeasure D γ M := by
  have hs := matchedRadialCellSquare_summable hP hf
  have he (m : ℕ) :
      (matchedRadialWeight D γ M m * ‖matchedPhysicalPartitionInput D hP m f‖) ^ 2 ≤
        B ^ 2 * matchedRadialCellSquare D γ M f m := by
    rw [mul_pow]
    have hh := mul_le_mul_of_nonneg_left
      (matchedPhysicalPartitionInput_norm_sq_le hP hB hbound m f)
      (sq_nonneg (matchedRadialWeight D γ M m))
    exact hh.trans_eq (by unfold matchedRadialCellSquare; ring)
  have hi := Summable.of_nonneg_of_le (fun _ => sq_nonneg _) he (hs.mul_left (B ^ 2))
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∑' m, B ^ 2 * matchedRadialCellSquare D γ M f m :=
      Summable.tsum_le_tsum he hi (hs.mul_left (B ^ 2))
    _ = B ^ 2 * ∫ r, f r ^ 2 ∂referenceRadialWeightedMeasure D γ M := by
      rw [tsum_mul_left, matchedRadialWeighted_integral_sq hP hf]

end ContinuousFlexibility.Radial
