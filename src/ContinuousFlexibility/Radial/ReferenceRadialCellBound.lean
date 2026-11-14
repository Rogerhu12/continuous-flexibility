module

public import ContinuousFlexibility.Radial.ReferenceRadialKernelPairing
public import ContinuousFlexibility.Radial.MatchedPartitionNormalization
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# A cellwise bound implies actual weighted radial L2 membership

The square sum of the true partition is at most one. Finite partial sums
of the cell energies are therefore bounded by the ordinary interval
length times the common pointwise energy bound. This proves both the
summability and the actual weighted L2 estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Real Filter MeasureTheory
open scoped ENNReal
open ContinuousFlexibility.Radial

theorem referenceRadial_memLp_of_cellwise_sq_bound {D : ReferenceData}
    (hab : D.a < D.b) (hD : RadialPartition D) {γ M A : ℝ}
    (hA : 0 ≤ A) {u : ℝ → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict (radialCore D)))
    (hcell : ∀ m : ℕ, ∀ r ∈ D.cells m,
      exp (2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
        (u r) ^ 2 ≤ A) :
    MemLp u 2 (referenceRadialWeightedMeasure D γ M) ∧
      (∫ r, (u r) ^ 2 ∂referenceRadialWeightedMeasure D γ M) ≤ (D.b - D.a) * A := by
  letI : IsFiniteMeasure (volume.restrict (radialCore D)) := by
    change IsFiniteMeasure (volume.restrict (Ioo D.a D.b))
    infer_instance
  let g (m : ℕ) (r : ℝ) : ℝ :=
    exp (2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
      (D.localizer m r) ^ 2 * (u r) ^ 2
  have hg0 (m : ℕ) (r : ℝ) : 0 ≤ g m r := by
    dsimp only [g]
    positivity
  have hgcell (m : ℕ) (r : ℝ) :
      g m r ≤ A * (D.localizer m r) ^ 2 := by
    by_cases hn : D.localizer m r = 0
    · simp only [g, hn, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_mul, le_refl]
    · have hmr : r ∈ D.cells m := hD.2.2.1 m hn
      have h := mul_le_mul_of_nonneg_right (hcell m r hmr) (sq_nonneg (D.localizer m r))
      dsimp only [g]
      nlinarith only [h]
  have hgm (m : ℕ) : AEStronglyMeasurable (g m) (volume.restrict (radialCore D)) :=
    (aestronglyMeasurable_const.mul
      ((hD.1 m).continuous.aestronglyMeasurable.pow 2)).mul (hu.pow 2)
  have hgi (m : ℕ) : Integrable (g m) (volume.restrict (radialCore D)) := by
    apply (integrable_const A).mono' (hgm m)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [Real.norm_of_nonneg (hg0 m r)]
    have hθ0 := hD.2.1 m r
    have hθ1 := matchedRadialLocalizer_le_one hD m r
    have hθsq : (D.localizer m r) ^ 2 ≤ 1 := by nlinarith only [hθ0, hθ1]
    exact (hgcell m r).trans
      ((mul_le_mul_of_nonneg_left hθsq hA).trans_eq (mul_one A))
  have hid (m : ℕ) :
      (∫ r, (u r) ^ 2 ∂referenceRadialWeightedCellMeasure D γ M m) =
        ∫ r in radialCore D, g m r := by
    unfold referenceRadialWeightedCellMeasure
    rw [integral_withDensity_eq_integral_toReal_smul
      (referenceRadialCellDensity_measurable hD γ M m)
      (ae_of_all _ (fun r => ENNReal.ofReal_lt_top))]
    apply integral_congr_ae
    exact ae_of_all _ (fun r => by
      simp only [referenceRadialCellDensity, g,
        ENNReal.toReal_ofReal (mul_nonneg (exp_pos _).le (sq_nonneg _)), smul_eq_mul])
  have hui (m : ℕ) :
      Integrable (fun r => (u r) ^ 2) (referenceRadialWeightedCellMeasure D γ M m) := by
    unfold referenceRadialWeightedCellMeasure
    apply (integrable_withDensity_iff_integrable_smul'
      (referenceRadialCellDensity_measurable hD γ M m)
      (ae_of_all _ (fun r => ENNReal.ofReal_lt_top))).mpr
    simpa only [referenceRadialCellDensity,
      ENNReal.toReal_ofReal (mul_nonneg (exp_pos _).le (sq_nonneg _)), smul_eq_mul]
      using hgi m
  let e (m : ℕ) : ℝ := ∫ r, (u r) ^ 2 ∂referenceRadialWeightedCellMeasure D γ M m
  have he0 (m : ℕ) : 0 ≤ e m := integral_nonneg (fun _ => sq_nonneg _)
  have hfinite (s : Finset ℕ) : ∑ m ∈ s, e m ≤ (D.b - D.a) * A := by
    calc
      ∑ m ∈ s, e m = ∫ r in radialCore D, ∑ m ∈ s, g m r := by
        simp_rw [e, hid]
        exact (integral_finsetSum s (fun m _ => hgi m)).symm
      _ ≤ ∫ _ in radialCore D, A := by
        apply integral_mono_ae (integrable_finsetSum s (fun m _ => hgi m)) (integrable_const A)
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        calc
          ∑ m ∈ s, g m r ≤ ∑ m ∈ s, A * (D.localizer m r) ^ 2 :=
            Finset.sum_le_sum (fun m _ => hgcell m r)
          _ = A * ∑ m ∈ s, (D.localizer m r) ^ 2 := (Finset.mul_sum _ _ _).symm
          _ ≤ A * matchedPartitionSquare D r := mul_le_mul_of_nonneg_left
            ((matchedPartitionSquare_summable hD r).sum_le_tsum s
              (fun _ _ => sq_nonneg _)) hA
          _ ≤ A * 1 := mul_le_mul_of_nonneg_left (matchedPartitionSquare_le_one hD hr) hA
          _ = A := mul_one A
      _ = _ := by
        rw [integral_const]
        simp only [measureReal_def, Measure.restrict_apply_univ, radialCore,
          Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le), smul_eq_mul]
  have hesum : Summable e := summable_of_sum_le he0 hfinite
  have huisum : Integrable (fun r => (u r) ^ 2) (referenceRadialWeightedMeasure D γ M) := by
    rw [referenceRadialWeightedMeasure_eq_sum hD γ M]
    apply integrable_sum_measure hui
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hesum
  have hum : AEStronglyMeasurable u (referenceRadialWeightedMeasure D γ M) :=
    hu.mono_ac (referenceRadialWeightedMeasure_absolutelyContinuous D γ M)
  refine ⟨(memLp_two_iff_integrable_sq hum).mpr huisum, ?_⟩
  rw [referenceRadialWeightedMeasure_eq_sum hD γ M] at huisum ⊢
  rw [integral_sum_measure huisum]
  exact Real.tsum_le_of_sum_le he0 hfinite

end ContinuousFlexibility.Statements
