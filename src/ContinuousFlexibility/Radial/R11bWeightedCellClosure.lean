module

public import ContinuousFlexibility.Radial.R11bBoundedMultiplierLimit
public import ContinuousFlexibility.Radial.ProfilePartitionBounds
public import ContinuousFlexibility.Radial.R11bPhysicalPairing
public import ContinuousFlexibility.Radial.R11bWeightEmbedding
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Weighted cell square bounds are closed under physical L² limits

Each radial localizer is bounded by one. Its square integral is therefore
continuous in physical L². Finite cell sums pass to the limit, and their
uniform bound yields the complete summable weighted series.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Filter Set MeasureTheory Real
open scoped BigOperators Topology
open ContinuousFlexibility.Statements

theorem r11b_cellIntegrable_of_global_memLp {D : ReferenceData}
    (hpart : RadialPartition D) {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (radialPhysicalMeasure D)) :
    RadialCellIntegrable D f := by
  intro m
  apply r11b_memLp_mul_bounded
    (((hpart.1 m).continuous.measurable.comp measurable_fst).aestronglyMeasurable)
    (C := 1) _ hf
  exact Eventually.of_forall fun x => by
    change ‖D.localizer m x.1‖ ≤ 1
    simpa only [Real.norm_eq_abs] using profile_localizer_abs_le_one hpart m x.1

theorem r11b_tendsto_referenceCellSquare {D : ReferenceData}
    (hpart : RadialPartition D) (hab : D.a ≤ D.b)
    {f : ℕ → PolarPoint → ℝ} {g : PolarPoint → ℝ}
    (hf : ∀ n, MemLp (f n) 2 (radialPhysicalMeasure D))
    (hg : MemLp g 2 (radialPhysicalMeasure D))
    (hlim : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g))) (m : ℕ) :
    Tendsto (fun n => referenceCellSquare D m (f n)) atTop
      (𝓝 (referenceCellSquare D m g)) := by
  have ha : AEStronglyMeasurable (fun x : PolarPoint => D.localizer m x.1)
      (radialPhysicalMeasure D) :=
    ((hpart.1 m).continuous.measurable.comp measurable_fst).aestronglyMeasurable
  have hC : ∀ᵐ x ∂radialPhysicalMeasure D, ‖D.localizer m x.1‖ ≤ 1 :=
    Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using profile_localizer_abs_le_one hpart m x.1
  have hm := r11b_tendsto_toLp_mul_bounded ha hC hf hg hlim
  have hi : Tendsto
      (fun n => ∫ x, (D.localizer m x.1 * f n x) ^ 2 ∂radialPhysicalMeasure D)
      atTop (𝓝 (∫ x, (D.localizer m x.1 * g x) ^ 2 ∂radialPhysicalMeasure D)) := by
    simpa only [r11b_norm_toLp_sq] using hm.norm.pow 2
  have heq : (fun n => referenceCellSquare D m (f n)) =
      fun n => (2 * Real.pi)⁻¹ *
        ∫ x, (D.localizer m x.1 * f n x) ^ 2 ∂radialPhysicalMeasure D := by
    funext n
    exact r11b_referenceCellSquare_eq_integral hab
      (r11b_cellIntegrable_of_global_memLp hpart (hf n)) m
  rw [heq, r11b_referenceCellSquare_eq_integral hab
    (r11b_cellIntegrable_of_global_memLp hpart hg) m]
  exact hi.const_mul ((2 * Real.pi)⁻¹)

theorem r11b_weighted_cell_square_closed {D : ReferenceData}
    (hpart : RadialPartition D) (hab : D.a ≤ D.b)
    (w : ℕ → ℝ) (hw : ∀ m, 0 ≤ w m)
    {f : ℕ → PolarPoint → ℝ} {g : PolarPoint → ℝ} {B : ℝ}
    (hf : ∀ n, MemLp (f n) 2 (radialPhysicalMeasure D))
    (hg : MemLp g 2 (radialPhysicalMeasure D))
    (hlim : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)))
    (hs : ∀ n, Summable (fun m => w m * referenceCellSquare D m (f n)))
    (hbound : ∀ n, (∑' m, w m * referenceCellSquare D m (f n)) ≤ B) :
    RadialCellIntegrable D g ∧
      Summable (fun m => w m * referenceCellSquare D m g) ∧
      (∑' m, w m * referenceCellSquare D m g) ≤ B := by
  have hnn (m : ℕ) : 0 ≤ w m * referenceCellSquare D m g :=
    mul_nonneg (hw m) (r11b_referenceCellSquare_nonneg hab m g)
  have hfinite (s : Finset ℕ) : (∑ m ∈ s, w m * referenceCellSquare D m g) ≤ B := by
    have ht : Tendsto (fun n => ∑ m ∈ s, w m * referenceCellSquare D m (f n))
        atTop (𝓝 (∑ m ∈ s, w m * referenceCellSquare D m g)) :=
      tendsto_finsetSum s (fun m _ =>
        (r11b_tendsto_referenceCellSquare hpart hab hf hg hlim m).const_mul (w m))
    apply le_of_tendsto' ht
    intro n
    exact (Summable.sum_le_tsum s
      (fun m _ => mul_nonneg (hw m) (r11b_referenceCellSquare_nonneg hab m (f n)))
      (hs n)).trans (hbound n)
  exact ⟨r11b_cellIntegrable_of_global_memLp hpart hg,
    summable_of_sum_le hnn hfinite, Real.tsum_le_of_sum_le hnn hfinite⟩

end ContinuousFlexibility.Radial
