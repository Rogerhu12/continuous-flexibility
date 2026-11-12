import ContinuousFlexibility.Radial.MatchedModeLocalization
import ContinuousFlexibility.Radial.ReferenceCellL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Analysis.MeanInequalities

/-!
# Normalizing the actual radial partition for block reconstruction

The localizers sum to one; their squares need not. Dividing their squares
by their actual square sum gives nonnegative reconstruction coefficients.
The reciprocal square sum has one uniform bound from the finite overlap.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def matchedPartitionSquare (D : ReferenceData) (r : ℝ) : ℝ :=
  ∑' m : ℕ, (D.localizer m r) ^ 2

theorem matchedPartitionSquare_summable {D : ReferenceData}
    (hP : RadialPartition D) (r : ℝ) :
    Summable (fun m : ℕ => (D.localizer m r) ^ 2) := by
  obtain ⟨B, hB⟩ := hP.2.2.2.2.2
  apply summable_of_hasFiniteSupport
  apply (hB r).1.subset
  intro m hm
  change D.localizer m r ≠ 0
  intro hz
  apply hm
  change (D.localizer m r) ^ 2 = 0
  rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)]

theorem matchedPartitionSquare_measurable {D : ReferenceData} (hP : RadialPartition D) :
    Measurable (matchedPartitionSquare D) := by
  apply measurable_of_tendsto_metrizable
    (f := fun N r => ∑ m ∈ Finset.range N, (D.localizer m r) ^ 2)
  · intro N
    exact Finset.measurable_sum _ (fun m _ => (hP.1 m).continuous.measurable.pow_const 2)
  · apply tendsto_pi_nhds.mpr
    intro r
    exact (matchedPartitionSquare_summable hP r).hasSum.tendsto_sum_nat

theorem matchedPartitionSquare_nonneg (D : ReferenceData) (r : ℝ) :
    0 ≤ matchedPartitionSquare D r :=
  tsum_nonneg (fun _ => sq_nonneg _)

theorem matchedPartitionSquare_pos {D : ReferenceData} (hP : RadialPartition D)
    {r : ℝ} (hr : r ∈ radialCore D) : 0 < matchedPartitionSquare D r := by
  obtain ⟨m, hm⟩ := hP.exists_localizer_ne_zero hr
  exact (sq_pos_of_ne_zero hm).trans_le
    ((matchedPartitionSquare_summable hP r).le_tsum m (fun _ _ => sq_nonneg _))

theorem matchedPartitionSquare_le_one {D : ReferenceData} (hP : RadialPartition D)
    {r : ℝ} (hr : r ∈ radialCore D) : matchedPartitionSquare D r ≤ 1 := by
  rw [← (hP.2.2.2.2.1 r hr).2]
  apply Summable.tsum_le_tsum _ (matchedPartitionSquare_summable hP r)
    (hP.2.2.2.2.1 r hr).1
  intro m
  have h0 := hP.2.1 m r
  have h1 := matchedRadialLocalizer_le_one hP m r
  nlinarith

/-- The overlap constant is independent of the point, weights, and mode. -/
theorem exists_matchedPartitionSquare_inv_bound {D : ReferenceData}
    (hP : RadialPartition D) :
    ∃ B : ℝ, 0 < B ∧ ∀ r ∈ radialCore D, (matchedPartitionSquare D r)⁻¹ ≤ B := by
  classical
  obtain ⟨N, hN⟩ := hP.2.2.2.2.2
  let B : ℝ := (N : ℝ) + 1
  refine ⟨B, by dsimp only [B]; positivity, ?_⟩
  intro r hr
  let s : Finset ℕ := (hN r).1.toFinset
  have hzero (m : ℕ) (hm : m ∉ s) : D.localizer m r = 0 := by
    by_contra hn
    exact hm ((hN r).1.mem_toFinset.mpr hn)
  have hsum : (∑ m ∈ s, D.localizer m r) = 1 :=
    (tsum_eq_sum hzero).symm.trans (hP.2.2.2.2.1 r hr).2
  have hsq : (∑ m ∈ s, (D.localizer m r) ^ 2) = matchedPartitionSquare D r :=
    (tsum_eq_sum (s := s) (fun m hm => by rw [hzero m hm, zero_pow (by decide)])).symm
  have hcard : (s.card : ℝ) ≤ B := by
    have hn : s.card ≤ N := by
      simpa only [s, Set.ncard_eq_toFinset_card _ (hN r).1] using (hN r).2
    have hc : (s.card : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hn
    dsimp only [B]
    linarith
  have hCS :
      1 ≤ (s.card : ℝ) * matchedPartitionSquare D r := by
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hsum, hsq]
      using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ : ℕ => (1 : ℝ))
        (fun m => D.localizer m r)
  have hone : 1 ≤ B * matchedPartitionSquare D r :=
    hCS.trans (mul_le_mul_of_nonneg_right hcard (matchedPartitionSquare_nonneg D r))
  rw [← one_div]
  exact (div_le_iff₀ (matchedPartitionSquare_pos hP hr)).mpr hone

def matchedPartitionCoefficient (D : ReferenceData) (m : ℕ) (r : ℝ) : ℝ :=
  (D.localizer m r) ^ 2 / matchedPartitionSquare D r

theorem matchedPartitionCoefficient_measurable {D : ReferenceData}
    (hP : RadialPartition D) (m : ℕ) :
    Measurable (matchedPartitionCoefficient D m) :=
  ((hP.1 m).continuous.measurable.pow_const 2).div (matchedPartitionSquare_measurable hP)

theorem matchedPartitionCoefficient_nonneg (D : ReferenceData) (m : ℕ) (r : ℝ) :
    0 ≤ matchedPartitionCoefficient D m r :=
  div_nonneg (sq_nonneg _) (matchedPartitionSquare_nonneg D r)

theorem matchedPartitionCoefficient_summable {D : ReferenceData}
    (hP : RadialPartition D) (r : ℝ) :
    Summable (fun m => matchedPartitionCoefficient D m r) :=
  (matchedPartitionSquare_summable hP r).div_const _

theorem matchedPartitionCoefficient_tsum {D : ReferenceData}
    (hP : RadialPartition D) {r : ℝ} (hr : r ∈ radialCore D) :
    (∑' m, matchedPartitionCoefficient D m r) = 1 := by
  simp only [matchedPartitionCoefficient, tsum_div_const]
  exact div_self (matchedPartitionSquare_pos hP hr).ne'

theorem matchedPartitionCoefficient_partial {D : ReferenceData}
    (hP : RadialPartition D) (s : Finset ℕ) {r : ℝ} (hr : r ∈ radialCore D) :
    0 ≤ ∑ m ∈ s, matchedPartitionCoefficient D m r ∧
      (∑ m ∈ s, matchedPartitionCoefficient D m r) ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun m _ => matchedPartitionCoefficient_nonneg D m r), ?_⟩
  rw [← matchedPartitionCoefficient_tsum hP hr]
  exact (matchedPartitionCoefficient_summable hP r).sum_le_tsum s
    (fun m _ => matchedPartitionCoefficient_nonneg D m r)

end ContinuousFlexibility.Radial
