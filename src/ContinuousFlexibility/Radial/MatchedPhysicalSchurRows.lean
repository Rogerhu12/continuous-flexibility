import ContinuousFlexibility.Radial.MatchedRadialWeightedNorm
import ContinuousFlexibility.Radial.MatchedSchurSquareBounds

/-!
# Schur estimates for the existing physical modal operator

Channel zero is the scalar border. The other channels are the genuine
physical cell input and output maps. Norm convergence of the actual
partition reconstruction supplies every row inequality.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology
open ContinuousFlexibility.Statements

def matchedPhysicalChannelWeight (D : ReferenceData) (γ M : ℝ) : ℕ → ℝ
  | 0 => 1
  | m + 1 => matchedRadialWeight D γ M m

def matchedPhysicalSourceSequence (D : ReferenceData) (hP : RadialPartition D)
    (γ M : ℝ) (f : MatchedPhysicalL2 D) (t : ℝ) : ℕ → ℝ
  | 0 => ‖t‖
  | m + 1 => matchedRadialWeight D γ M m * ‖matchedPhysicalPartitionInput D hP m f‖

def matchedPhysicalOutputSequence (D : ReferenceData)
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (γ M : ℝ) (U : RadialModePair D) : ℕ → ℝ
  | 0 => ‖U.2‖
  | k + 1 => matchedRadialWeight D γ M k * ‖matchedPhysicalOutputCell D hD hP k U‖

/-- These are norms of the actual four kinds of block. No weighted
output bound or independently chosen solution is included. -/
def matchedPhysicalRawKernel (D : ReferenceData)
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (G : RadialModePair D →L[ℝ] RadialModePair D) : ℕ → ℕ → ℝ
  | 0, 0 => ‖(G (0, 1)).2‖
  | 0, m + 1 =>
      ‖(ContinuousLinearMap.snd ℝ (RadialModeL2 D) ℝ) ∘L G ∘L
        matchedPhysicalSourceCell D hD hP m‖
  | k + 1, 0 => ‖matchedPhysicalOutputCell D hD hP k (G (0, 1))‖
  | k + 1, m + 1 => ‖matchedPhysicalCellBlock D hD hP G k m‖

theorem matchedPhysicalRawKernel_nonneg (D : ReferenceData)
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (G : RadialModePair D →L[ℝ] RadialModePair D) (k m : ℕ) :
    0 ≤ matchedPhysicalRawKernel D hD hP G k m := by
  cases k <;> cases m <;> exact norm_nonneg _

theorem matchedPhysicalSourceSequence_nonneg (D : ReferenceData)
    (hP : RadialPartition D) (γ M : ℝ) (f : MatchedPhysicalL2 D) (t : ℝ) (m : ℕ) :
    0 ≤ matchedPhysicalSourceSequence D hP γ M f t m := by
  cases m with
  | zero => exact norm_nonneg _
  | succ m => exact mul_nonneg (matchedRadialWeight_pos D γ M m).le (norm_nonneg _)

theorem matchedPhysicalOutputSequence_nonneg (D : ReferenceData)
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (γ M : ℝ) (U : RadialModePair D) (k : ℕ) :
    0 ≤ matchedPhysicalOutputSequence D hD hP γ M U k := by
  cases k with
  | zero => exact norm_nonneg _
  | succ k => exact mul_nonneg (matchedRadialWeight_pos D γ M k).le (norm_nonneg _)

theorem matchedPhysicalSourceSequence_sq {D : ReferenceData}
    (hP : RadialPartition D) {B γ M : ℝ} (hB : 1 ≤ B)
    (hbound : ∀ r ∈ radialCore D, (matchedPartitionSquare D r)⁻¹ ≤ B)
    (f : MatchedPhysicalL2 D) (t : ℝ)
    (hf : MemLp (f : ℝ → ℝ) 2 (referenceRadialWeightedMeasure D γ M)) :
    Summable (fun m => matchedPhysicalSourceSequence D hP γ M f t m ^ 2) ∧
      (∑' m, matchedPhysicalSourceSequence D hP γ M f t m ^ 2) ≤
        B ^ 2 * ((∫ r, f r ^ 2 ∂referenceRadialWeightedMeasure D γ M) + t ^ 2) := by
  have hB₀ : 0 ≤ B := zero_le_one.trans hB
  obtain ⟨hs, hb⟩ := matchedPhysicalPartition_weighted_sq hP hB₀ hbound f hf
  have ht : Summable
      (fun m => matchedPhysicalSourceSequence D hP γ M f t (m + 1) ^ 2) := hs
  have hall := (summable_nat_add_iff 1).mp ht
  refine ⟨hall, ?_⟩
  rw [hall.tsum_eq_zero_add]
  simp only [matchedPhysicalSourceSequence, Real.norm_eq_abs, sq_abs]
  have hBsq : 1 ≤ B ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hBsq (sq_nonneg t)]

/-- A single actual output map is controlled by its scalar column and
its physical cell blocks. The scalar channel is included once. -/
theorem matchedPhysical_row_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : RadialModePair D →L[ℝ] E)
    (f : MatchedPhysicalL2 D) (u : RadialModeL2 D) (t : ℝ)
    (hu : (u : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      fun r => -f r / matchingDensity D r)
    (γ M w : ℝ) (hw : 0 ≤ w) (K : ℕ → ℝ)
    (hK : ∀ m, 0 ≤ K m)
    (hs : Summable (fun m => K m * matchedPhysicalSourceSequence D hP γ M f t m))
    (hzero : w * ‖R (0, 1)‖ ≤ K 0)
    (hcell : ∀ m, w * ‖R ∘L matchedPhysicalSourceCell D hD hP m‖ ≤
      K (m + 1) * matchedRadialWeight D γ M m) :
    w * ‖R (u, t)‖ ≤
      ∑' m, K m * matchedPhysicalSourceSequence D hP γ M f t m := by
  let x := matchedPhysicalSourceSequence D hP γ M f t
  have hx : ∀ m, 0 ≤ x m := matchedPhysicalSourceSequence_nonneg D hP γ M f t
  have htail : Summable (fun m => K (m + 1) * x (m + 1)) :=
    (summable_nat_add_iff 1).mpr hs
  have hpiece (m : ℕ) :
      w * ‖R (matchedPhysicalSourceCell D hD hP m
        (matchedPhysicalPartitionInput D hP m f))‖ ≤ K (m + 1) * x (m + 1) := by
    calc
      _ ≤ w * (‖R ∘L matchedPhysicalSourceCell D hD hP m‖ *
          ‖matchedPhysicalPartitionInput D hP m f‖) :=
        mul_le_mul_of_nonneg_left
          ((R ∘L matchedPhysicalSourceCell D hD hP m).le_opNorm _) hw
      _ = (w * ‖R ∘L matchedPhysicalSourceCell D hD hP m‖) *
          ‖matchedPhysicalPartitionInput D hP m f‖ := by ring
      _ ≤ (K (m + 1) * matchedRadialWeight D γ M m) *
          ‖matchedPhysicalPartitionInput D hP m f‖ :=
        mul_le_mul_of_nonneg_right (hcell m) (norm_nonneg _)
      _ = _ := by dsimp only [x, matchedPhysicalSourceSequence]; ring
  have hb : w * ‖R (0, 1)‖ * ‖t‖ ≤ K 0 * x 0 :=
    mul_le_mul_of_nonneg_right hzero (norm_nonneg t)
  have hlim := (matchedPhysicalPartition_apply_tendsto hD hP R f u t hu).norm.const_mul w
  apply le_of_tendsto' hlim
  intro N
  have hn :
      ‖(∑ m ∈ Finset.range N, R (matchedPhysicalSourceCell D hD hP m
          (matchedPhysicalPartitionInput D hP m f))) + t • R (0, 1)‖ ≤
        (∑ m ∈ Finset.range N, ‖R (matchedPhysicalSourceCell D hD hP m
          (matchedPhysicalPartitionInput D hP m f))‖) + ‖t‖ * ‖R (0, 1)‖ := by
    exact (norm_add_le _ _).trans
      (add_le_add (norm_sum_le _ _) (le_of_eq (norm_smul _ _)))
  calc
    _ ≤ w * ((∑ m ∈ Finset.range N, ‖R (matchedPhysicalSourceCell D hD hP m
        (matchedPhysicalPartitionInput D hP m f))‖) + ‖t‖ * ‖R (0, 1)‖) :=
      mul_le_mul_of_nonneg_left hn hw
    _ = (∑ m ∈ Finset.range N, w * ‖R (matchedPhysicalSourceCell D hD hP m
        (matchedPhysicalPartitionInput D hP m f))‖) + w * ‖R (0, 1)‖ * ‖t‖ := by
      rw [mul_add, Finset.mul_sum]
      ring
    _ ≤ (∑ m ∈ Finset.range N, K (m + 1) * x (m + 1)) + K 0 * x 0 :=
      add_le_add (Finset.sum_le_sum (fun m _ => hpiece m)) hb
    _ ≤ (∑' m, K (m + 1) * x (m + 1)) + K 0 * x 0 :=
      add_le_add (htail.sum_le_tsum _ (fun m _ => mul_nonneg (hK _) (hx _))) le_rfl
    _ = _ := by rw [hs.tsum_eq_zero_add]; exact add_comm _ _

theorem matchedPhysical_outputSequence_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (G : RadialModePair D →L[ℝ] RadialModePair D)
    (f : MatchedPhysicalL2 D) (u : RadialModeL2 D) (t : ℝ)
    (hu : (u : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      fun r => -f r / matchingDensity D r)
    (γ M₀ Mout : ℝ) (K : ℕ → ℕ → ℝ)
    (hK : ∀ k m, 0 ≤ K k m)
    (hrow : ∀ k, Summable (K k))
    (hxs : Summable (fun m => matchedPhysicalSourceSequence D hP γ M₀ f t m ^ 2))
    (hmajor : ∀ k m,
      matchedPhysicalChannelWeight D γ Mout k * matchedPhysicalRawKernel D hD hP G k m ≤
        K k m * matchedPhysicalChannelWeight D γ M₀ m) :
    ∀ k, matchedPhysicalOutputSequence D hD hP γ Mout (G (u, t)) k ≤
      ∑' m, K k m * matchedPhysicalSourceSequence D hP γ M₀ f t m := by
  intro k
  have hs := schur_row_mul_summable hK hrow
    (matchedPhysicalSourceSequence_nonneg D hP γ M₀ f t) hxs k
  cases k with
  | zero =>
      let R := (ContinuousLinearMap.snd ℝ (RadialModeL2 D) ℝ) ∘L G
      have h0 : 1 * ‖R (0, 1)‖ ≤ K 0 0 := by
        simpa only [matchedPhysicalChannelWeight, matchedPhysicalRawKernel, mul_one]
          using hmajor 0 0
      have hc (m : ℕ) :
          1 * ‖R ∘L matchedPhysicalSourceCell D hD hP m‖ ≤
            K 0 (m + 1) * matchedRadialWeight D γ M₀ m := hmajor 0 (m + 1)
      have hh := matchedPhysical_row_bound hD hP R f u t hu γ M₀ 1 zero_le_one
        (K 0) (hK 0) hs h0 hc
      simpa only [one_mul] using hh
  | succ k =>
      let R := matchedPhysicalOutputCell D hD hP k ∘L G
      have h0 : matchedRadialWeight D γ Mout k * ‖R (0, 1)‖ ≤ K (k + 1) 0 := by
        simpa only [matchedPhysicalChannelWeight, matchedPhysicalRawKernel, mul_one]
          using hmajor (k + 1) 0
      have hc (m : ℕ) :
          matchedRadialWeight D γ Mout k * ‖R ∘L matchedPhysicalSourceCell D hD hP m‖ ≤
            K (k + 1) (m + 1) * matchedRadialWeight D γ M₀ m := hmajor (k + 1) (m + 1)
      exact matchedPhysical_row_bound hD hP R f u t hu γ M₀
        (matchedRadialWeight D γ Mout k) (matchedRadialWeight_pos D γ Mout k).le
        (K (k + 1)) (hK (k + 1)) hs h0 hc

end ContinuousFlexibility.Radial
