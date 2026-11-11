import ContinuousFlexibility.Radial.MatchedPartitionNormalization
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Actual L² reconstruction for modal block estimates

The normalized square partition reconstructs every actual modal L²
vector in norm. Applying the existing continuous inverse to these finite
source decompositions therefore converges to its actual value.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace
open ContinuousFlexibility.Statements

theorem matchedL2_norm_sq (μ : Measure ℝ) (u : Lp ℝ 2 μ) :
    ‖u‖ ^ 2 = ∫ r, u r ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact .of_forall (fun r => by simp only [Real.inner_apply]; ring)

theorem matchedModePartitionPiece_memLp {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (m : ℕ) (u : RadialModeL2 D) :
    MemLp (fun r => matchedPartitionCoefficient D m r * u r) 2
      (radialHilbertMeasure D) := by
  apply (Lp.memLp u).of_le
    ((matchedPartitionCoefficient_measurable hP m).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable u))
  have hcore : ∀ᵐ r ∂radialHilbertMeasure D, r ∈ radialCore D :=
    (radialHilbertMeasure_ae_iff hD).mpr (ae_restrict_mem measurableSet_Ioo)
  filter_upwards [hcore] with r hr
  have hc : matchedPartitionCoefficient D m r ≤ 1 := by
    simpa only [Finset.sum_singleton] using
      (matchedPartitionCoefficient_partial hP {m} hr).2
  rw [norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (matchedPartitionCoefficient_nonneg D m r)]
  exact (mul_le_mul_of_nonneg_right hc (norm_nonneg (u r))).trans_eq (one_mul _)

def matchedModePartitionPiece (D : ReferenceData)
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (m : ℕ) (u : RadialModeL2 D) : RadialModeL2 D :=
  (matchedModePartitionPiece_memLp hD hP m u).toLp
    (fun r => matchedPartitionCoefficient D m r * u r)

theorem matchedModePartitionPiece_ae (D : ReferenceData)
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (m : ℕ) (u : RadialModeL2 D) :
    (matchedModePartitionPiece D hD hP m u : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (fun r => matchedPartitionCoefficient D m r * u r) :=
  (matchedModePartitionPiece_memLp hD hP m u).coeFn_toLp

theorem matchedModePartition_sum_ae (D : ReferenceData)
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (s : Finset ℕ) (u : RadialModeL2 D) :
    ((∑ m ∈ s, matchedModePartitionPiece D hD hP m u) : ℝ → ℝ)
      =ᵐ[radialHilbertMeasure D]
        (fun r => (∑ m ∈ s, matchedPartitionCoefficient D m r) * u r) := by
  have hall : ∀ᵐ r ∂radialHilbertMeasure D, ∀ m : ℕ,
      matchedModePartitionPiece D hD hP m u r = matchedPartitionCoefficient D m r * u r :=
    ae_all_iff.mpr (fun m => matchedModePartitionPiece_ae D hD hP m u)
  filter_upwards [Lp.coeFn_fun_finsetSum s (fun m => matchedModePartitionPiece D hD hP m u),
    hall] with r hsum hpieces
  calc
    _ = ∑ m ∈ s, matchedModePartitionPiece D hD hP m u r := hsum
    _ = ∑ m ∈ s, matchedPartitionCoefficient D m r * u r :=
      Finset.sum_congr rfl (fun m _ => hpieces m)
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem matchedModePartition_sum_sub_norm_sq (D : ReferenceData)
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (s : Finset ℕ) (u : RadialModeL2 D) :
    ‖(∑ m ∈ s, matchedModePartitionPiece D hD hP m u) - u‖ ^ 2 =
      ∫ r, ((∑ m ∈ s, matchedPartitionCoefficient D m r) - 1) ^ 2 * u r ^ 2
        ∂radialHilbertMeasure D := by
  rw [matchedL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (∑ m ∈ s, matchedModePartitionPiece D hD hP m u) u,
    matchedModePartition_sum_ae D hD hP s u] with r hsub hsum
  simp only [Pi.sub_apply] at hsub
  rw [hsub, hsum]
  ring

/-- Norm convergence, not merely pointwise reconstruction of representatives. -/
theorem matchedModePartition_sum_tendsto (D : ReferenceData)
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D) (u : RadialModeL2 D) :
    Tendsto (fun N => ∑ m ∈ Finset.range N, matchedModePartitionPiece D hD hP m u)
      atTop (𝓝 u) := by
  let a : ℕ → ℝ → ℝ := fun N r =>
    (∑ m ∈ Finset.range N, matchedPartitionCoefficient D m r) - 1
  have hcore : ∀ᵐ r ∂radialHilbertMeasure D, r ∈ radialCore D :=
    (radialHilbertMeasure_ae_iff hD).mpr (ae_restrict_mem measurableSet_Ioo)
  have hI : Tendsto
      (fun N => ∫ r, a N r ^ 2 * u r ^ 2 ∂radialHilbertMeasure D)
      atTop (𝓝 (∫ _r, (0 : ℝ) ∂radialHilbertMeasure D)) := by
    apply tendsto_integral_of_dominated_convergence (fun r => u r ^ 2)
    · intro N
      have ha : Measurable (fun r => a N r ^ 2) :=
        ((Finset.measurable_sum _ (fun m _ =>
          matchedPartitionCoefficient_measurable hP m)).sub measurable_const).pow_const 2
      exact ha.aestronglyMeasurable.mul (Lp.memLp u).integrable_sq.aestronglyMeasurable
    · exact (Lp.memLp u).integrable_sq
    · intro N
      filter_upwards [hcore] with r hr
      have hc := matchedPartitionCoefficient_partial hP (Finset.range N) hr
      have ha : a N r ^ 2 ≤ 1 := by dsimp only [a]; nlinarith [hc.1, hc.2]
      change ‖a N r ^ 2 * u r ^ 2‖ ≤ u r ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact (mul_le_mul_of_nonneg_right ha (sq_nonneg (u r))).trans_eq (one_mul _)
    · filter_upwards [hcore] with r hr
      have hc : Tendsto
          (fun N => ∑ m ∈ Finset.range N, matchedPartitionCoefficient D m r)
          atTop (𝓝 (1 : ℝ)) := by
        rw [← matchedPartitionCoefficient_tsum hP hr]
        exact (matchedPartitionCoefficient_summable hP r).hasSum.tendsto_sum_nat
      have ha := ((hc.sub_const 1).pow 2).mul_const (u r ^ 2)
      simpa only [a, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul] using ha
  simp only [integral_zero] at hI
  have hsq : Tendsto
      (fun N => ‖(∑ m ∈ Finset.range N, matchedModePartitionPiece D hD hP m u) - u‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simp_rw [matchedModePartition_sum_sub_norm_sq]
    exact hI
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have he :
      (fun N => Real.sqrt
        (‖(∑ m ∈ Finset.range N, matchedModePartitionPiece D hD hP m u) - u‖ ^ 2)) =
      (fun N => ‖(∑ m ∈ Finset.range N, matchedModePartitionPiece D hD hP m u) - u‖) := by
    funext N
    exact Real.sqrt_sq (norm_nonneg _)
  change Tendsto (fun N => Real.sqrt
    (‖(∑ m ∈ Finset.range N, matchedModePartitionPiece D hD hP m u) - u‖ ^ 2))
    atTop (𝓝 (Real.sqrt 0)) at hsqrt
  rw [he, Real.sqrt_zero] at hsqrt
  exact (tendsto_iff_norm_sub_tendsto_zero).mpr hsqrt

/-- The scalar border is retained once, separately from every radial cell. -/
theorem matchedModePartition_pair_tendsto (D : ReferenceData)
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D) (U : RadialModePair D) :
    Tendsto (fun N =>
      ((∑ m ∈ Finset.range N, matchedModePartitionPiece D hD hP m U.1), U.2))
      atTop (𝓝 U) :=
  (matchedModePartition_sum_tendsto D hD hP U.1).prodMk_nhds tendsto_const_nhds

/-- Continuous application identifies the reconstructed solution with the
existing inverse, rather than a newly postulated weighted operator. -/
theorem matchedModePartition_apply_tendsto (D : ReferenceData)
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (G : RadialModePair D →L[ℝ] RadialModePair D) (U : RadialModePair D) :
    Tendsto (fun N => G
      ((∑ m ∈ Finset.range N, matchedModePartitionPiece D hD hP m U.1), U.2))
      atTop (𝓝 (G U)) :=
  (G.continuous.tendsto U).comp (matchedModePartition_pair_tendsto D hD hP U)

end ContinuousFlexibility.Radial
