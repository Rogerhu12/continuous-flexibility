import ContinuousFlexibility.Analysis.N05ReferenceLowAngularBasis
import ContinuousFlexibility.Radial.ReferenceGraphCoefficients
import ContinuousFlexibility.Radial.ReferenceWeightedMeasure

/-!
# The low angular jets keep the original output weights

The positive frequency coefficient is that of the original output. Its
weighted norm is bounded by the true remainder norm. The mean disappears
at positive derivative order, and the bordered mode contributes only 2^(2b).
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped BigOperators
open ContinuousFlexibility.Statements

theorem n05_referenceLowCoefficient_output_bound {D : ReferenceData}
    (hab : D.a ≤ D.b) (hpart : RadialPartition D)
    {γ M a : ℝ} {U : RadialUnknown} (hU : OutputRealization D γ M a U) :
    (∑' m, Real.exp (-2 * M * radialQ (D.cellIndex m) +
        2 * γ * radialS (D.cellIndex m)) *
      ∫ r, (D.localizer m r * referenceRadialCoefficient U.1 1 r) ^ 2
        ∂volume.restrict (radialCore D)) ≤ outputNormSquare D γ M a U := by
  have hc := referenceRadialCoefficient_output_weighted hab hpart hU
    (n := 1) (by decide)
  have he := referenceRadialCoefficient_output_remainder_ae hpart hU
    (n := 1) (by decide)
  have hcell (m : ℕ) :
      (∫ r, (D.localizer m r * referenceRadialCoefficient U.1 1 r) ^ 2
        ∂volume.restrict (radialCore D)) ≤
          referenceCellSquare D m (outputRemainder D a U) := by
    calc
      (∫ r, (D.localizer m r * referenceRadialCoefficient U.1 1 r) ^ 2
          ∂volume.restrict (radialCore D)) =
          ∫ r, (D.localizer m r *
            referenceRadialCoefficient (outputRemainder D a U) 1 r) ^ 2
              ∂volume.restrict (radialCore D) := by
        apply integral_congr_ae
        filter_upwards [he] with r hr
        rw [hr]
      _ ≤ _ := referenceRadialCoefficient_cell_sq_le hab hU.1 1 m
  have hsum := Summable.tsum_le_tsum
    (fun m => mul_le_mul_of_nonneg_left (hcell m) (Real.exp_pos _).le) hc.2 hU.2.1
  calc
    _ ≤ ∑' m, outputCellSquare D γ M (outputRemainder D a U) m := hsum
    _ ≤ outputNormSquare D γ M a U := by
      unfold outputNormSquare
      nlinarith only [sq_nonneg a, sq_nonneg U.2]

theorem n05_referenceLowAngularJet_cell_parseval {D : ReferenceData}
    (hab : D.a ≤ D.b) {u : PolarPoint → ℝ}
    (hc : ∀ m, MemLp (fun r => D.localizer m r * referenceRadialCoefficient u 1 r)
      2 (volume.restrict (radialCore D))) {b : ℕ} (hb : 0 < b) :
    RadialCellIntegrable D (n05_referenceLowAngularJet b u) ∧
      ∀ m, referenceCellSquare D m (n05_referenceLowAngularJet b u) =
        (2 : ℝ) ^ (2 * b) *
          ∫ r, (D.localizer m r * referenceRadialCoefficient u 1 r) ^ 2
            ∂volume.restrict (radialCore D) := by
  have hsyn : n05_referenceLowAngularJet b u =
      r11bFiniteSynthesis ({0} : Finset ℕ)
        (fun _ r => (2 : ℝ) ^ b * referenceRadialCoefficient u 1 r)
        (fun _ => n05_referenceLowJetBasis b) := by
    funext x
    simp only [n05_referenceLowAngularJet_apply hb,
      r11bFiniteSynthesis, Finset.sum_singleton]
  have hcoeff (i : ℕ) (_hi : i ∈ ({0} : Finset ℕ)) (m : ℕ) :
      MemLp (fun r => D.localizer m r *
        ((2 : ℝ) ^ b * referenceRadialCoefficient u 1 r)) 2
          (volume.restrict (radialCore D)) := by
    have he : (fun r => D.localizer m r *
        ((2 : ℝ) ^ b * referenceRadialCoefficient u 1 r)) =
        fun r => (2 : ℝ) ^ b *
          (D.localizer m r * referenceRadialCoefficient u 1 r) := by
      funext r
      ring
    rw [he]
    exact (hc m).const_mul _
  have horth (i : ℕ) (hi : i ∈ ({0} : Finset ℕ))
      (j : ℕ) (hj : j ∈ ({0} : Finset ℕ)) :
      angularPairing (n05_referenceLowJetBasis b) (n05_referenceLowJetBasis b) =
        if i = j then 1 else 0 := by
    simp only [Finset.mem_singleton] at hi hj
    subst i
    subst j
    simpa only [ite_true] using n05_referenceLowJetBasis_pairing b
  obtain ⟨hcell, henergy⟩ := r11b_finiteSynthesis_cell_parseval_of_localized hab
    ({0} : Finset ℕ) (fun _ r => (2 : ℝ) ^ b * referenceRadialCoefficient u 1 r)
    (fun _ => n05_referenceLowJetBasis b) hcoeff
    (fun _ _ => n05_referenceLowJetBasis_memLp b) horth
  refine ⟨by simpa only [hsyn] using hcell, fun m => ?_⟩
  rw [hsyn, henergy, Finset.sum_singleton]
  have he : (fun r => (D.localizer m r *
      ((2 : ℝ) ^ b * referenceRadialCoefficient u 1 r)) ^ 2) =
      fun r => (2 : ℝ) ^ (2 * b) *
        (D.localizer m r * referenceRadialCoefficient u 1 r) ^ 2 := by
    funext r
    rw [Nat.mul_comm 2 b, pow_mul]
    ring
  rw [he, integral_const_mul]

theorem n05_referenceLowAngularJet_output_bound {D : ReferenceData}
    (hab : D.a ≤ D.b) (hpart : RadialPartition D)
    {γ M a : ℝ} {U : RadialUnknown} (hU : OutputRealization D γ M a U)
    {b : ℕ} (hb : 0 < b) :
    MemLp (n05_referenceLowAngularJet b U.1) 2 (referenceWeightedMeasure D γ (-M)) ∧
      outputNormSquare D γ M 0 (n05_referenceLowAngularJet b U.1, 0) ≤
        (2 : ℝ) ^ (2 * b) * outputNormSquare D γ M a U := by
  have hcoef := referenceRadialCoefficient_output_weighted hab hpart hU
    (n := 1) (by decide)
  obtain ⟨hc, he⟩ := n05_referenceLowAngularJet_cell_parseval hab hcoef.1 hb
  have hs : Summable (outputCellSquare D γ M (n05_referenceLowAngularJet b U.1)) := by
    apply (hcoef.2.mul_left ((2 : ℝ) ^ (2 * b))).congr
    intro m
    dsimp only [outputCellSquare]
    rw [he]
    ring
  have hw : MemLp (n05_referenceLowAngularJet b U.1) 2
      (referenceWeightedMeasure D γ (-M)) := by
    apply memLp_referenceWeightedMeasure hab hpart hc
    simpa only [sourceCellSquare_neg_fun] using hs
  have hn : outputNormSquare D γ M 0 (n05_referenceLowAngularJet b U.1, 0) =
      (2 : ℝ) ^ (2 * b) *
        ∑' m, Real.exp (-2 * M * radialQ (D.cellIndex m) +
          2 * γ * radialS (D.cellIndex m)) *
          ∫ r, (D.localizer m r * referenceRadialCoefficient U.1 1 r) ^ 2
            ∂volume.restrict (radialCore D) := by
    have hzero : outputRemainder D 0 (n05_referenceLowAngularJet b U.1, 0) =
        n05_referenceLowAngularJet b U.1 := by
      funext p
      simp only [outputRemainder, zero_mul, sub_zero]
    simp only [outputNormSquare, hzero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, outputCellSquare]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    rw [he]
    ring
  refine ⟨hw, ?_⟩
  rw [hn]
  exact mul_le_mul_of_nonneg_left (n05_referenceLowCoefficient_output_bound hab hpart hU)
    (by positivity)

end ContinuousFlexibility.Radial
