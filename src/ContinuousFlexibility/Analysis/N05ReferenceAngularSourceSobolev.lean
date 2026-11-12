import ContinuousFlexibility.Analysis.N05ReferenceAngularWeakCoefficients
import ContinuousFlexibility.Analysis.N05ReferenceAngularWeighted
import ContinuousFlexibility.Analysis.N05ReferenceAngularJetCells
import ContinuousFlexibility.Radial.R11bWeightedBessel
import ContinuousFlexibility.Radial.R11bGlobalL2

/-!
# Actual weak source jets supply the angular square sum

Weighted Bessel applies to the actual derivative field, without any parity
or compatibility requirement on that field. The weak coefficient identity
then gives summability and the bound for the original source coefficients.
Thus the angular source hypothesis is expressed in physical Sobolev terms.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped BigOperators
open ContinuousFlexibility.Statements

theorem n05_referenceHighWeakJet_cell_square {D : ReferenceData}
    (hab : D.a ≤ D.b) {u d : PolarPoint → ℝ} {b : ℕ}
    (huc : RadialCellIntegrable D u)
    (hu : MemLp u 2 (radialPhysicalMeasure D))
    (hd : MemLp d 2 (radialPhysicalMeasure D))
    (hder : n05_weakReferenceAngularJet D u d b) (n m : ℕ) :
    (∫ r, (D.localizer m r * n05_referenceHighJetCoefficient d b n r) ^ 2
      ∂volume.restrict (radialCore D)) =
      (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
        referenceCellSquare D m (referenceBasisProjection {n + 2} u) := by
  rw [n05_referenceHighProjection_cell_square hab huc]
  have hc := n05_referenceHighJetCoefficient_ae hab hu hd hder n
  calc
    (∫ r, (D.localizer m r * n05_referenceHighJetCoefficient d b n r) ^ 2
        ∂volume.restrict (radialCore D)) =
        ∫ r, (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
          (D.localizer m r * referenceRadialCoefficient u (n + 2) r) ^ 2
            ∂volume.restrict (radialCore D) := by
      apply integral_congr_ae
      filter_upwards [hc] with r hr
      rw [← hr, Nat.mul_comm 2 b, pow_mul]
      ring
    _ = _ := integral_const_mul _ _

theorem n05_referenceHighWeakJet_mode_energy {D : ReferenceData}
    (hab : D.a ≤ D.b) {γ M : ℝ} {F : RadialSource} {d : PolarPoint → ℝ} {b : ℕ}
    (hFc : RadialCellIntegrable D F.1)
    (hF : MemLp F.1 2 (radialPhysicalMeasure D))
    (hd : MemLp d 2 (radialPhysicalMeasure D))
    (hder : n05_weakReferenceAngularJet D F.1 d b) (n : ℕ) :
    (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
        n05_referenceHighSourceSquare D γ M F n =
      ∑' m, Real.exp (2 * M * radialQ (D.cellIndex m) +
          2 * γ * radialS (D.cellIndex m)) *
        ∫ r, (D.localizer m r * n05_referenceHighJetCoefficient d b n r) ^ 2
          ∂volume.restrict (radialCore D) := by
  simp only [n05_referenceHighSourceSquare, sourceNormSquare,
    zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, sourceCellSquare]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  rw [n05_referenceHighWeakJet_cell_square hab hFc hF hd hder]
  ring

/-- The high angular source energy is a conclusion of the actual weak
Sobolev hypothesis. No spectral summability assumption remains. -/
theorem n05_referenceHighWeakJet_source_summable_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M : ℝ} (hγ : 0 < γ)
    {F : RadialSource} (hF : SourceMember D γ M F)
    {d : PolarPoint → ℝ} {b : ℕ}
    (hd : SourceDerivativeMember D γ M d)
    (hder : n05_weakReferenceAngularJet D F.1 d b) :
    Summable (fun n => (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
      n05_referenceHighSourceSquare D γ M F n) ∧
      (∑' n, (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
        n05_referenceHighSourceSquare D γ M F n) ≤ sourceNormSquare D γ M (d, 0) := by
  have hab : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  have hFp := r11b_source_memLp hD hγ hF
  have hdp := r11b_sourceDerivative_memLp hD hγ hd
  have he (n : ℕ) := n05_referenceHighWeakJet_mode_energy
    (γ := γ) (M := M) hab hF.1 hFp hdp hder n
  have hnonneg (n : ℕ) :
      0 ≤ (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
        n05_referenceHighSourceSquare D γ M F n := by
    rw [he n]
    exact tsum_nonneg (fun m =>
      mul_nonneg (Real.exp_pos _).le (integral_nonneg fun r => sq_nonneg _))
  have hfinite (J : Finset ℕ) :
      (∑ n ∈ J, (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
        n05_referenceHighSourceSquare D γ M F n) ≤ sourceNormSquare D γ M (d, 0) := by
    obtain ⟨_, hb⟩ := r11b_weighted_cell_finite_bessel hab J
      (n05_referenceHighJetBasis b) hd.1
      (fun n _ => n05_referenceHighJetBasis_memLp b n)
      (fun i _ j _ => n05_referenceHighJetBasis_pairing b i j)
      (fun m => Real.exp (2 * M * radialQ (D.cellIndex m) +
        2 * γ * radialS (D.cellIndex m))) (fun m => (Real.exp_pos _).le) hd.2
    simp only [← n05_referenceHighJetCoefficient_eq_pairing] at hb
    simp_rw [he]
    simpa only [sourceNormSquare, sourceCellSquare,
      zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] using hb
  exact ⟨summable_of_sum_le hnonneg hfinite,
    Real.tsum_le_of_sum_le hnonneg hfinite⟩

end ContinuousFlexibility.Radial
