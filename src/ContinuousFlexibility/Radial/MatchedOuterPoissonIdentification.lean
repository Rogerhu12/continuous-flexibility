import ContinuousFlexibility.Radial.MatchingOuterDecomposition

/-!
# Identifying the actual outer Poisson columns

A square-integrable homogeneous candidate with the normalized Robin
datum is the Poisson column already stored in the matching data.
The proof uses the actual outer inverse and its separated-graph
uniqueness. Thus quantitative bounds for a constructed physical
candidate apply to that same matching column.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem matchedOuterPoisson_eq_of_candidate {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (hM : MatchingLocalRealizations D M)
    (ha : D.a < M.innerLeft) (hm : M.innerLeft < M.innerRight)
    (hb : M.innerRight < D.b) (hscale : ∀ k, 0 < M.boundaryScale k)
    (hdiag : ∀ k l, k ≠ l → M.A k l = 0 ∧ M.B k l = 0)
    (hnorm : ∀ k, M.A k k ^ 2 + M.B k k ^ 2 = 1)
    (i : Fin 2) {P : RadialModePair D} {p : ℝ → ℝ}
    (hEq : ModeLocalEquation D M.frequency (matchingOuterRegion D M) P 0)
    (hscalar : P.2 = 0)
    (hp : (P.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] p)
    (hinside : ∀ r ∈ Ioo M.innerLeft M.innerRight, p r = 0)
    (hreg : ContDiffOn ℝ 1 p (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b))
    (htrace : ∀ k,
      M.A k k * Real.sqrt (M.boundaryScale k) * p (matchingCut D M k) +
        M.B k k * matchingOuterFlux D M p k = if i = k then 1 else 0) :
    M.outerPoisson i = P := by
  classical
  have hz : (P.1 : ℝ → ℝ) =ᵐ[
      (radialHilbertMeasure D).restrict (Ioo M.innerLeft M.innerRight)] fun _ => 0 := by
    filter_upwards [hp.restrict, ae_restrict_mem measurableSet_Ioo] with r hr hmem
    rw [hr, hinside r hmem]
  have hsum :
      (∑ k,
        (M.A k k * Real.sqrt (M.boundaryScale k) * p (matchingCut D M k) +
          M.B k k * matchingOuterFlux D M p k) • M.outerPoisson k) =
        M.outerPoisson i := by
    rw [Finset.sum_eq_single i]
    · rw [htrace]
      simp only [ite_true, one_smul]
    · intro k _ hki
      rw [htrace, if_neg hki.symm, zero_smul]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have he := matching_outerInverse_eq_sub_poisson hD hM ha hm hb hscale hdiag hnorm
    hEq hscalar hp.restrict hz hreg
  rw [map_zero, hsum] at he
  exact (sub_eq_zero.mp he.symm).symm

end ContinuousFlexibility.Radial
