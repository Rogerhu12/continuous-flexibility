import ContinuousFlexibility.Radial.MatchedOuterPoissonIdentification
import ContinuousFlexibility.Radial.MatchedOuterNaturalRealization
import ContinuousFlexibility.Radial.MatchedOuterGlobalCells

/-!
# Actual outer columns are independent of the orientation of the natural line

Two unit boundary states defining the same Robin line differ only by a
sign.  The existing outer decomposition identifies the supplied actual
natural vector with that signed matching column. Every localized norm
therefore agrees, without requiring equality of the chosen unit states.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem matchedOuterPoisson_norm_eq_unit_candidate {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (hM : MatchingLocalRealizations D M)
    (ha : D.a < M.innerLeft) (hm : M.innerLeft < M.innerRight)
    (hb : M.innerRight < D.b) (hscale : ∀ k, 0 < M.boundaryScale k)
    (hdiag : ∀ k l, k ≠ l → M.A k l = 0 ∧ M.B k l = 0)
    (hnorm : ∀ k, M.A k k ^ 2 + M.B k k ^ 2 = 1)
    (i : Fin 2) {P : RadialModePair D} {p : ℝ → ℝ} {z : ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2 ^ 2 = 1)
    (hline : ∀ q, outerStatePair z q = 0 ↔
      outerStatePair (M.A i i, M.B i i) q = 0)
    (hEq : ModeLocalEquation D M.frequency (matchingOuterRegion D M) P 0)
    (hscalar : P.2 = 0)
    (hp : (P.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] p)
    (hinside : ∀ r ∈ Ioo M.innerLeft M.innerRight, p r = 0)
    (hreg : ContDiffOn ℝ 1 p (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b))
    (htrace : ∀ k : Fin 2,
      p (matchingCut D M k) = (if k = i then z.1 else 0) / sqrt (M.boundaryScale k) ∧
        matchingOuterFlux D M p k = if k = i then z.2 else 0) :
    ∀ T : RadialModePair D →L[ℝ] RadialModePair D,
      ‖T (M.outerPoisson i)‖ = ‖T P‖ := by
  classical
  let a := outerStatePair (M.A i i, M.B i i) z
  have horth := (hline (outerStatePerp z)).mp (outerStatePair_perp z)
  change M.A i i * (-z.2) + M.B i i * z.1 = 0 at horth
  have hid : a ^ 2 + (M.A i i * (-z.2) + M.B i i * z.1) ^ 2 =
      (M.A i i ^ 2 + M.B i i ^ 2) * (z.1 ^ 2 + z.2 ^ 2) := by
    dsimp only [a, outerStatePair]
    ring
  have ha₂ : a ^ 2 = 1 := by
    simpa only [horth, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero, hnorm i, hz, one_mul]
      using hid
  have habs : |a| = 1 := by
    calc
      |a| = sqrt (a ^ 2) := (sqrt_sq_eq_abs a).symm
      _ = 1 := by rw [ha₂, sqrt_one]
  have hc (k : Fin 2) :
      M.A k k * sqrt (M.boundaryScale k) * p (matchingCut D M k) +
        M.B k k * matchingOuterFlux D M p k = if k = i then a else 0 := by
    rw [(htrace k).1, (htrace k).2]
    by_cases hki : k = i
    · subst k
      simp only [ite_true]
      dsimp only [a, outerStatePair]
      field_simp [(sqrt_pos.mpr (hscale i)).ne']
    · simp only [if_neg hki, zero_div, mul_zero, add_zero]
  have hzero : (P.1 : ℝ → ℝ) =ᵐ[
      (radialHilbertMeasure D).restrict (Ioo M.innerLeft M.innerRight)] fun _ => 0 := by
    filter_upwards [hp.restrict, ae_restrict_mem measurableSet_Ioo] with r hr hmem
    rw [hr, hinside r hmem]
  have hsum :
      (∑ k,
        (M.A k k * sqrt (M.boundaryScale k) * p (matchingCut D M k) +
          M.B k k * matchingOuterFlux D M p k) • M.outerPoisson k) =
        a • M.outerPoisson i := by
    rw [Finset.sum_eq_single i]
    · rw [hc, if_pos rfl]
    · intro k _ hki
      rw [hc, if_neg hki, zero_smul]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have he := matching_outerInverse_eq_sub_poisson hD hM ha hm hb hscale hdiag hnorm
    hEq hscalar hp.restrict hzero hreg
  rw [map_zero, hsum] at he
  have hP : P = a • M.outerPoisson i := sub_eq_zero.mp he.symm
  intro T
  rw [hP, map_smul, norm_smul, Real.norm_eq_abs, habs, one_mul]

/-- The actual first-order natural solution supplies all hypotheses of the
preceding identity.  The matching column itself is kept unchanged. -/
theorem matchedOuterPoisson_norm_eq_natural {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hBorder : RadialTrueBorder D)
    {M : RadialMatchingData D} (hM : MatchingLocalRealizations D M)
    (ha : D.a < M.innerLeft) (hm : M.innerLeft < M.innerRight)
    (hb : M.innerRight < D.b) (hscale : ∀ k, 0 < M.boundaryScale k)
    (hdiag : ∀ k l, k ≠ l → M.A k l = 0 ∧ M.B k l = 0)
    (hnorm : ∀ k, M.A k k ^ 2 + M.B k k ^ 2 = 1)
    (right : Bool) {c : ℝ} {P ZP Q ZQ : ℝ → ℝ}
    (H : OuterFundamentalStatePair
      (fun x => M.boundaryScale (if right then 1 else 0) / outerTailOutwardWeight D right x)
      (fun x => (M.frequency : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x /
        (M.boundaryScale (if right then 1 else 0) * x))
      P ZP Q ZQ (outerOutwardRadius right (if right then M.innerRight else M.innerLeft)) c
      (outerOutwardRadius right (tailPhysicalEndpoint D right)))
    (hV : MemLp H.V 2 (outerWholeMeasure D right
      (if right then M.innerRight else M.innerLeft)))
    (hline : ∀ q, outerStatePair H.entrance q = 0 ↔
      outerStatePair (M.A (if right then 1 else 0) (if right then 1 else 0),
        M.B (if right then 1 else 0) (if right then 1 else 0)) q = 0)
    (T : RadialModePair D →L[ℝ] RadialModePair D) :
    ‖T (M.outerPoisson (if right then 1 else 0))‖ =
      ‖T (matchedOuterNaturalPoisson D right
        (if right then M.innerRight else M.innerLeft)
        (M.boundaryScale (if right then 1 else 0)) H.V hV)‖ := by
  obtain ⟨hrep, _, hreg, hscalar, heq, htrace⟩ :=
    matchedOuterNatural_side_realization hD hBorder ha hm hb right
      (hscale _) H hV
  exact matchedOuterPoisson_norm_eq_unit_candidate hD hM ha hm hb hscale hdiag hnorm
    (if right then 1 else 0) H.unit hline heq hscalar hrep
    (fun r hr => matchedOuterNaturalFunction_inner M right _ H.V hr)
    (hreg.of_le (by norm_num)) htrace T

/-- The actual global natural candidate has exactly its whole-tail cell
norm; the extension contributes neither a factor nor an extra cell. -/
theorem norm_matchedModeCell_naturalPoisson
    (D : ReferenceData) (hP : RadialPartition D) (right : Bool)
    (entry lam : ℝ) (V : ℝ → ℝ)
    (hV : MemLp V 2 (outerWholeMeasure D right entry)) (m : ℕ) :
    ‖matchedModeCell D hP m (matchedOuterNaturalPoisson D right entry lam V hV)‖ =
      ‖matchedOuterCell D hP right (outerWholeMeasure D right entry) m
        ((sqrt lam)⁻¹ • hV.toLp V)‖ := by
  rw [matchedModeCell_apply, matchedOuterNaturalPoisson, Prod.norm_def,
    norm_zero, max_eq_left (norm_nonneg _), norm_matchedOuterWholeExtend_cell]

end ContinuousFlexibility.Radial
