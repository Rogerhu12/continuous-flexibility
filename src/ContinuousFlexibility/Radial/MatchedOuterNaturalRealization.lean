import ContinuousFlexibility.Radial.MatchedOuterNaturalColumns
import ContinuousFlexibility.Radial.MatchedPiecesAssembly

/-!
# The natural-column clauses of the same matching datum

The two columns are the actual normalized whole-tail natural vectors.
Their physical representatives are zero in the open inner interval and
on the opposite side. The first-order system proves their homogeneous
modal equations and both cut traces, including when an entrance value is
zero. The final theorem fills the fifth group of MatchingOuterRealizations
using only the constructor's field identities.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem matchedOuterNatural_side_realization {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {M : RadialMatchingData D} (ha : D.a < M.innerLeft)
    (hm : M.innerLeft < M.innerRight) (hb : M.innerRight < D.b)
    (right : Bool) {c : ℝ} {P ZP Q ZQ : ℝ → ℝ}
    (hlam : 0 < M.boundaryScale (if right then 1 else 0))
    (H : OuterFundamentalStatePair
      (fun x => M.boundaryScale (if right then 1 else 0) /
        outerTailOutwardWeight D right x)
      (fun x => (M.frequency : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x /
        (M.boundaryScale (if right then 1 else 0) * x))
      P ZP Q ZQ
      (outerOutwardRadius right (if right then M.innerRight else M.innerLeft)) c
      (outerOutwardRadius right (tailPhysicalEndpoint D right)))
    (hV : MemLp H.V 2 (outerWholeMeasure D right
      (if right then M.innerRight else M.innerLeft))) :
    let U := matchedOuterNaturalPoisson D right
      (if right then M.innerRight else M.innerLeft)
      (M.boundaryScale (if right then 1 else 0)) H.V hV
    let u := matchedOuterNaturalFunction M right
      (M.boundaryScale (if right then 1 else 0)) H.V
    (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u ∧
      (U.1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
        (Ioo M.innerLeft M.innerRight)] (fun _ => 0) ∧
      ContDiffOn ℝ 2 u (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b) ∧
      U.2 = 0 ∧
      ModeLocalEquation D M.frequency (matchingOuterRegion D M) U 0 ∧
      ∀ k : Fin 2,
        u (matchingCut D M k) =
          (if k = (if right then 1 else 0) then H.entrance.1 else 0) /
            sqrt (M.boundaryScale k) ∧
        matchingOuterFlux D M u k =
          (if k = (if right then 1 else 0) then H.entrance.2 else 0) := by
  let entry : ℝ := if right then M.innerRight else M.innerLeft
  let lam : ℝ := M.boundaryScale (if right then 1 else 0)
  let U := matchedOuterNaturalPoisson D right entry lam H.V hV
  let u := matchedOuterNaturalFunction M right lam H.V
  have hentry : entry ∈ radialCore D := by
    cases right
    · exact ⟨ha, hm.trans hb⟩
    · exact ⟨ha.trans hm, hb⟩
  have hotherEntry : (if right then M.innerLeft else M.innerRight) ∈ radialCore D := by
    cases right
    · exact ⟨ha.trans hm, hb⟩
    · exact ⟨ha, hm.trans hb⟩
  have hstate := matchedOuterNatural_state hD hentry hlam H
  have hzero : ((0 : RadialModePair D).1 : ℝ → ℝ)
      =ᵐ[radialHilbertMeasure D] (fun _ => 0) :=
    Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D)
  have hactive : ModeLocalEquation D M.frequency
      (radialTailInterval D right entry) U 0 := by
    apply matchedOuterWhole_modeLocalEquation hD hB hentry (U := U) (F := 0)
      (u := fun x => H.V x / sqrt lam) (f := fun _ => 0) rfl
    · exact matchedOuterNaturalPoisson_ae_on D right entry lam H.V hV
        (by cases right <;> exact measurableSet_Ioo) (Subset.refl _)
    · exact hzero.filter_mono (Measure.restrict_le_self).ae_le
    · exact hstate.1.of_le (by simp)
    · simpa only [mul_zero, sub_zero] using hstate.2.1
  have hother : ModeLocalEquation D M.frequency
      (radialTailInterval D (!right) (if right then M.innerLeft else M.innerRight)) U 0 := by
    apply matchedOuterWhole_modeLocalEquation hD hB hotherEntry (U := U) (F := 0)
      (u := fun _ => 0) (f := fun _ => 0) rfl
    · exact matchedOuterNaturalPoisson_other_zero hm right lam H.V hV
    · exact hzero.filter_mono (Measure.restrict_le_self).ae_le
    · exact contDiffOn_const
    · intro ψ hψ hc hs
      simp only [deriv_const, mul_zero, sub_zero, integral_zero, neg_zero]
  refine ⟨matchedOuterNaturalPoisson_representative hD hm right lam H.V hV,
    matchedOuterNaturalPoisson_inner_zero M right lam H.V hV,
    matchedOuterNaturalFunction_contDiffOn hm right lam H.V (hstate.1.of_le (by simp)),
    rfl, ?_, ?_⟩
  · cases right
    · exact modeLocalEquation_matchingOuter_of_sides hD hB hm hactive hother
    · exact modeLocalEquation_matchingOuter_of_sides hD hB hm hother hactive
  · cases right
    · intro k
      fin_cases k
      · constructor
        · change matchedOuterSideGlue M.innerLeft M.innerRight
            (fun r => H.V (outerOutwardRadius false r) / sqrt (M.boundaryScale 0))
            (fun _ => 0) M.innerLeft = H.entrance.1 / sqrt (M.boundaryScale 0)
          rw [matchedOuterSideGlue_of_le _ _ le_rfl]
          exact hstate.2.2.1
        · have hflux := matchedOuterSideGlue_flux_left ha hm hb
            (fun r => H.V (outerOutwardRadius false r) / sqrt (M.boundaryScale 0))
            (fun _ => 0)
          calc
            matchingOuterFlux D M u 0 =
                D.w M.innerLeft *
                  derivWithin (fun x => H.V x / sqrt (M.boundaryScale 0))
                    (Ico (outerOutwardRadius false M.innerLeft)
                      (outerOutwardRadius false (tailPhysicalEndpoint D false)))
                    (outerOutwardRadius false M.innerLeft) /
                  sqrt (M.boundaryScale 0) := by
              simpa only [u, lam, matchedOuterNaturalFunction, Bool.false_eq_true,
                ite_false, outerOutwardRadius_twice] using hflux
            _ = H.entrance.2 := hstate.2.2.2
      · constructor
        · change matchedOuterSideGlue M.innerLeft M.innerRight
            (fun r => H.V (outerOutwardRadius false r) / sqrt (M.boundaryScale 0))
            (fun _ => 0) M.innerRight = 0 / sqrt (M.boundaryScale 1)
          rw [matchedOuterSideGlue_of_ge hm _ _ le_rfl, zero_div]
        · have hflux := matchedOuterSideGlue_flux_right ha hm hb
            (fun r => H.V (outerOutwardRadius false r) / sqrt (M.boundaryScale 0))
            (fun _ => 0)
          simpa only [u, lam, matchedOuterNaturalFunction, Bool.false_eq_true,
            ite_false, derivWithin_const, mul_zero, zero_div] using hflux
    · intro k
      fin_cases k
      · constructor
        · change matchedOuterSideGlue M.innerLeft M.innerRight (fun _ => 0)
            (fun r => H.V (outerOutwardRadius true r) / sqrt (M.boundaryScale 1))
            M.innerLeft = 0 / sqrt (M.boundaryScale 0)
          rw [matchedOuterSideGlue_of_le _ _ le_rfl, zero_div]
        · have hflux := matchedOuterSideGlue_flux_left ha hm hb
            (fun _ => 0)
            (fun r => H.V (outerOutwardRadius true r) / sqrt (M.boundaryScale 1))
          simpa only [u, lam, matchedOuterNaturalFunction, ite_true,
            derivWithin_const, mul_zero, zero_div] using hflux
      · constructor
        · change matchedOuterSideGlue M.innerLeft M.innerRight (fun _ => 0)
            (fun r => H.V (outerOutwardRadius true r) / sqrt (M.boundaryScale 1))
            M.innerRight = H.entrance.1 / sqrt (M.boundaryScale 1)
          rw [matchedOuterSideGlue_of_ge hm _ _ le_rfl]
          exact hstate.2.2.1
        · have hflux := matchedOuterSideGlue_flux_right ha hm hb
            (fun _ => 0)
            (fun r => H.V (outerOutwardRadius true r) / sqrt (M.boundaryScale 1))
          calc
            matchingOuterFlux D M u 1 =
                D.w M.innerRight *
                  derivWithin (fun x => H.V x / sqrt (M.boundaryScale 1))
                    (Ico (outerOutwardRadius true M.innerRight)
                      (outerOutwardRadius true (tailPhysicalEndpoint D true)))
                    (outerOutwardRadius true M.innerRight) /
                  sqrt (M.boundaryScale 1) := by
              simpa only [u, lam, matchedOuterNaturalFunction, ite_true,
                outerOutwardRadius_twice] using hflux
            _ = H.entrance.2 := hstate.2.2.2

/-- These are precisely the natural-column clauses of the existing
MatchingOuterRealizations. The hypotheses identify constructor fields;
all analytic and boundary conclusions are proved for the same columns.
For an actual whole-tail Green construction, take hV right to be its
natural_memLp field. -/
theorem matchedOuterNaturalColumns_realization {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hBorder : RadialTrueBorder D)
    {M : RadialMatchingData D} (ha : D.a < M.innerLeft)
    (hm : M.innerLeft < M.innerRight) (hb : M.innerRight < D.b)
    {c : Bool → ℝ} {P ZP Q ZQ : Bool → ℝ → ℝ}
    (hlam : ∀ i, 0 < M.boundaryScale i)
    (H : ∀ right : Bool, OuterFundamentalStatePair
      (fun x => M.boundaryScale (if right then 1 else 0) /
        outerTailOutwardWeight D right x)
      (fun x => (M.frequency : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x /
        (M.boundaryScale (if right then 1 else 0) * x))
      (P right) (ZP right) (Q right) (ZQ right)
      (outerOutwardRadius right (if right then M.innerRight else M.innerLeft)) (c right)
      (outerOutwardRadius right (tailPhysicalEndpoint D right)))
    (hV : ∀ right : Bool, MemLp (H right).V 2 (outerWholeMeasure D right
      (if right then M.innerRight else M.innerLeft)))
    (hPoisson : ∀ right : Bool, M.outerPoisson (if right then 1 else 0) =
      matchedOuterNaturalPoisson D right
        (if right then M.innerRight else M.innerLeft)
        (M.boundaryScale (if right then 1 else 0)) (H right).V (hV right))
    (hFunction : ∀ right : Bool, M.outerFunction (if right then 1 else 0) =
      matchedOuterNaturalFunction M right
        (M.boundaryScale (if right then 1 else 0)) (H right).V)
    (hA : ∀ right : Bool,
      M.A (if right then 1 else 0) (if right then 1 else 0) = (H right).entrance.1)
    (hB : ∀ right : Bool,
      M.B (if right then 1 else 0) (if right then 1 else 0) = (H right).entrance.2)
    (hoff : ∀ k i, k ≠ i → M.A k i = 0 ∧ M.B k i = 0) :
    ∀ i,
      ((M.outerPoisson i).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] M.outerFunction i ∧
      ((M.outerPoisson i).1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
        (Ioo M.innerLeft M.innerRight)] (fun _ => 0) ∧
      ContDiffOn ℝ 2 (M.outerFunction i)
        (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b) ∧
      (M.outerPoisson i).2 = 0 ∧
      ModeLocalEquation D M.frequency (matchingOuterRegion D M) (M.outerPoisson i) 0 ∧
      ∀ k, M.outerFunction i (matchingCut D M k) = M.A k i / sqrt (M.boundaryScale k) ∧
        matchingOuterFlux D M (M.outerFunction i) k = M.B k i := by
  intro i
  obtain ⟨right, rfl⟩ : ∃ right : Bool, (if right then (1 : Fin 2) else 0) = i := by
    fin_cases i
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  rw [hPoisson right, hFunction right]
  obtain ⟨hrep, hzero, hreg, hscalar, heq, htrace⟩ :=
    matchedOuterNatural_side_realization hD hBorder ha hm hb right
      (hlam _) (H right) (hV right)
  refine ⟨hrep, hzero, hreg, hscalar, heq, ?_⟩
  intro k
  have hAk : M.A k (if right then 1 else 0) =
      (if k = (if right then 1 else 0) then (H right).entrance.1 else 0) := by
    by_cases hk : k = (if right then 1 else 0)
    · subst k
      simpa only [ite_true] using hA right
    · rw [if_neg hk]
      exact (hoff k _ hk).1
  have hBk : M.B k (if right then 1 else 0) =
      (if k = (if right then 1 else 0) then (H right).entrance.2 else 0) := by
    by_cases hk : k = (if right then 1 else 0)
    · subst k
      simpa only [ite_true] using hB right
    · rw [if_neg hk]
      exact (hoff k _ hk).2
  rw [hAk, hBk]
  exact htrace k

end ContinuousFlexibility.Radial
