import ContinuousFlexibility.Radial.MatchingInnerDecomposition
import ContinuousFlexibility.Radial.MatchingOuterDecomposition
import ContinuousFlexibility.Radial.MatchingOuterCorePairing
import ContinuousFlexibility.Radial.MatchingInactiveScalar
import ContinuousFlexibility.Radial.ModeCoreInverse

/-!
# Exact inversion of the concrete smooth core

The inner and outer inverse decompositions identify the two remainders.
The actual Poisson trace pairings give the coefficients in the matching
matrix system. Its left inverse therefore recovers the smooth boundary
values and fluxes, and all Poisson corrections cancel exactly.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace
open ContinuousFlexibility.Statements

theorem matchingOuterFlux_eq_smoothBoundaryFlux {D : ReferenceData}
    {M : RadialMatchingData D} (ha : D.a < M.innerLeft)
    (hb : M.innerRight < D.b) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (i : Fin 2) :
    matchingOuterFlux D M ψ i = matchingSmoothBoundaryFlux D M ψ i := by
  unfold matchingOuterFlux matchingSmoothBoundaryFlux
  rw [(hψ.differentiable (by simp) (matchingCut D M i)).derivWithin
    (matchingOuter_uniqueDiffWithinAt ha hb i)]

theorem actualMatchedRepresentation_core_leftInverse_active {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {G : RadialModePair D →L[ℝ] RadialModePair D} {M : RadialMatchingData D}
    (hactual : ActualMatchedRepresentation D G M)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hs : Function.support ψ ⊆ radialCore D)
    (s : ℝ) (hsactive : M.frequency ≠ 2 → s = 0) :
    G (matchingTestSource D hD hB M.frequency ψ hψ s) =
      matchingTestInput D hD ψ hψ s := by
  classical
  rcases hactual with
    ⟨ha, hm, hb, hcolumn, hmargin, hscales, hDbBound, hKBound,
      hM, hsym, hdiag, hnorm, hleft, hright, hformula⟩
  have hscale : ∀ i, 0 < M.boundaryScale i := fun i => (hscales i).1
  let U := matchingTestInput D hD ψ hψ s
  let F := matchingTestSource D hD hB M.frequency ψ hψ s
  let x := matchingSmoothBoundaryValue D M ψ
  let z := matchingSmoothBoundaryFlux D M ψ
  let y : Fin 2 → ℝ := fun i => M.A i i * x i + M.B i i * z i
  let h : Fin 2 → ℝ := fun i => modePairing D (M.innerPoisson i) (M.sourceInner F)
  let o : Fin 2 → ℝ := fun i => modePairing D (M.outerPoisson i) (M.sourceOuter F)
  have hUF : ModeFullGraph D M.frequency U F := by
    apply (modeFullGraph_iff_extended M.frequency U F).mpr
    refine ⟨matchingTestPair_mem_extendedGraph hD hB M.frequency ψ hψ s, ?_⟩
    intro hj
    simp only [F, matchingTestSource, if_neg hj, hsactive hj]
  have hu : (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] ψ :=
    matchingTestInput_coe hD ψ hψ s
  have hreg : ContDiffOn ℝ 1 ψ (radialCore D) := (hψ.of_le (by simp)).contDiffOn
  have hi :
      M.innerInverse (M.sourceInner F) =
        M.sourceInner U - ∑ i, x i • M.innerPoisson i :=
    matching_innerInverse_source_eq_sub_poisson hD hB hM ha hm hb hscale hcolumn
      hUF hreg hu
  have ho :
      M.outerInverse (M.sourceOuter F) =
        M.sourceOuter U - ∑ i, y i • M.outerPoisson i := by
    have he := matching_outerInverse_source_eq_sub_poisson hD hM
      ha hm hb hscale hdiag hnorm hcolumn hUF hreg hu
    have hco (i : Fin 2) :
        M.A i i * sqrt (M.boundaryScale i) * ψ (matchingCut D M i) +
          M.B i i * matchingOuterFlux D M ψ i = y i := by
      rw [matchingOuterFlux_eq_smoothBoundaryFlux ha hb hψ]
      dsimp only [y, x, z, matchingSmoothBoundaryValue]
      ring
    simpa only [hco] using he
  have hh (i : Fin 2) : h i = radialMatrixApply M.Db x i - z i :=
    matchingInnerPoisson_testSource_pairing hD hB ha hm hb hcolumn hscale hsym hM
      i ψ hψ s
  have hoo (i : Fin 2) : o i = M.A i i * z i - M.B i i * x i :=
    matchingOuterPoisson_testSource_pairing hD hB ha hm hb hcolumn hscale hdiag hM
      i ψ hψ hc hs s
  have hmatch (i : Fin 2) :
      -M.B i i * o i + M.A i i * y i = x i ∧
        M.A i i * o i + M.B i i * y i = radialMatrixApply M.Db x i - h i := by
    have hr := (matching_boundary_rotation_iff
      (M.A i i) (M.B i i) (x i) (z i) (o i) (y i) (hnorm i)).mpr
      (And.intro (by rw [hoo i]; ring) (by rfl))
    refine ⟨hr.1, ?_⟩
    calc
      M.A i i * o i + M.B i i * y i = z i := hr.2
      _ = radialMatrixApply M.Db x i - h i := by rw [hh i]; ring
  obtain ⟨hx, hy⟩ := matching_boundary_coefficients_unique
    M.A M.B M.Db M.Kinv hdiag hnorm hleft h o x y hmatch
  have hGF : G F = M.innerInverse (M.sourceInner F) + M.outerInverse (M.sourceOuter F) +
      (∑ i, x i • M.innerPoisson i) + (∑ i, y i • M.outerPoisson i) := by
    have he := hformula F
    dsimp only at he
    change G F = M.innerInverse (M.sourceInner F) + M.outerInverse (M.sourceOuter F) +
      (∑ i, radialMatrixApply M.Kinv (fun k => o k + radialMatrixApply M.A h k) i •
        M.innerPoisson i) +
      (∑ i, (radialMatrixApply
        (fun a b => M.A a b + radialMatrixProduct M.B M.Db a b)
          (radialMatrixApply M.Kinv (fun k => o k + radialMatrixApply M.A h k)) i -
          radialMatrixApply M.B h i) • M.outerPoisson i) at he
    rw [← hx] at he
    have hyi (i : Fin 2) :
        radialMatrixApply (fun a b => M.A a b + radialMatrixProduct M.B M.Db a b) x i -
          radialMatrixApply M.B h i = y i := congrFun hy.symm i
    simpa only [hyi] using he
  change G F = U
  calc
    G F = M.innerInverse (M.sourceInner F) + M.outerInverse (M.sourceOuter F) +
        (∑ i, x i • M.innerPoisson i) + (∑ i, y i • M.outerPoisson i) := hGF
    _ = M.sourceInner U + M.sourceOuter U := by
      rw [hi, ho]
      abel
    _ = U := matching_sources_add hM U

/-- The matching formula left-inverts every concrete smooth test pair,
with the identity extension on the inactive scalar. -/
theorem actualMatchedRepresentation_core_leftInverse {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {G : RadialModePair D →L[ℝ] RadialModePair D} {M : RadialMatchingData D}
    (hactual : ActualMatchedRepresentation D G M)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hs : Function.support ψ ⊆ radialCore D) (s : ℝ) :
    matchingExtendedOperator M.frequency G
      (matchingTestSource D hD hB M.frequency ψ hψ s) =
        matchingTestInput D hD ψ hψ s := by
  by_cases hj : M.frequency = 2
  · rw [matchingExtendedOperator_apply, if_pos hj, Prod.mk_zero_zero, add_zero]
    exact actualMatchedRepresentation_core_leftInverse_active hD hB hactual
      ψ hψ hc hs s (fun h => (h hj).elim)
  · have hM : MatchingLocalRealizations D M := hactual.2.2.2.2.2.2.2.2.1
    have hbase := actualMatchedRepresentation_core_leftInverse_active hD hB hactual
      ψ hψ hc hs 0 (fun _ => rfl)
    have hpure : G (0, s) = 0 := by
      rw [hactual.formula]
      exact matchingFormulaValue_pure_scalar hM hj rfl
    have hsource :
        matchingTestSource D hD hB M.frequency ψ hψ s =
          matchingTestSource D hD hB M.frequency ψ hψ 0 + (0, s) := by
      apply Prod.ext <;>
        simp [matchingTestSource, hj, Prod.fst_add, Prod.snd_add]
    calc
      matchingExtendedOperator M.frequency G
          (matchingTestSource D hD hB M.frequency ψ hψ s) =
          G (matchingTestSource D hD hB M.frequency ψ hψ s) + (0, s) := by
        rw [matchingExtendedOperator_apply]
        simp only [hj, if_neg, ite_false, matchingTestSource]
      _ = G (matchingTestSource D hD hB M.frequency ψ hψ 0) + (0, s) := by
        rw [hsource, map_add, hpure, add_zero]
      _ = matchingTestInput D hD ψ hψ 0 + (0, s) := by rw [hbase]
      _ = matchingTestInput D hD ψ hψ s := by
        apply Prod.ext <;> simp [matchingTestInput, Prod.fst_add, Prod.snd_add]

end ContinuousFlexibility.Radial
