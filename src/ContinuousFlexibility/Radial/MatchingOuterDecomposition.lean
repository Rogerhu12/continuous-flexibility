module

public import ContinuousFlexibility.Radial.MatchingInnerDecomposition
public import ContinuousFlexibility.Radial.MatchingTraceCalculus
public import Mathlib.Tactic.Ring

/-!
# Outer inverse decomposition by the Poisson columns

The normalized Robin datum of a local solution is removed by the
supplied outer Poisson columns. The remainder belongs to the exact
frozen separated graph, so local uniqueness identifies it with the
outer inverse. No adjointness of the local inverse is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem matching_outerInverse_eq_sub_poisson {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (hM : MatchingLocalRealizations D M)
    (ha : D.a < M.innerLeft) (hm : M.innerLeft < M.innerRight)
    (hb : M.innerRight < D.b) (hscale : ∀ i, 0 < M.boundaryScale i)
    (hdiag : ∀ i j, i ≠ j → M.A i j = 0 ∧ M.B i j = 0)
    (hnorm : ∀ i, M.A i i ^ 2 + M.B i i ^ 2 = 1)
    {U F : RadialModePair D} {u : ℝ → ℝ}
    (hEq : ModeLocalEquation D M.frequency (matchingOuterRegion D M) U F)
    (hscalar : U.2 = 0)
    (hu : (U.1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (matchingOuterRegion D M)] u)
    (hz : (U.1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (Ioo M.innerLeft M.innerRight)] fun _ => 0)
    (hreg : ContDiffOn ℝ 1 u (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b)) :
    M.outerInverse F = U - ∑ i,
      (M.A i i * Real.sqrt (M.boundaryScale i) * u (matchingCut D M i) +
        M.B i i * matchingOuterFlux D M u i) • M.outerPoisson i := by
  classical
  let y : Fin 2 → ℝ := fun i =>
    M.A i i * Real.sqrt (M.boundaryScale i) * u (matchingCut D M i) +
      M.B i i * matchingOuterFlux D M u i
  let P : RadialModePair D := ∑ i, y i • M.outerPoisson i
  let p : ℝ → ℝ := fun r => ∑ i, y i * M.outerFunction i r
  have hdata := hM.2.2.2.2.2
  have hPa : (P.1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (matchingOuterRegion D M)] p :=
    matching_pair_sum_ae_restrict M.outerPoisson M.outerFunction y
      (fun i => (hdata i).2.1.restrict)
  have hPzero : (P.1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
      (Ioo M.innerLeft M.innerRight)] fun _ => 0 := by
    simpa only [mul_zero, Finset.sum_const_zero] using
      (matching_pair_sum_ae_restrict M.outerPoisson (fun _ _ => 0) y
        (fun i => (hdata i).2.2.2.1))
  have hpreg : ∀ i, ContDiffOn ℝ 1 (M.outerFunction i)
      (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b) :=
    fun i => (hdata i).2.2.2.2.2.1.of_le (by norm_num)
  have hps : ContDiffOn ℝ 1 p (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b) := by
    apply ContDiffOn.sum
    intro i hi
    exact contDiffOn_const.mul (hpreg i)
  have hpvalue : ∀ k,
      Real.sqrt (M.boundaryScale k) * p (matchingCut D M k) = M.A k k * y k := by
    intro k
    have hsqrt : Real.sqrt (M.boundaryScale k) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (hscale k))
    have hvalue : p (matchingCut D M k) =
        y k * (M.A k k / Real.sqrt (M.boundaryScale k)) := by
      calc
        p (matchingCut D M k) =
            ∑ i, y i * (M.A k i / Real.sqrt (M.boundaryScale k)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [((hdata i).2.2.2.2.2.2.2.2.2.2 k).2.2.1]
        _ = y k * (M.A k k / Real.sqrt (M.boundaryScale k)) := by
          apply Finset.sum_eq_single k
          · intro i hi hik
            simp only [(hdiag k i hik.symm).1, zero_div, mul_zero]
          · intro hk
            exact (hk (Finset.mem_univ k)).elim
    rw [hvalue]
    field_simp [hsqrt] <;> ring
  have hpflux : ∀ k, matchingOuterFlux D M p k = M.B k k * y k := by
    intro k
    change matchingOuterFlux D M (fun r => ∑ i, y i * M.outerFunction i r) k = _
    rw [matchingOuterFlux_fun_sum ha hm hb y M.outerFunction hpreg k]
    calc
      (∑ i, y i * matchingOuterFlux D M (M.outerFunction i) k) =
          ∑ i, y i * M.B k i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [((hdata i).2.2.2.2.2.2.2.2.2.2 k).2.2.2]
      _ = y k * M.B k k := by
        apply Finset.sum_eq_single k
        · intro i hi hik
          simp only [(hdiag k i hik.symm).2, mul_zero]
        · intro hk
          exact (hk (Finset.mem_univ k)).elim
      _ = M.B k k * y k := mul_comm _ _
  have hPeq : ModeLocalEquation D M.frequency (matchingOuterRegion D M) P 0 := by
    have he := modeLocalEquation_finset_sum hD Finset.univ
      (fun i => y i • M.outerPoisson i) (fun i => y i • (0 : RadialModePair D))
      (fun i _ => modeLocalEquation_smul hD (hdata i).2.2.2.2.2.2.2.2.1 (y i))
    simpa only [P, smul_zero, Finset.sum_const_zero] using he
  have hPscalar : P.2 = 0 := by
    dsimp only [P]
    simp only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro i hi
    rw [(hdata i).2.2.2.2.2.2.1, mul_zero]
  have hReq : ModeLocalEquation D M.frequency (matchingOuterRegion D M) (U - P) F := by
    simpa only [sub_zero] using modeLocalEquation_sub hD hEq hPeq
  have hRscalar : (U - P).2 = 0 := by
    simp only [Prod.snd_sub, hscalar, hPscalar, sub_zero]
  have hRa := matching_pair_sub_ae_restrict hu hPa
  have hRzero : (((U - P).1 : RadialModeL2 D) : ℝ → ℝ) =ᵐ[
      (radialHilbertMeasure D).restrict (Ioo M.innerLeft M.innerRight)] fun _ => 0 := by
    simpa only [sub_self] using matching_pair_sub_ae_restrict hz hPzero
  have hboundary : ∀ i,
      M.A i i * Real.sqrt (M.boundaryScale i) *
        (u (matchingCut D M i) - p (matchingCut D M i)) +
      M.B i i * matchingOuterFlux D M (fun r => u r - p r) i = 0 := by
    intro i
    rw [matchingOuterFlux_sub ha hm hb hreg hps i, hpflux i]
    calc
      M.A i i * Real.sqrt (M.boundaryScale i) *
          (u (matchingCut D M i) - p (matchingCut D M i)) +
          M.B i i * (matchingOuterFlux D M u i - M.B i i * y i) =
        y i - (M.A i i * (Real.sqrt (M.boundaryScale i) * p (matchingCut D M i)) +
          M.B i i ^ 2 * y i) := by dsimp only [y]; ring
      _ = (1 - (M.A i i ^ 2 + M.B i i ^ 2)) * y i := by rw [hpvalue i]; ring
      _ = 0 := by rw [hnorm i]; ring
  have hgraph := matching_outerGraph_of_representative hD ha hb hReq hRscalar hRa hRzero
    (hreg.sub hps) hboundary
  exact hM.2.2.1 (U - P) F hgraph

/-- The outer decomposition for a full modal graph and its global
representative. -/
theorem matching_outerInverse_source_eq_sub_poisson {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (hM : MatchingLocalRealizations D M)
    (ha : D.a < M.innerLeft) (hm : M.innerLeft < M.innerRight)
    (hb : M.innerRight < D.b) (hscale : ∀ i, 0 < M.boundaryScale i)
    (hdiag : ∀ i j, i ≠ j → M.A i j = 0 ∧ M.B i j = 0)
    (hnorm : ∀ i, M.A i i ^ 2 + M.B i i ^ 2 = 1)
    (hcolumn : Function.support (referenceColumn D) ⊆ Ioo M.innerLeft M.innerRight)
    {U F : RadialModePair D} {u : ℝ → ℝ}
    (hU : ModeFullGraph D M.frequency U F)
    (hreg : ContDiffOn ℝ 1 u (radialCore D))
    (hu : (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u) :
    M.outerInverse (M.sourceOuter F) = M.sourceOuter U - ∑ i,
      (M.A i i * Real.sqrt (M.boundaryScale i) * u (matchingCut D M i) +
        M.B i i * matchingOuterFlux D M u i) • M.outerPoisson i := by
  have hEq := (matching_modeLocalEquation_outerSource_iff hD hM).mpr
    (matching_modeLocalEquation_sourceOuter hD hM ha hm hb hcolumn hU.1)
  have hreps := matching_sourceOuter_representative hM hu
  apply matching_outerInverse_eq_sub_poisson hD hM ha hm hb hscale hdiag hnorm
    hEq (hM.2.2.2.1 U).2.1 hreps.1 hreps.2
  apply hreg.mono
  intro r hr
  rcases hr with hL | hR
  · exact ⟨hL.1, lt_of_le_of_lt hL.2 (lt_trans hm hb)⟩
  · exact ⟨lt_of_lt_of_le (lt_trans ha hm) hR.1, hR.2⟩

end ContinuousFlexibility.Radial
