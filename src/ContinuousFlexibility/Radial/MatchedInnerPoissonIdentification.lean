module

public import ContinuousFlexibility.Radial.MatchingInnerDecomposition
public import ContinuousFlexibility.Radial.TerminalPoissonCorrection
public import ContinuousFlexibility.Radial.MatchedPhysicalPartition

/-!
# Identification and interior return of the actual inner Poisson columns

A normalized homogeneous candidate equals the Poisson column stored in
the frozen matching data by Dirichlet uniqueness. In particular, the
actual cutoff lift minus its actual Dirichlet correction is that same
column. Away from the lift support, only the small source correction
remains. No weighted inverse estimate is part of the candidate data.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem matchedInnerPoisson_eq_of_candidate {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {M : RadialMatchingData D} (hM : MatchingLocalRealizations D M)
    (hm : M.innerLeft < M.innerRight) (hscale : ∀ k, 0 < M.boundaryScale k)
    (i : Fin 2) {P : RadialModePair D} {p : ℝ → ℝ}
    (hEq : ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) P 0)
    (hp : (P.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] p)
    (hreg : ContDiffOn ℝ 1 p (Icc M.innerLeft M.innerRight))
    (hout : ∀ r ∈ matchingOuterRegion D M, p r = 0)
    (hrow : if M.frequency = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * p r) = 0 else P.2 = 0)
    (htrace : ∀ k, p (matchingCut D M k) =
      (if i = k then 1 else 0) / Real.sqrt (M.boundaryScale k)) :
    M.innerPoisson i = P := by
  classical
  have hz : (P.1 : ℝ → ℝ) =ᵐ[
      (radialHilbertMeasure D).restrict (matchingOuterRegion D M)] fun _ => 0 := by
    filter_upwards [hp.restrict, ae_restrict_mem
      (show MeasurableSet (matchingOuterRegion D M) from measurableSet_Ioo.union measurableSet_Ioo)]
      with r hr hmem
    rw [hr, hout r hmem]
  have hrow' : if M.frequency = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * P.1 r) = (0 : RadialModePair D).2
      else P.2 = 0 ∧ (0 : RadialModePair D).2 = 0 := by
    by_cases hj : M.frequency = 2
    · simp only [if_pos hj, Prod.snd_zero]
      rw [matchingInterval_congr_ae hD
        (hp.mono (fun r hr => congrArg (fun z => referenceColumn D r * z) hr))]
      simpa only [if_pos hj] using hrow
    · simp only [if_neg hj, Prod.snd_zero]
      exact ⟨by simpa only [if_neg hj] using hrow, True.intro⟩
  have hcoef (k : Fin 2) :
      Real.sqrt (M.boundaryScale k) * p (matchingCut D M k) =
        if i = k then 1 else 0 := by
    rw [htrace k, div_eq_mul_inv]
    by_cases hik : i = k
    · simp only [if_pos hik, one_mul,
        mul_inv_cancel₀ (Real.sqrt_pos.mpr (hscale k)).ne']
    · simp only [if_neg hik, zero_mul, mul_zero]
  have hsum :
      (∑ k, (Real.sqrt (M.boundaryScale k) * p (matchingCut D M k)) • M.innerPoisson k) =
        M.innerPoisson i := by
    rw [Finset.sum_eq_single i]
    · rw [hcoef]
      simp only [ite_true, one_smul]
    · intro k _ hki
      rw [hcoef, if_neg hki.symm, zero_smul]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have he := matching_innerInverse_eq_sub_poisson hD hB hM hm hscale
    hEq hrow' hp.restrict hz hreg
  rw [map_zero, hsum] at he
  exact (sub_eq_zero.mp he.symm).symm

/-- Actual lift and source data, stated before any quantitative bound.
The graph field is precisely the Dirichlet equation already supplied
by the constructed finite inner inverse. -/
structure MatchedInnerPoissonLift (D : ReferenceData) (M : RadialMatchingData D)
    (H : RadialModePair D →L[ℝ] RadialModePair D) (i : Fin 2) where
  lift : RadialModePair D
  source : RadialModePair D
  representative : ℝ → ℝ
  equation : ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) lift source
  dirichlet : ModeInnerDirichletGraph D M (H source) source
  represents : (lift.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] representative
  regular : ContDiffOn ℝ 1 representative (Icc M.innerLeft M.innerRight)
  outside : ∀ r ∈ matchingOuterRegion D M, representative r = 0
  source_scalar : source.2 = 0
  row : if M.frequency = 2 then
    (∫ r in D.a..D.b, referenceColumn D r * representative r) = 0 else lift.2 = 0
  trace : ∀ k, representative (matchingCut D M k) =
    (if i = k then 1 else 0) / Real.sqrt (M.boundaryScale k)

namespace MatchedInnerPoissonLift

variable {D : ReferenceData} {M : RadialMatchingData D}
  {H : RadialModePair D →L[ℝ] RadialModePair D} {i : Fin 2}
  (L : MatchedInnerPoissonLift D M H i)

theorem eq_innerPoisson
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (hM : MatchingLocalRealizations D M) (hm : M.innerLeft < M.innerRight)
    (hscale : ∀ k, 0 < M.boundaryScale k) :
    M.innerPoisson i = L.lift - H L.source := by
  obtain ⟨p, hp, hreg, hout, htrace, hEq, hrow⟩ :=
    terminalInnerPoisson_correction hD hB M H L.lift L.source L.representative
      L.equation L.dirichlet L.represents L.regular L.outside L.source_scalar L.row
  apply matchedInnerPoisson_eq_of_candidate hD hB hM hm hscale i hEq hp hreg hout hrow
  intro k
  rw [htrace k]
  exact L.trace k

theorem projected_bound
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (hM : MatchingLocalRealizations D M) (hm : M.innerLeft < M.innerRight)
    (hscale : ∀ k, 0 < M.boundaryScale k)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : RadialModePair D →L[ℝ] E) :
    ‖Q (M.innerPoisson i)‖ ≤ ‖Q L.lift‖ + ‖Q ∘L H‖ * ‖L.source‖ := by
  rw [L.eq_innerPoisson hD hB hM hm hscale, map_sub]
  exact (norm_sub_le _ _).trans
    (add_le_add le_rfl ((Q ∘L H).le_opNorm L.source))

theorem return_bound
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (hM : MatchingLocalRealizations D M) (hm : M.innerLeft < M.innerRight)
    (hscale : ∀ k, 0 < M.boundaryScale k)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : RadialModePair D →L[ℝ] E) (hQ : Q L.lift = 0) :
    ‖Q (M.innerPoisson i)‖ ≤ ‖Q ∘L H‖ * ‖L.source‖ := by
  have hh := L.projected_bound hD hB hM hm hscale Q
  simpa only [hQ, norm_zero, zero_add] using hh

/-- The cutoff support proves vanishing of the actual mode cell map;
no separate projection identity is assumed. -/
theorem modeCell_lift_zero (hP : RadialPartition D) (k : ℕ)
    (hcut : ∀ r, D.localizer k r ≠ 0 → L.representative r = 0) :
    matchedModeCell D hP k L.lift = 0 := by
  rw [matchedModeCell_apply]
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [matchedModeCellL2_ae D hP k L.lift.1,
      L.represents, (Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D))] with r hcell hrep hz
    change matchedModeCellL2 D hP k L.lift.1 r = (0 : RadialModeL2 D) r
    rw [hcell, hrep, hz]
    change D.localizer k r * L.representative r = 0
    by_cases hr : D.localizer k r = 0
    · rw [hr, zero_mul]
    · rw [hcut r hr, mul_zero]
  · rfl

theorem physicalCell_lift_zero
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D) (k : ℕ)
    (hcut : ∀ r, D.localizer k r ≠ 0 → L.representative r = 0) :
    matchedPhysicalOutputCell D hD hP k L.lift = 0 := by
  rw [matchedPhysicalOutputCell, ContinuousLinearMap.comp_apply,
    L.modeCell_lift_zero hP k hcut, map_zero]

/-- Actual physical cell return, with its local density conversion
already included in the continuous output map. -/
theorem physicalCell_return
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D) (hP : RadialPartition D)
    (hM : MatchingLocalRealizations D M) (hm : M.innerLeft < M.innerRight)
    (hscale : ∀ k, 0 < M.boundaryScale k) (k : ℕ)
    (hcut : ∀ r, D.localizer k r ≠ 0 → L.representative r = 0) :
    ‖matchedPhysicalOutputCell D hD hP k (M.innerPoisson i)‖ ≤
      ‖matchedPhysicalOutputCell D hD hP k ∘L H‖ * ‖L.source‖ :=
  L.return_bound hD hB hM hm hscale (matchedPhysicalOutputCell D hD hP k)
    (L.physicalCell_lift_zero hD hP k hcut)

theorem physicalCell_return_exp
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D) (hP : RadialPartition D)
    (hM : MatchingLocalRealizations D M) (hm : M.innerLeft < M.innerRight)
    (hscale : ∀ k, 0 < M.boundaryScale k) (k : ℕ)
    (hcut : ∀ r, D.localizer k r ≠ 0 → L.representative r = 0)
    {A C σ : ℝ} (hC : 0 ≤ C)
    (hH : ‖matchedPhysicalOutputCell D hD hP k ∘L H‖ ≤ C)
    (hsource : ‖L.source‖ ≤ A * Real.exp (-σ)) :
    ‖matchedPhysicalOutputCell D hD hP k (M.innerPoisson i)‖ ≤
      C * A * Real.exp (-σ) := by
  calc
    _ ≤ ‖matchedPhysicalOutputCell D hD hP k ∘L H‖ * ‖L.source‖ :=
      L.physicalCell_return hD hB hP hM hm hscale k hcut
    _ ≤ C * ‖L.source‖ := mul_le_mul_of_nonneg_right hH (norm_nonneg _)
    _ ≤ C * (A * Real.exp (-σ)) := mul_le_mul_of_nonneg_left hsource hC
    _ = _ := by ring

end MatchedInnerPoissonLift

end ContinuousFlexibility.Radial
