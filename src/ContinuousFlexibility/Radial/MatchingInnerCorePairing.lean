import ContinuousFlexibility.Radial.ModeCoreGraph
import ContinuousFlexibility.Radial.ModeRegionalPairing
import ContinuousFlexibility.Radial.ModeWeakGreen
import ContinuousFlexibility.Radial.MatchingSourcePairing

/-!
# Inner Poisson reciprocity for the actual smooth source

The prescribed inner Poisson columns convert a smooth source into the
difference between its Dirichlet-to-Neumann value and its actual
conormal flux. The proof uses the finite weak Green identity on the
regular inner interval and the frozen representative, row and trace
clauses of the local realizations.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace
open ContinuousFlexibility.Statements

def matchingSmoothBoundaryValue (D : ReferenceData) (M : RadialMatchingData D)
    (ψ : ℝ → ℝ) (i : Fin 2) : ℝ :=
  sqrt (M.boundaryScale i) * ψ (matchingCut D M i)

def matchingSmoothBoundaryFlux (D : ReferenceData) (M : RadialMatchingData D)
    (ψ : ℝ → ℝ) (i : Fin 2) : ℝ :=
  bufferSign i * D.w (matchingCut D M i) * deriv ψ (matchingCut D M i) /
    sqrt (M.boundaryScale i)

/-- Finite Green boundary data in the exact normalization of the frozen
matching matrices. -/
theorem matchingInner_smooth_green_boundary {D : ReferenceData}
    {M : RadialMatchingData D} (hlh : M.innerLeft < M.innerRight)
    (hscale : ∀ k, 0 < M.boundaryScale k)
    (hsym : ∀ k n, M.Db k n = M.Db n k)
    (i : Fin 2) {p ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hp : ∀ k, p (matchingCut D M k) =
      (if i = k then 1 else 0) / sqrt (M.boundaryScale k))
    (hflux : ∀ k, M.Db k i = matchingInnerFlux D M p k) :
    -((p M.innerRight *
          (D.w M.innerRight * derivWithin ψ (Icc M.innerLeft M.innerRight) M.innerRight) -
        ψ M.innerRight *
          (D.w M.innerRight * derivWithin p (Icc M.innerLeft M.innerRight) M.innerRight)) -
      (p M.innerLeft *
          (D.w M.innerLeft * derivWithin ψ (Icc M.innerLeft M.innerRight) M.innerLeft) -
        ψ M.innerLeft *
          (D.w M.innerLeft * derivWithin p (Icc M.innerLeft M.innerRight) M.innerLeft))) =
      radialMatrixApply M.Db (matchingSmoothBoundaryValue D M ψ) i -
        matchingSmoothBoundaryFlux D M ψ i := by
  have hdL : derivWithin ψ (Icc M.innerLeft M.innerRight) M.innerLeft =
      deriv ψ M.innerLeft :=
    (hψ.differentiable (by simp) M.innerLeft).derivWithin
      (uniqueDiffOn_Icc hlh _ ⟨le_rfl, hlh.le⟩)
  have hdR : derivWithin ψ (Icc M.innerLeft M.innerRight) M.innerRight =
      deriv ψ M.innerRight :=
    (hψ.differentiable (by simp) M.innerRight).derivWithin
      (uniqueDiffOn_Icc hlh _ ⟨hlh.le, le_rfl⟩)
  have hpL : p M.innerLeft = (if i = 0 then 1 else 0) / sqrt (M.boundaryScale 0) := by
    simpa only [matchingCut, if_pos rfl] using hp 0
  have hpR : p M.innerRight = (if i = 1 then 1 else 0) / sqrt (M.boundaryScale 1) := by
    simpa [matchingCut] using hp 1
  have hn0 : sqrt (M.boundaryScale 0) ≠ 0 := (sqrt_pos.mpr (hscale 0)).ne'
  have hn1 : sqrt (M.boundaryScale 1) ≠ 0 := (sqrt_pos.mpr (hscale 1)).ne'
  rw [hdL, hdR, hpL, hpR]
  simp only [radialMatrixApply, Fin.sum_univ_two]
  rw [hsym i 0, hsym i 1, hflux 0, hflux 1]
  fin_cases i <;>
    simp [matchingSmoothBoundaryValue, matchingSmoothBoundaryFlux,
      matchingInnerFlux, matchingCut, bufferSign] <;>
    field_simp [hn0, hn1] <;> ring

theorem matchingInnerPoisson_testSource_pairing {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {M : RadialMatchingData D}
    (ha : D.a < M.innerLeft) (hlh : M.innerLeft < M.innerRight)
    (hb : M.innerRight < D.b)
    (hcolumn : Function.support (referenceColumn D) ⊆ Ioo M.innerLeft M.innerRight)
    (hscale : ∀ k, 0 < M.boundaryScale k)
    (hsym : ∀ k n, M.Db k n = M.Db n k)
    (hM : MatchingLocalRealizations D M)
    (i : Fin 2) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (s : ℝ) :
    modePairing D (M.innerPoisson i)
      (M.sourceInner (matchingTestSource D hD hB M.frequency ψ hψ s)) =
      radialMatrixApply M.Db (matchingSmoothBoundaryValue D M ψ) i -
        matchingSmoothBoundaryFlux D M ψ i := by
  rcases hM.2.2.2.2.2 i with
    ⟨hrep, hrepO, hzero, hzeroO, hp, hpO, hsO, hEq, hEqO, hrow, htrace⟩
  have hsub : Icc M.innerLeft M.innerRight ⊆ radialCore D := by
    intro r hr
    exact ⟨lt_of_lt_of_le ha hr.1, lt_of_le_of_lt hr.2 hb⟩
  have hsub' : Icc M.innerLeft M.innerRight ⊆ Icc D.a D.b :=
    hsub.trans Ioo_subset_Icc_self
  have hfix := matching_sourceInner_innerPoisson hD hM i
  have hJ :
      ⟪(M.innerPoisson i).1, matchingJacobiVector D hD M.frequency ψ hψ⟫_ℝ =
        ∫ r in M.innerLeft..M.innerRight,
          M.innerFunction i r * radialJacobi ((M.frequency : ℝ) ^ 2) D.w ψ r :=
    (matchingJacobi_integral_eq_inner hD (M.innerPoisson i).1 hψ M.frequency).symm.trans
      (matchingInner_integral_eq_of_fixed hD hM hlh.le hsub
        (M.innerPoisson i) hfix hrep
        (radialJacobi ((M.frequency : ℝ) ^ 2) D.w ψ))
  have hC :
      (∫ r in D.a..D.b, referenceColumn D r * ψ r) =
        ∫ r in M.innerLeft..M.innerRight, referenceColumn D r * ψ r := by
    apply matchingInterval_eq_subinterval (Ioo_subset_Icc_self.trans hsub)
    intro r hr
    exact hcolumn ((mul_ne_zero_iff.mp hr).1)
  have hrowrep :
      ⟪(M.innerPoisson i).1, matchingBorderVector D hD hB⟫_ℝ =
        ∫ r in D.a..D.b, referenceColumn D r * M.innerFunction i r := by
    rw [← matchingColumn_integral_eq_inner hD hB]
    apply matchingInterval_congr_ae hD
    filter_upwards [hrep] with r hr
    rw [hr]
  have hpair :
      modePairing D (M.innerPoisson i)
        (M.sourceInner (matchingTestSource D hD hB M.frequency ψ hψ s)) =
      -(∫ r in M.innerLeft..M.innerRight,
          M.innerFunction i r * radialJacobi ((M.frequency : ℝ) ^ 2) D.w ψ r) +
        (M.innerPoisson i).2 *
          (∫ r in M.innerLeft..M.innerRight, referenceColumn D r * ψ r) := by
    rw [matchingSourceInner_pairing_of_fixed D M hM _ _ hfix,
      matchingTestSource_pairing, hJ, hC]
    by_cases hj : M.frequency = 2
    · have hr : ⟪(M.innerPoisson i).1, matchingBorderVector D hD hB⟫_ℝ = 0 := by
        rw [hrowrep]
        simpa only [hj, if_pos] using hrow
      simp only [hj, if_pos, hr, mul_zero, add_zero]
    · have hs : (M.innerPoisson i).2 = 0 := by simpa only [hj, if_neg] using hrow
      simp only [hj, if_neg, hs, zero_mul, add_zero]
  have hp₁ : ContDiffOn ℝ 1 (M.innerFunction i) (Icc M.innerLeft M.innerRight) :=
    hp.of_le (by norm_num)
  have hψ₂ : ContDiffOn ℝ 2 ψ (Icc M.innerLeft M.innerRight) :=
    (hψ.of_le (by simp)).contDiffOn
  have hgreen := modeLocalEquation_green_on_compact hD hB hEq hrep hlh hsub
    (fun _ h => h) hp₁ hψ₂
  have hiL : IntervalIntegrable
      (fun r => M.innerFunction i r * radialJacobi ((M.frequency : ℝ) ^ 2) D.w ψ r)
      volume M.innerLeft M.innerRight :=
    (hp.continuousOn.mul
      ((matchingJacobi_continuousOn hD hψ M.frequency).mono hsub')).intervalIntegrable_of_Icc
        hlh.le
  have hiC : IntervalIntegrable (fun r => referenceColumn D r * ψ r)
      volume M.innerLeft M.innerRight :=
    (((matchingColumn_continuousOn hD hB).mono hsub').mul
      hψ.continuous.continuousOn).intervalIntegrable_of_Icc hlh.le
  have hzeroInt :
      (∫ r in M.innerLeft..M.innerRight,
        M.innerFunction i r * radialJacobi ((M.frequency : ℝ) ^ 2) D.w ψ r -
          ((M.innerPoisson i).2 * referenceColumn D r -
            matchingDensity D r * (0 : RadialModePair D).1 r) * ψ r) =
      ∫ r in M.innerLeft..M.innerRight,
        M.innerFunction i r * radialJacobi ((M.frequency : ℝ) ^ 2) D.w ψ r -
          (M.innerPoisson i).2 * (referenceColumn D r * ψ r) := by
    apply matchingSubinterval_congr_ae hD hlh.le hsub
    filter_upwards [(Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D) :
      ⇑(0 : RadialModeL2 D) =ᵐ[radialHilbertMeasure D] 0)] with r hr
    simp only [Prod.fst_zero, hr, Pi.zero_apply, mul_zero, sub_zero]
    ring
  rw [hzeroInt, intervalIntegral.integral_sub hiL (hiC.const_mul (M.innerPoisson i).2),
    intervalIntegral.integral_const_mul] at hgreen
  rw [hpair]
  calc
    _ = -((M.innerFunction i M.innerRight *
          (D.w M.innerRight * derivWithin ψ (Icc M.innerLeft M.innerRight) M.innerRight) -
        ψ M.innerRight *
          (D.w M.innerRight * derivWithin (M.innerFunction i)
            (Icc M.innerLeft M.innerRight) M.innerRight)) -
      (M.innerFunction i M.innerLeft *
          (D.w M.innerLeft * derivWithin ψ (Icc M.innerLeft M.innerRight) M.innerLeft) -
        ψ M.innerLeft *
          (D.w M.innerLeft * derivWithin (M.innerFunction i)
            (Icc M.innerLeft M.innerRight) M.innerLeft))) := by
      linarith only [hgreen]
    _ = _ := matchingInner_smooth_green_boundary hlh hscale hsym i hψ
      (fun k => (htrace k).1) (fun k => (htrace k).2.1)

end ContinuousFlexibility.Radial
