import ContinuousFlexibility.Radial.TerminalRegionalData
import ContinuousFlexibility.Radial.MatchedInnerExternalDecomposition
import ContinuousFlexibility.Radial.MatchedModeWeightedCells

/-!
# The original terminal cutoff columns in the matching data

The lift, source and zero extension are exactly those used by
TerminalRegionalData. The frozen uniqueness identifies their actual
Dirichlet correction with M.innerPoisson, for both endpoints at once.
The source estimate below uses its proved support and measured norm.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff

/-- The actual full matching column is the original terminal leading
field minus the original inner inverse of its actual cutoff source. -/
theorem terminalRegional_innerPoisson_eq {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (R : TerminalRegionalData D)
    (hM : MatchingLocalRealizations D R.matching) (i : Fin 2) :
    R.matching.innerPoisson i =
      terminalCapInnerLift hD R.matching.innerLeft R.matching.innerRight
        (R.matching.boundaryScale i) (R.cutoff_smooth i) (R.standIn_smooth i) -
      R.matching.innerInverse
        (terminalCapInnerSource R.matching.innerLeft R.matching.innerRight
          (R.matching.boundaryScale i) (R.cutoff i) (R.standIn i) (R.source_memLp i)) := by
  let M := R.matching
  have hsub : Icc M.innerLeft M.innerRight ⊆ radialCore D := by
    intro r hr
    exact ⟨R.cut_order.1.trans_le hr.1, hr.2.trans_lt R.cut_order.2.2⟩
  obtain ⟨L, F, ell, hL, hF, _hell, heq, hrep, hreg, hout, hLs, hFs,
      hfix, horth, htrace, _hflux, _hpair, _hbound⟩ :=
    terminalActualCutoff_columns_exists hD M R.cut_order.2.1 hsub
      R.cutoff R.standIn R.cutoff_smooth R.standIn_smooth
      R.standIn_equation R.source_memLp R.cutoff_derivative_inside
      R.cutoff_disjoint R.cutoff_column_disjoint R.cutoff_boundary
      R.standIn_boundary R.boundary_scale R.frequency_pos
      (fun k => (R.sourceCost * sqrt (M.D0 k)) * exp (-R.attenuation k))
      R.source_bound
  have hLp : (((L i).1, 0) : RadialModePair D) = L i := Prod.ext rfl (hLs i).symm
  have hFp : (((F i).1, 0) : RadialModePair D) = F i := Prod.ext rfl (hFs i).symm
  have hproject : M.sourceInner (F i) = F i :=
    (R.inner_source (F i)).trans (hfix i)
  have hrow : (∫ r in D.a..D.b, referenceColumn D r * (L i).1 r) = 0 := by
    calc
      _ = ∫ r in D.a..D.b, referenceColumn D r * ell i r :=
        matchingInterval_congr_ae hD
          ((hrep i).mono fun r hr => congrArg (fun z => referenceColumn D r * z) hr)
      _ = ∫ _r in D.a..D.b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro r _
        by_cases hr : r ∈ Icc M.innerLeft M.innerRight
        · exact horth i r hr
        · have hz : referenceColumn D r = 0 := by
            by_contra hn
            exact hr (Ioo_subset_Icc_self (R.column_inside hn))
          rw [hz, zero_mul]
      _ = 0 := intervalIntegral.integral_zero
  have hi : ((L i).1 : ℝ → ℝ) =ᵐ[
      (radialHilbertMeasure D).restrict (Ioo M.innerLeft M.innerRight)] ell i :=
    ae_restrict_of_ae (hrep i)
  have ho : ((L i).1 : ℝ → ℝ) =ᵐ[
      (radialHilbertMeasure D).restrict (matchingOuterRegion D M)] fun _ => 0 := by
    filter_upwards [ae_restrict_of_ae (hrep i),
      ae_restrict_mem (measurableSet_Ioo.union measurableSet_Ioo)] with r hr hro
    exact hr.trans (hout i r hro)
  have heq' : ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight)
      ((L i).1, 0) ((F i).1, 0) := by
    rw [hLp, hFp]
    exact heq i
  have hdec := matchedInnerPoisson_eq_leading_sub_inverse hD hB hM R.cut_order.2.1
    (fun k => (R.diagonal k).1) i (L i).1 (F i).1 (ell i)
      heq' hrow hi ho (hreg i) (htrace i)
  rw [hLp, hFp, hproject, hL i, hF i] at hdec
  exact hdec

/-- A true field multiplier only pays its bound on the actual support
of a vector whose scalar coordinate is zero. -/
theorem matchedMode_weighted_zeroScalar_support_bound {D : ReferenceData}
    (E : RadialModeL2 D ≃L[ℝ] RadialModeL2 D) (w : ℝ → ℝ)
    (hE : ∀ u, E u =ᵐ[radialHilbertMeasure D] fun r => w r * u r)
    (F : RadialModePair D) (hFs : F.2 = 0) (s : Set ℝ)
    (hf : ∀ᵐ r ∂radialHilbertMeasure D, r ∉ s → F.1 r = 0)
    {A : ℝ} (hA : 0 ≤ A) (hlocal : ∀ r ∈ s, |w r| ≤ A) :
    ‖(E.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)) F‖ ≤ A * ‖F‖ := by
  rw [ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.refl_apply,
    hFs, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
  have hn : ‖E F.1‖ ≤ A * ‖F.1‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hE F.1, hf] with r he hz
    rw [he, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    by_cases hr : r ∈ s
    · exact mul_le_mul_of_nonneg_right (hlocal r hr) (abs_nonneg _)
    · rw [hz hr, abs_zero, mul_zero, mul_zero]
  exact hn.trans
    (mul_le_mul_of_nonneg_left (norm_fst_le F) hA)

/-- The original terminal source, with its original attenuation, after
an actual weight. No weighted source norm is assumed. -/
theorem terminalRegional_source_weighted_bound {D : ReferenceData}
    (R : TerminalRegionalData D) (i : Fin 2)
    (E : RadialModeL2 D ≃L[ℝ] RadialModeL2 D) (w : ℝ → ℝ)
    (hE : ∀ u, E u =ᵐ[radialHilbertMeasure D] fun r => w r * u r)
    {A : ℝ} (hA : 0 ≤ A)
    (hlocal : ∀ r ∈ tsupport (deriv (R.cutoff i)), |w r| ≤ A) :
    ‖(E.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ))
      (terminalCapInnerSource R.matching.innerLeft R.matching.innerRight
        (R.matching.boundaryScale i) (R.cutoff i) (R.standIn i) (R.source_memLp i))‖ ≤
      A * ((R.sourceCost * sqrt (R.matching.D0 i)) * exp (-R.attenuation i)) := by
  let F := terminalCapInnerSource R.matching.innerLeft R.matching.innerRight
    (R.matching.boundaryScale i) (R.cutoff i) (R.standIn i) (R.source_memLp i)
  have hFs : F.2 = 0 := rfl
  have hs : ∀ᵐ r ∂radialHilbertMeasure D,
      r ∉ tsupport (deriv (R.cutoff i)) → F.1 r = 0 := by
    filter_upwards [terminalCapInnerSource_ae (R.source_memLp i)
      (R.cutoff_derivative_inside i)] with r hr hout
    rw [hr]
    by_contra hn
    exact hout (terminalCapHilbertSource_support (R.matching.boundaryScale i)
      D.w (R.cutoff i) (R.standIn i) hn)
  have hnorm : ‖F‖ ≤ (R.sourceCost * sqrt (R.matching.D0 i)) *
      exp (-R.attenuation i) :=
    (terminalCapInnerSource_norm_le_eLpNorm R.matching.innerLeft R.matching.innerRight
      (R.matching.boundaryScale i) (R.cutoff i) (R.standIn i)
      (R.source_memLp i)).trans (R.source_bound i)
  exact (matchedMode_weighted_zeroScalar_support_bound E w hE F hFs _
    hs hA hlocal).trans (mul_le_mul_of_nonneg_left hnorm hA)

end ContinuousFlexibility.Radial
