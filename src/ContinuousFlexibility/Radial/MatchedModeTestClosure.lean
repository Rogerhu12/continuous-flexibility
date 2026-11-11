import ContinuousFlexibility.Radial.MatchedModeTestApprox

/-!
# Closing the frozen modal test class

The actual Hilbert L² domain controls the ordinary L¹ coefficients w u
and w' u. Affine compression therefore extends every compact-core weak
equation to all smooth tests whose ordinary support lies in the core,
which is exactly the test class of ModeLocalEquation.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem matchedMode_density_intervalIntegrable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (u : RadialModeL2 D) :
    IntervalIntegrable (fun r => matchingDensity D r * u r) volume D.a D.b := by
  letI : IsFiniteMeasure (radialHilbertMeasure D) := radialHilbertMeasure_isFinite hD
  have hu : Integrable (fun r => u r) (radialHilbertMeasure D) :=
    MemLp.integrable (by norm_num) (Lp.memLp u)
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (matchingProfileGeometry hD).2.1.le).mpr
      ((matchingDensity_integrable_iff hD _).mp hu)

theorem matchedMode_profile_intervalIntegrable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (u : RadialModeL2 D) :
    IntervalIntegrable (fun r => u r * D.w r) volume D.a D.b := by
  have hg := matchingProfileGeometry hD
  have hi := (matchedMode_density_intervalIntegrable hD u).mul_continuousOn
    (((continuous_id.pow 2).div_const 12).continuousOn)
  apply hi.congr_uIoo
  intro r hr
  rw [uIoo_of_le hg.2.1.le] at hr
  have hr0 : r ≠ 0 := (hg.1.trans hr.1).ne'
  simp only [Pi.pow_apply, id_eq]
  unfold matchingDensity
  field_simp [hr0]
  <;> ring

theorem matchedMode_profileDeriv_intervalIntegrable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (u : RadialModeL2 D) :
    IntervalIntegrable (fun r => u r * deriv D.w r) volume D.a D.b := by
  have hg := matchingProfileGeometry hD
  have hi₀ := (matchingDensity_integrable_iff hD
    (fun r => u r * (deriv D.w r / D.w r))).mp
      ((Lp.memLp u).integrable_mul (matchingLogDerivative_memLp hD))
  have hi₁ : IntervalIntegrable
      (fun r => matchingDensity D r * (u r * (deriv D.w r / D.w r)))
      volume D.a D.b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hg.2.1.le).mpr hi₀
  have hi := hi₁.mul_continuousOn (((continuous_id.pow 2).div_const 12).continuousOn)
  apply hi.congr_uIoo
  intro r hr
  rw [uIoo_of_le hg.2.1.le] at hr
  have hr0 : r ≠ 0 := (hg.1.trans hr.1).ne'
  have hw0 : D.w r ≠ 0 := (hg.2.2.2.2.1 r hr).ne'
  simp only [Pi.pow_apply, id_eq]
  unfold matchingDensity
  field_simp [hr0, hw0]
  <;> ring

theorem matchedMode_potential_intervalIntegrable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (u : RadialModeL2 D) (j : ℕ) :
    IntervalIntegrable (fun r => u r * deriv D.w r * ((j : ℝ) ^ 2 / r))
      volume D.a D.b := by
  have hg := matchingProfileGeometry hD
  apply (matchedMode_profileDeriv_intervalIntegrable hD u).mul_continuousOn
  rw [uIcc_of_le hg.2.1.le]
  apply continuous_const.continuousOn.div continuous_id.continuousOn
  intro r hr
  exact (hg.1.trans_le hr.1).ne'

theorem matchedMode_jacobi_pairing_expansion {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (u : RadialModeL2 D)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (j : ℕ) :
    (∫ r in D.a..D.b, u r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) =
      (∫ r in D.a..D.b, (u r * D.w r) * deriv (deriv ψ) r) +
      (∫ r in D.a..D.b, (u r * deriv D.w r) * deriv ψ r) -
      (∫ r in D.a..D.b, (u r * deriv D.w r * ((j : ℝ) ^ 2 / r)) * ψ r) := by
  have hdψ : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hddψ : ContDiff ℝ ∞ (deriv (deriv ψ)) := (contDiff_infty_iff_deriv.mp hdψ).2
  have hi₂ := (matchedMode_profile_intervalIntegrable hD u).mul_continuousOn
    hddψ.continuous.continuousOn
  have hi₁ := (matchedMode_profileDeriv_intervalIntegrable hD u).mul_continuousOn
    hdψ.continuous.continuousOn
  have hi₀ := (matchedMode_potential_intervalIntegrable hD u j).mul_continuousOn
    hψ.continuous.continuousOn
  rw [← intervalIntegral.integral_add hi₂ hi₁,
    ← intervalIntegral.integral_sub (hi₂.add hi₁) hi₀]
  apply intervalIntegral.integral_congr
  intro r _
  change u r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r =
    (u r * D.w r) * deriv (deriv ψ) r +
      (u r * deriv D.w r) * deriv ψ r -
        (u r * deriv D.w r * ((j : ℝ) ^ 2 / r)) * ψ r
  rw [matchingJacobi_expansion hD hψ j r]
  ring

theorem matchedMode_jacobi_pairing_tendsto {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (u : RadialModeL2 D)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (j : ℕ) (c : ℝ) :
    Tendsto (fun n => ∫ r in D.a..D.b, u r *
      radialJacobi ((j : ℝ) ^ 2) D.w
        (matchedTestDilate c (matchedTestScale n) ψ) r)
      atTop (𝓝 (∫ r in D.a..D.b, u r *
        radialJacobi ((j : ℝ) ^ 2) D.w ψ r)) := by
  have hab := (matchingProfileGeometry hD).2.1.le
  have h₂ := matchedTestDilate_tendsto_second_integral hab
    (matchedMode_profile_intervalIntegrable hD u) hψ hcψ c
  have h₁ := matchedTestDilate_tendsto_deriv_integral hab
    (matchedMode_profileDeriv_intervalIntegrable hD u) hψ hcψ c
  have h₀ := matchedTestDilate_tendsto_intervalIntegral hab
    (matchedMode_potential_intervalIntegrable hD u j) hψ.continuous hcψ c
  have he :
      (fun n => ∫ r in D.a..D.b, u r *
        radialJacobi ((j : ℝ) ^ 2) D.w (matchedTestDilate c (matchedTestScale n) ψ) r) =
      (fun n =>
        (∫ r in D.a..D.b, (u r * D.w r) *
          deriv (deriv (matchedTestDilate c (matchedTestScale n) ψ)) r) +
        (∫ r in D.a..D.b, (u r * deriv D.w r) *
          deriv (matchedTestDilate c (matchedTestScale n) ψ) r) -
        (∫ r in D.a..D.b, (u r * deriv D.w r * ((j : ℝ) ^ 2 / r)) *
          matchedTestDilate c (matchedTestScale n) ψ r)) := by
    funext n
    exact matchedMode_jacobi_pairing_expansion hD u
      (matchedTestDilate_contDiff c (matchedTestScale n) hψ) j
  rw [he, matchedMode_jacobi_pairing_expansion hD u hψ j]
  exact (h₂.add h₁).sub h₀

/-- Compactly contained tests suffice for the exact frozen modal graph.
The proof uses the actual model L² vectors, not an assumed graph closure. -/
theorem modeLocalEquation_of_compactCore {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {j : ℕ} {U F : RadialModePair D}
    (hEq : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ radialCore D →
      (∫ r in D.a..D.b, U.1 r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) -
        U.2 * (∫ r in D.a..D.b, referenceColumn D r * ψ r) =
        -(∫ r in D.a..D.b, matchingDensity D r * F.1 r * ψ r)) :
    ModeLocalEquation D j (radialCore D) U F := by
  intro ψ hψ hcψ hψs
  change (∫ r in D.a..D.b, U.1 r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) -
    U.2 * (∫ r in D.a..D.b, referenceColumn D r * ψ r) =
      -(∫ r in D.a..D.b, matchingDensity D r * F.1 r * ψ r)
  have hg := matchingProfileGeometry hD
  let c : ℝ := (D.a + D.b) / 2
  let ψn : ℕ → ℝ → ℝ := fun n => matchedTestDilate c (matchedTestScale n) ψ
  have hn (n : ℕ) :
      (∫ r in D.a..D.b, U.1 r * radialJacobi ((j : ℝ) ^ 2) D.w (ψn n) r) -
        U.2 * (∫ r in D.a..D.b, referenceColumn D r * ψn n r) =
        -(∫ r in D.a..D.b, matchingDensity D r * F.1 r * ψn n r) :=
    hEq (ψn n) (matchedTestDilate_contDiff c (matchedTestScale n) hψ)
      (matchedTestDilate_hasCompactSupport hg.2.1 (matchedTestScale_one_lt n) hψs)
      (matchedTestDilate_tsupport hg.2.1 (matchedTestScale_one_lt n) hψs)
  have hJ := matchedMode_jacobi_pairing_tendsto hD U.1 hψ hcψ j c
  have hcol : IntervalIntegrable (referenceColumn D) volume D.a D.b :=
    (matchingColumn_continuousOn hD hB).intervalIntegrable_of_Icc hg.2.1.le
  have hC := matchedTestDilate_tendsto_intervalIntegral hg.2.1.le hcol
    hψ.continuous hcψ c
  have hF := matchedTestDilate_tendsto_intervalIntegral hg.2.1.le
    (matchedMode_density_intervalIntegrable hD F.1) hψ.continuous hcψ c
  have hleft := hJ.sub ((tendsto_const_nhds (x := U.2)).mul hC)
  have hright := hF.neg
  have heq :
      (fun n => (∫ r in D.a..D.b, U.1 r *
        radialJacobi ((j : ℝ) ^ 2) D.w (matchedTestDilate c (matchedTestScale n) ψ) r) -
        U.2 * (∫ r in D.a..D.b,
          referenceColumn D r * matchedTestDilate c (matchedTestScale n) ψ r)) =
      (fun n => -(∫ r in D.a..D.b,
        (matchingDensity D r * F.1 r) * matchedTestDilate c (matchedTestScale n) ψ r)) := by
    funext n
    exact hn n
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

end ContinuousFlexibility.Radial
