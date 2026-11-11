import ContinuousFlexibility.Analysis.N01aReferenceNormalPairing

/-!
# Weighted cells of the actual derivative of the eigenfunction

Testing the weak normal equation with interior cutoffs of
`localizer² * phi' * cos(2θ)` proves the localized L² bound directly.
Only the square-integrability that is actually present in the frozen
normal estimate is used for its supplied derivative representative.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

private theorem n01a_le_of_sqrt_product {I J : ℝ} (hI : 0 ≤ I) (hJ : 0 ≤ J)
    (h : I ≤ Real.sqrt J * Real.sqrt I) : I ≤ J := by
  by_cases hz : I = 0
  · simpa only [hz] using hJ
  have hp : 0 < Real.sqrt I :=
    Real.sqrt_pos.mpr (lt_of_le_of_ne hI (fun he => hz he.symm))
  have hs : Real.sqrt I ≤ Real.sqrt J := by
    nlinarith [Real.sq_sqrt hI]
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg I) hs 2
  simpa only [Real.sq_sqrt hI, Real.sq_sqrt hJ] using hsq

private theorem n01a_normalized_sqrt_product {I J : ℝ} :
    (2 * Real.pi)⁻¹ *
      (Real.sqrt ((2 * Real.pi) * J) * Real.sqrt ((2 * Real.pi) * I)) =
      Real.sqrt J * Real.sqrt I := by
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  rw [Real.sqrt_mul hπ, Real.sqrt_mul hπ]
  calc
    _ = ((2 * Real.pi)⁻¹ * (Real.sqrt (2 * Real.pi)) ^ 2) *
        (Real.sqrt J * Real.sqrt I) := by ring
    _ = _ := by rw [Real.sq_sqrt hπ, inv_mul_cancel₀ (by positivity), one_mul]

theorem weakNormalDerivative_reference_cell_square_le {D : ReferenceData}
    (hab : D.a ≤ D.b) (hpart : RadialPartition D) (hphi : EndpointFlat D D.phi)
    {u ur : PolarPoint → ℝ} (hweak : WeakNormalDerivative D u ur)
    (hmode : referenceMode u 2 =ᵐ[volume.restrict (radialCore D)] D.phi)
    (hur : RadialCellIntegrable D ur) (m : ℕ) :
    referenceCellSquare D m (fun p => deriv D.phi p.1 * Radial.cosineMode 2 p.2) ≤
      referenceCellSquare D m ur := by
  have hphid : ContDiff ℝ ∞ (deriv D.phi) := (contDiff_infty_iff_deriv.mp hphi.1).2
  have hl : ContDiff ℝ ∞ (D.localizer m) := hpart.1 m
  let ψn (n : ℕ) : ℝ → ℝ := Radial.intervalCutoffTest D.a D.b
    (fun r => D.localizer m r ^ 2 * deriv D.phi r) n
  let f : PolarPoint → ℝ := fun p => D.localizer m p.1 * ur p
  let g : PolarPoint → ℝ := fun p =>
    D.localizer m p.1 * (deriv D.phi p.1 * Radial.cosineMode 2 p.2)
  let gn (n : ℕ) (p : PolarPoint) : ℝ := Radial.intervalTestCutoff D.a D.b n p.1 * g p
  have hgc : Continuous g := by
    dsimp only [g]
    unfold Radial.cosineMode
    fun_prop
  have hgnc (n : ℕ) : Continuous (gn n) :=
    ((Radial.contDiff_intervalTestCutoff D.a D.b n).continuous.comp continuous_fst).mul hgc
  have hfi : Integrable (fun p => f p ^ 2) (radialPhysicalMeasure D) := hur.integrable_square m
  have hgi : Integrable (fun p => g p ^ 2) (radialPhysicalMeasure D) :=
    (continuous_memLp_radialPhysicalMeasure hgc).integrable_sq
  have hgni (n : ℕ) : Integrable (fun p => gn n p ^ 2) (radialPhysicalMeasure D) :=
    (continuous_memLp_radialPhysicalMeasure (hgnc n)).integrable_sq
  have hgn_bound (n : ℕ) : (∫ p, gn n p ^ 2 ∂radialPhysicalMeasure D) ≤
      (∫ p, g p ^ 2 ∂radialPhysicalMeasure D) := by
    apply integral_mono (hgni n) hgi
    intro p
    have hc0 := Radial.intervalTestCutoff_nonneg D.a D.b n p.1
    have hc1 := Radial.intervalTestCutoff_le_one D.a D.b n p.1
    have hc2 : Radial.intervalTestCutoff D.a D.b n p.1 ^ 2 ≤ 1 := by nlinarith
    dsimp only [gn]
    rw [mul_pow]
    exact (mul_le_mul_of_nonneg_right hc2 (sq_nonneg (g p))).trans_eq (one_mul _)
  have hψn (n : ℕ) : ContDiff ℝ ∞ (ψn n) :=
    Radial.contDiff_intervalCutoffTest ((hl.pow 2).mul hphid) n
  have hpair (n : ℕ) :
      (∫ r in D.a..D.b, deriv D.phi r * ψn n r) =
        ∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ) * gn n (r, θ)) := by
    rw [← weakNormalDerivative_mode_pairing hab hphi hweak hmode (hψn n)
      (Radial.intervalCutoffTest_hasCompactSupport D.a D.b _ n)
      (Radial.intervalCutoffTest_tsupport_subset D.a D.b _ n)]
    apply intervalIntegral.integral_congr
    intro r _
    apply congrArg radialAngularMean
    funext θ
    dsimp only [ψn, f, gn, g, Radial.intervalCutoffTest]
    ring
  have hbound (n : ℕ) :
      (∫ r in D.a..D.b, deriv D.phi r * ψn n r) ≤
        (2 * Real.pi)⁻¹ *
          (Real.sqrt (∫ p, f p ^ 2 ∂radialPhysicalMeasure D) *
            Real.sqrt (∫ p, g p ^ 2 ∂radialPhysicalMeasure D)) := by
    rw [hpair]
    apply (le_abs_self _).trans
    apply (abs_radial_pairing_le_sqrt_squares hab hfi (hgni n)).trans
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hgn_bound n)) (Real.sqrt_nonneg _))
      (by positivity)
  have hidentity (n : ℕ) :
      (∫ r in D.a..D.b, deriv D.phi r * ψn n r) =
        ∫ r in D.a..D.b, Radial.intervalTestCutoff D.a D.b n r *
          (D.localizer m r * deriv D.phi r) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only [ψn, Radial.intervalCutoffTest]
    ring
  have hlim : Tendsto (fun n => ∫ r in D.a..D.b, deriv D.phi r * ψn n r) atTop
      (𝓝 (referenceCellSquare D m
        (fun p => deriv D.phi p.1 * Radial.cosineMode 2 p.2))) := by
    simp_rw [hidentity]
    rw [referenceCellSquare_cosine_lift D m (deriv D.phi) 2 (by decide)]
    exact tendsto_integral_cutoff_mul hab
      (((hl.continuous.mul hphid.continuous).pow 2).integrableOn_Icc)
  have hcell : referenceCellSquare D m
      (fun p => deriv D.phi p.1 * Radial.cosineMode 2 p.2) ≤
      (2 * Real.pi)⁻¹ *
        (Real.sqrt (∫ p, f p ^ 2 ∂radialPhysicalMeasure D) *
          Real.sqrt (∫ p, g p ^ 2 ∂radialPhysicalMeasure D)) :=
    le_of_tendsto hlim (Eventually.of_forall hbound)
  have hfint : (∫ p, f p ^ 2 ∂radialPhysicalMeasure D) =
      (2 * Real.pi) * referenceCellSquare D m ur :=
    integral_reference_cell_square hab hur m
  have hgint : (∫ p, g p ^ 2 ∂radialPhysicalMeasure D) =
      (2 * Real.pi) * referenceCellSquare D m
        (fun p => deriv D.phi p.1 * Radial.cosineMode 2 p.2) :=
    integral_reference_cell_square hab
      (radialCellIntegrable_cosine_lift hpart hphid.continuous 2) m
  rw [hfint, hgint, n01a_normalized_sqrt_product] at hcell
  exact n01a_le_of_sqrt_product (referenceCellSquare_nonneg hab m _)
    (referenceCellSquare_nonneg hab m ur) hcell

theorem weakNormalDerivative_reference_output {D : ReferenceData}
    (hab : D.a ≤ D.b) (hpart : RadialPartition D) (hphi : EndpointFlat D D.phi)
    {u ur : PolarPoint → ℝ} (hweak : WeakNormalDerivative D u ur)
    (hmode : referenceMode u 2 =ᵐ[volume.restrict (radialCore D)] D.phi)
    {γ M : ℝ} (hur : OutputRealization D γ M 0 (ur, 0)) :
    OutputRealization D γ M 0
      ((fun p => deriv D.phi p.1 * Radial.cosineMode 2 p.2), 0) := by
  have hrem : outputRemainder D 0 (ur, 0) = ur := by
    funext p
    simp only [outputRemainder, zero_mul, sub_zero]
  have hcells : RadialCellIntegrable D ur := by simpa only [hrem] using hur.1
  have hs : Summable (outputCellSquare D γ M ur) := by simpa only [hrem] using hur.2.1
  apply outputRealization_cosine_lift_of_summable hpart
    (contDiff_infty_iff_deriv.mp hphi.1).2.continuous
  apply Summable.of_nonneg_of_le
    (fun m => outputCellSquare_nonneg hab γ M _ m) _ hs
  intro m
  exact mul_le_mul_of_nonneg_left
    (weakNormalDerivative_reference_cell_square_le hab hpart hphi hweak hmode hcells m)
    (Real.exp_pos _).le

end ContinuousFlexibility.Statements
