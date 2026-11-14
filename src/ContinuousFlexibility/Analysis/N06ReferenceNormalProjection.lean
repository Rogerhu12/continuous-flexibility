module

public import ContinuousFlexibility.Analysis.N06ReferenceGraphFourierProjection
public import ContinuousFlexibility.Radial.R11bAngularDerivativeModes

/-!
# Finite angular projection of the actual physical normal derivative

The original full-period weak normal identity commutes with the actual
cosine projection. Its normal coefficients are unique as radial L2
functions, without differentiating an L2 representative pointwise. Thus
the first normal derivative supplied by the physical inverse has the
same projected derivative as that same inverse at the projected source.

All weighted output estimates below use the original physical cell
weights. No reference chart or controlled-coordinate premise is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- On smooth tests the genuine radial derivative commutes with projection. -/
theorem n06_referenceBasisProjection_radialPartial {u : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) (I : Finset ℕ) :
    radialPartial (referenceBasisProjection I u) =
      referenceBasisProjection I (radialPartial u) := by
  funext p
  have hslice := (hasDerivAt_radialSlice
    ((referenceBasisProjection_contDiff hu I).differentiable (by simp) p)).deriv
  have hsum :
      deriv (fun r => referenceBasisProjection I u (r, p.2)) p.1 =
        ∑ n ∈ I, referenceRadialCoefficient (radialPartial u) n p.1 *
          referenceAngularBasis n p.2 := by
    change deriv (fun r => ∑ n ∈ I,
      referenceRadialCoefficient u n r * referenceAngularBasis n p.2) p.1 = _
    exact (HasDerivAt.fun_sum fun n _ =>
      (hasDerivAt_referenceRadialCoefficient hu n p.1).mul_const
        (referenceAngularBasis n p.2)).deriv
  exact hslice.symm.trans hsum

/-- This is an identity of the original weak derivatives, with arbitrary
L2 representatives and every original radial test. -/
theorem WeakNormalDerivative.n06_basisProjection {D : ReferenceData}
    {u d : PolarPoint → ℝ} (h : WeakNormalDerivative D u d) (hab : D.a ≤ D.b)
    (hu : MemLp u 2 (radialPhysicalMeasure D))
    (hd : MemLp d 2 (radialPhysicalMeasure D)) (I : Finset ℕ) :
    WeakNormalDerivative D (referenceBasisProjection I u)
      (referenceBasisProjection I d) := by
  intro φ hφ
  have hφL := r11b_continuous_memLp (D := D) hφ.1.continuous
  have hφrL := r11b_continuous_memLp (D := D)
    (r11b_radialTest_radialPartial hφ).1.continuous
  have hweak := h _ (referenceBasisProjection_test hφ I)
  rw [n06_referenceBasisProjection_radialPartial hφ.1 I] at hweak
  rw [referenceBasisProjection_integral_pairing hab hu hφrL I,
    referenceBasisProjection_integral_pairing hab hd hφL I]
  exact hweak

/-- Changing only the L2 representative of the original field preserves
its true weak normal derivative. -/
theorem WeakNormalDerivative.n06_congr_left {D : ReferenceData}
    {u v d : PolarPoint → ℝ} (h : WeakNormalDerivative D u d) (hab : D.a ≤ D.b)
    (hu : MemLp u 2 (radialPhysicalMeasure D))
    (hv : MemLp v 2 (radialPhysicalMeasure D))
    (heq : u =ᵐ[radialPhysicalMeasure D] v) : WeakNormalDerivative D v d := by
  intro φ hφ
  have hφr := r11b_continuous_memLp (D := D)
    (r11b_radialTest_radialPartial hφ).1.continuous
  have hpair : (∫ r in D.a..D.b,
      radialAngularMean (fun θ => v (r, θ) * radialPartial φ (r, θ))) =
        ∫ r in D.a..D.b,
          radialAngularMean (fun θ => u (r, θ) * radialPartial φ (r, θ)) := by
    rw [r11b_integral_angularMean_mul_eq hab hv hφr,
      r11b_integral_angularMean_mul_eq hab hu hφr]
    congr 1
    apply integral_congr_ae
    exact heq.symm.mono fun p hp => congrArg (fun x : ℝ => x * radialPartial φ p) hp
  rw [hpair]
  exact h φ hφ

/-- Separated tests give the actual one-dimensional weak normal identity
for every cosine coefficient, including the mean mode. -/
theorem WeakNormalDerivative.n06_coefficient_pairing {D : ReferenceData}
    {u d : PolarPoint → ℝ} (h : WeakNormalDerivative D u d)
    (n : ℕ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ radialCore D) :
    (∫ r in D.a..D.b, referenceRadialCoefficient u n r * deriv φ r) =
      -(∫ r in D.a..D.b, referenceRadialCoefficient d n r * φ r) := by
  have ht := r11b_radialTest_separated hφ hφc hφs
    (contDiff_referenceAngularBasis n) (referenceAngularBasis_periodic_two_pi n)
  have hw := h _ ht
  simp_rw [r11b_radialPartial_separated hφ (contDiff_referenceAngularBasis n),
    r11b_radialAngularMean_lift_pairing] at hw
  exact hw

/-- The normal coefficient is determined by the weak equation itself.
This needs no radial regularity of the original field. -/
theorem WeakNormalDerivative.n06_coefficient_unique {D : ReferenceData}
    {u d e : PolarPoint → ℝ} (hud : WeakNormalDerivative D u d) (hab : D.a ≤ D.b)
    (hd : MemLp d 2 (radialPhysicalMeasure D))
    (he : MemLp e 2 (radialPhysicalMeasure D))
    (hue : WeakNormalDerivative D u e) (n : ℕ) :
    referenceRadialCoefficient d n =ᵐ[volume.restrict (radialCore D)]
      referenceRadialCoefficient e n := by
  letI : IsFiniteMeasure (volume.restrict (radialCore D)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono (show radialCore D ⊆ Icc D.a D.b from Ioo_subset_Icc_self)).trans_lt
      isCompact_Icc.measure_lt_top⟩
  have hdP : MemLp d 2 ((volume.restrict (radialCore D)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    simpa only [radialPhysicalMeasure_eq_prod] using hd
  have heP : MemLp e 2 ((volume.restrict (radialCore D)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    simpa only [radialPhysicalMeasure_eq_prod] using he
  have hdloc : LocallyIntegrableOn (referenceRadialCoefficient d n)
      (radialCore D) volume :=
    (show IntegrableOn (referenceRadialCoefficient d n) (radialCore D) volume from
      (memLp_referenceRadialCoefficient_prod hdP n).integrable (by norm_num)).locallyIntegrableOn
  have heloc : LocallyIntegrableOn (referenceRadialCoefficient e n)
      (radialCore D) volume :=
    (show IntegrableOn (referenceRadialCoefficient e n) (radialCore D) volume from
      (memLp_referenceRadialCoefficient_prod heP n).integrable (by norm_num)).locallyIntegrableOn
  have hzero : ∀ᵐ r ∂volume, r ∈ radialCore D →
      referenceRadialCoefficient d n r - referenceRadialCoefficient e n r = 0 := by
    apply (show IsOpen (radialCore D) from isOpen_Ioo).ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hdloc.sub heloc)
    intro φ hφ hφc hφs
    have hdφ : Integrable (fun r => referenceRadialCoefficient d n r * φ r) :=
      Analysis.integrable_mul_test_of_locallyIntegrableOn_Ioo hdloc hφ.continuous hφc hφs
    have heφ : Integrable (fun r => referenceRadialCoefficient e n r * φ r) :=
      Analysis.integrable_mul_test_of_locallyIntegrableOn_Ioo heloc hφ.continuous hφc hφs
    have hpair := neg_injective <|
      (WeakNormalDerivative.n06_coefficient_pairing hud n hφ hφc hφs).symm.trans
        (WeakNormalDerivative.n06_coefficient_pairing hue n hφ hφc hφs)
    rw [r11b_intervalIntegral_mul_interior_test hab _ _ hφs,
      r11b_intervalIntegral_mul_interior_test hab _ _ hφs] at hpair
    change (∫ r, φ r •
      (referenceRadialCoefficient d n r - referenceRadialCoefficient e n r)) = 0
    have hfun : (fun r => φ r •
        (referenceRadialCoefficient d n r - referenceRadialCoefficient e n r)) =
        fun r => referenceRadialCoefficient d n r * φ r -
          referenceRadialCoefficient e n r * φ r := by
      funext r
      simp only [smul_eq_mul]
      ring
    rw [hfun, integral_sub hdφ heφ, hpair, sub_self]
  have hz : ∀ᵐ r ∂volume.restrict (radialCore D),
      referenceRadialCoefficient d n r - referenceRadialCoefficient e n r = 0 := by
    rw [ae_restrict_iff' (show MeasurableSet (radialCore D) from measurableSet_Ioo)]
    exact hzero
  exact hz.mono fun r hr => sub_eq_zero.mp hr

/-- Every finite normal projection is independent of representative choices. -/
theorem WeakNormalDerivative.n06_projection_unique {D : ReferenceData}
    {u d e : PolarPoint → ℝ} (hud : WeakNormalDerivative D u d) (hab : D.a ≤ D.b)
    (hd : MemLp d 2 (radialPhysicalMeasure D))
    (he : MemLp e 2 (radialPhysicalMeasure D))
    (hue : WeakNormalDerivative D u e) (I : Finset ℕ) :
    referenceBasisProjection I d =ᵐ[radialPhysicalMeasure D]
      referenceBasisProjection I e := by
  have hall : ∀ᵐ r ∂volume.restrict (radialCore D), ∀ n : ℕ,
      referenceRadialCoefficient d n r = referenceRadialCoefficient e n r :=
    ae_all_iff.mpr fun n => WeakNormalDerivative.n06_coefficient_unique hud hab hd he hue n
  rw [radialPhysicalMeasure_eq_prod]
  filter_upwards [(Measure.quasiMeasurePreserving_fst
    (μ := volume.restrict (radialCore D))
    (ν := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))).ae hall] with p hp
  change (∑ n ∈ I, referenceRadialCoefficient d n p.1 * referenceAngularBasis n p.2) =
    ∑ n ∈ I, referenceRadialCoefficient e n p.1 * referenceAngularBasis n p.2
  exact Finset.sum_congr rfl fun n _ => congrArg (fun x : ℝ => x * referenceAngularBasis n p.2)
    (hp n)

/-- The zero-left remainder is the original representative as a function. -/
theorem n06_outputRemainder_zero (D : ReferenceData) (u : PolarPoint → ℝ) :
    outputRemainder D 0 (u, 0) = u := by
  funext p
  change u p - 0 * D.chiLeft p.1 = u p
  rw [zero_mul, sub_zero]

/-- Projection contracts the exact original zero-left-constant output norm,
also when the selected modes omit the mean. -/
theorem n06_zeroOutput_projection_bound {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ M : ℝ} {u : PolarPoint → ℝ} (hu : OutputRealization D γ M 0 (u, 0))
    (I : Finset ℕ) :
    OutputRealization D γ M 0 (referenceBasisProjection I u, 0) ∧
      outputNormSquare D γ M 0 (referenceBasisProjection I u, 0) ≤
        outputNormSquare D γ M 0 (u, 0) := by
  have hc : RadialCellIntegrable D u := by
    simpa only [n06_outputRemainder_zero] using hu.1
  have hs : Summable (outputCellSquare D γ M u) := by
    simpa only [n06_outputRemainder_zero] using hu.2.1
  have hcp := referenceBasisProjection_cellIntegrable hc I
  have hle (m : ℕ) : outputCellSquare D γ M (referenceBasisProjection I u) m ≤
      outputCellSquare D γ M u m :=
    mul_le_mul_of_nonneg_left (referenceBasisProjection_cell_sq_le hab hc I m)
      (Real.exp_pos _).le
  have hsp : Summable (outputCellSquare D γ M (referenceBasisProjection I u)) :=
    hs.of_nonneg_of_le (fun m => mul_nonneg (Real.exp_pos _).le
      (referenceCellSquare_nonneg hab m hcp)) hle
  refine ⟨?_, ?_⟩
  · exact ⟨by simpa only [n06_outputRemainder_zero] using hcp,
      by simpa only [n06_outputRemainder_zero] using hsp,
      referenceBasisProjection_periodic I u, referenceBasisProjection_even I u⟩
  · simpa only [outputNormSquare, n06_outputRemainder_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] using
      Summable.tsum_le_tsum hle hsp hs

/-- The derivative selected by the physical first-normal estimate also
differentiates the same physical inverse at every projected source. The
bound retains the original constant and both original material exponents. -/
theorem n06_referenceInverse_firstNormal_projected {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G)
    (hN : FirstNormalInverseEstimate D γ M₀ M₁ G) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ F fθ,
      SourceMember D γ M₀ F → WeakAngularDerivative D F.1 fθ →
      SourceDerivativeMember D γ M₀ fθ →
      ∃ ur : PolarPoint → ℝ, WeakNormalDerivative D (G F).1 ur ∧
        OutputRealization D γ M₁ 0 (ur, 0) ∧
        ∀ I : Finset ℕ, 0 ∈ I → 1 ∈ I →
          WeakNormalDerivative D (G (referenceBasisProjection I F.1, F.2)).1
            (referenceBasisProjection I ur) ∧
          OutputRealization D γ M₁ 0 (referenceBasisProjection I ur, 0) ∧
          outputNormSquare D γ M₁ 0 (referenceBasisProjection I ur, 0) ≤
            C0 ^ 2 * (sourceNormSquare D γ M₀ F + sourceNormSquare D γ M₀ (fθ, 0)) := by
  obtain ⟨C0, hC0, hnormal⟩ := hN
  refine ⟨C0, hC0, fun F fθ hF hfθ hθ => ?_⟩
  obtain ⟨ur, hweak, hreal, hbound⟩ := hnormal F fθ hF hfθ hθ
  have hab := hD.choose_spec.1.2.1.le
  have hu := r11b_output_memLp hD hborder hγ (hG.1 F hF).1
  have hd : MemLp ur 2 (radialPhysicalMeasure D) := by
    simpa only [n06_outputRemainder_zero] using
      r11b_outputRemainder_memLp hD hγ hreal
  refine ⟨ur, hweak, hreal, fun I h0 h1 => ?_⟩
  have hFI := n06_referenceBasisProjection_sourceMember hab hF h0
  have hrep := n06_referenceInverse_basisProjection_source
    hD hborder hγ hG (hG.1 F hF) h0 h1
  have huI := r11b_output_memLp hD hborder hγ (hG.1 _ hFI).1
  have huP : MemLp (referenceBasisProjection I (G F).1) 2 (radialPhysicalMeasure D) := by
    have huProd : MemLp (G F).1 2 ((volume.restrict (radialCore D)).prod
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
      simpa only [radialPhysicalMeasure_eq_prod] using hu
    simpa only [radialPhysicalMeasure_eq_prod] using memLp_referenceBasisProjection_prod huProd I
  have hproject := WeakNormalDerivative.n06_basisProjection hweak hab hu hd I
  have hactual := WeakNormalDerivative.n06_congr_left hproject hab huP huI hrep.2.symm
  obtain ⟨hout, hb⟩ := n06_zeroOutput_projection_bound hab hreal I
  exact ⟨hactual, hout, hb.trans hbound⟩

end ContinuousFlexibility.Radial
