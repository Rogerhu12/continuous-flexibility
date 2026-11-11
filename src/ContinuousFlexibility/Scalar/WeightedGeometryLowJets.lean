import ContinuousFlexibility.Scalar.WeightedGeometryBall
import ContinuousFlexibility.Scalar.WeightedOrdinaryPointwise
import ContinuousFlexibility.Scalar.WeightedPartialIdentities
import ContinuousFlexibility.Scalar.WeightedReferenceBounds

/-!
# Actual low-order bounds for the common scalar geometry ball

Every constant below is obtained from the frozen reference, material and
physical-space hypotheses.  In particular, the reciprocal reference bound
converts the quantitative decoded mixed jets into bounds relative to the
actual flat reference profile, uniformly up to both endpoints.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem referenceProfile_uniform_upper_bound (hD : IsAccumulatingProfile D) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r ∈ Ioo D.a D.b, D.w r ≤ M := by
  have hw : Continuous D.w := hD.choose_spec.1.2.2.1.1.continuous
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc D.a D.b)).bddAbove_image
    hw.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun r hr => ?_⟩
  exact (hM ⟨r, ⟨hr.1.le, hr.2.le⟩, rfl⟩).trans (le_max_left _ _)

/-- Fixed ordinary jets of decoded heights are bounded relative to the
reference profile.  The input order is explicit and the constant is chosen
before the height and the point. -/
theorem scalarMixedDerivative_le_reference_grading
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (a b base : ℕ) (hbase : a + b + 2 ≤ base) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : ScalarHeightSpace S) (p : PolarPoint),
      p ∈ annularOpen D →
      |mixedDerivative a b ((S.height scalarBeta).decode v) p| ≤
        C * scalarHeightGrading S base v * D.w p.1 := by
  obtain ⟨J, hJ, hJbound⟩ :=
    mixedDerivative_decode_le_weighted_grading hT (hS.1 scalarBeta) a b
  obtain ⟨K, hK, hKbound⟩ := weighted_referenceInverseJet_bound hD hT
    (show 0 < scalarBeta by norm_num [scalarBeta]) 1 0
  refine ⟨J * K, mul_nonneg hJ hK, ?_⟩
  intro v p hp
  have hw : 0 < D.w p.1 := hD.choose_spec.1.2.2.2.2.1 p.1 hp.1
  have hreciprocal : T.H p.1 ^ scalarBeta * T.M p.1 * (D.w p.1)⁻¹ ≤ K := by
    simpa only [Real.rpow_one, radialJet, abs_of_pos (inv_pos.mpr hw)] using
      hKbound p.1 hp.1
  have hweight : T.H p.1 ^ scalarBeta * T.M p.1 ≤ K * D.w p.1 := by
    have h := mul_le_mul_of_nonneg_right hreciprocal hw.le
    simpa only [mul_assoc, inv_mul_cancel₀ hw.ne', mul_one] using h
  have hpnonneg : 0 ≤ scalarHeightGrading S (a + b + 2) v := apply_nonneg _ _
  calc
    _ ≤ J * T.H p.1 ^ scalarBeta * T.M p.1 *
        scalarHeightGrading S (a + b + 2) v := hJbound v p hp
    _ = J * (T.H p.1 ^ scalarBeta * T.M p.1) *
        scalarHeightGrading S (a + b + 2) v := by ring
    _ ≤ J * (K * D.w p.1) * scalarHeightGrading S (a + b + 2) v :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hweight hJ) hpnonneg
    _ = (J * K) * scalarHeightGrading S (a + b + 2) v * D.w p.1 := by ring
    _ ≤ (J * K) * scalarHeightGrading S base v * D.w p.1 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (scalarHeightGrading_monotone S hbase v)
          (mul_nonneg hJ hK)) hw.le

/-- The normalized angular mean has operator bound one in the uniform norm. -/
theorem abs_angularMean_le_of_uniform_bound {f : ℝ → ℝ} {C : ℝ}
    (hf : ∀ θ, |f θ| ≤ C) : |angularMean f| ≤ C := by
  have hi : |∫ θ in (0 : ℝ)..Real.pi, f θ| ≤ C * Real.pi := by
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos Real.pi_pos] using
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := Real.pi) (f := f)
        (fun θ _ => by simpa only [Real.norm_eq_abs] using hf θ))
  unfold angularMean
  rw [abs_mul, abs_of_pos (div_pos zero_lt_one Real.pi_pos)]
  calc
    _ ≤ (1 / Real.pi) * (C * Real.pi) :=
      mul_le_mul_of_nonneg_left hi (div_nonneg zero_le_one Real.pi_pos.le)
    _ = C := by field_simp [Real.pi_ne_zero]

private theorem scalar_div_radius_bound
    (hD : IsAccumulatingProfile D) {r z C P : ℝ} (hr : r ∈ Ioo D.a D.b)
    (hC : 0 ≤ C) (hP : 0 ≤ P) (hz : |z| ≤ C * P) :
    |z / r| ≤ (C / D.a) * P := by
  have ha : 0 < D.a := hD.choose_spec.1.1
  have hrad : 0 < r := ha.trans hr.1
  rw [abs_div, abs_of_pos hrad]
  calc
    _ ≤ (C * P) / r := div_le_div_of_nonneg_right hz hrad.le
    _ ≤ (C * P) / D.a := div_le_div_of_nonneg_left (mul_nonneg hC hP) ha hr.1.le
    _ = (C / D.a) * P := by ring

/-- The cutoff derivative is supported in a compact subset where the
reference profile is positive.  Its reference-normalized supremum is finite. -/
theorem scalarCutoff_deriv_le_reference
    (hD : IsAccumulatingProfile D) (hS : IsPhysicalSpaces D T S) :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧ ∀ r ∈ Ioo D.a D.b, |deriv S.chiLeft r| ≤ Cχ * D.w r := by
  obtain ⟨K, hK, hKsub, _, hzero⟩ := hS.2.2.1.2.2
  have hw : Continuous D.w := hD.choose_spec.1.2.2.1.1.continuous
  have hwpos : ∀ r ∈ Ioo D.a D.b, 0 < D.w r := hD.choose_spec.1.2.2.2.2.1
  have hχ : Continuous (deriv S.chiLeft) :=
    (contDiff_infty_iff_deriv.mp hS.2.2.1.1).2.continuous
  have hratio : ContinuousOn (fun r => deriv S.chiLeft r / D.w r) K :=
    hχ.continuousOn.div hw.continuousOn (fun r hr => (hwpos r (hKsub hr)).ne')
  obtain ⟨C, hC⟩ := hK.bddAbove_image hratio.abs
  refine ⟨max C 0, le_max_right _ _, fun r hr => ?_⟩
  by_cases hrK : r ∈ K
  · have hb : |deriv S.chiLeft r / D.w r| ≤ max C 0 :=
      (hC ⟨r, hrK, rfl⟩).trans (le_max_left _ _)
    rw [abs_div, abs_of_pos (hwpos r hr)] at hb
    exact (div_le_iff₀ (hwpos r hr)).mp hb
  · rw [hzero r hrK, abs_zero]
    exact mul_nonneg (le_max_right _ _) (hwpos r hr).le

/-- The four quantitative decoder bounds used by the geometry ball all hold
at the same actual input grading, namely order four. -/
theorem scalarHeight_low_jet_bounds
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) :
    ∃ Cm Cr Ct Ctt : ℝ, 0 ≤ Cm ∧ 0 ≤ Cr ∧ 0 ≤ Ct ∧ 0 ≤ Ctt ∧
      (∀ v : ScalarHeightSpace S, ∀ r ∈ Ioo D.a D.b,
        |angularMean (fun θ => (S.height scalarBeta).decode v (r, θ))| ≤
          Cm * scalarHeightGrading S 4 v) ∧
      (∀ v : ScalarHeightSpace S, ∀ p ∈ annularOpen D,
        |radialPartial ((S.height scalarBeta).decode v) p| ≤
          Cr * scalarHeightGrading S 4 v * D.w p.1) ∧
      (∀ v : ScalarHeightSpace S, ∀ p ∈ annularOpen D,
        |heightAngular ((S.height scalarBeta).decode v) p| ≤
          Ct * scalarHeightGrading S 4 v) ∧
      (∀ v : ScalarHeightSpace S, ∀ p ∈ annularOpen D,
        |angularPartial (heightAngular ((S.height scalarBeta).decode v)) p| ≤
          Ctt * scalarHeightGrading S 4 v * D.w p.1) := by
  obtain ⟨M, hM, hMbound⟩ := referenceProfile_uniform_upper_bound hD
  obtain ⟨C₀, hC₀, hC₀bound⟩ :=
    scalarMixedDerivative_le_reference_grading hD hT hS 0 0 4 (by omega)
  obtain ⟨Cr, hCr, hCrbound⟩ :=
    scalarMixedDerivative_le_reference_grading hD hT hS 1 0 4 (by omega)
  obtain ⟨Ct, hCt, hCtbound⟩ :=
    scalarMixedDerivative_le_reference_grading hD hT hS 0 1 4 (by omega)
  obtain ⟨Ctt, hCtt, hCttbound⟩ :=
    scalarMixedDerivative_le_reference_grading hD hT hS 0 2 4 (by omega)
  have ha : 0 < D.a := hD.choose_spec.1.1
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hsmooth (v : ScalarHeightSpace S) :
      ContDiffOn ℝ ∞ ((S.height scalarBeta).decode v) (annularOpen D) :=
    ((hS.1 scalarBeta).2.2.2.1 v).1
  refine ⟨C₀ * M, Cr, Ct * M / D.a, Ctt / D.a,
    mul_nonneg hC₀ hM, hCr, div_nonneg (mul_nonneg hCt hM) ha.le,
    div_nonneg hCtt ha.le, ?_, ?_, ?_, ?_⟩
  · intro v r hr
    apply abs_angularMean_le_of_uniform_bound
    intro θ
    have hjet : |(S.height scalarBeta).decode v (r, θ)| ≤
        C₀ * scalarHeightGrading S 4 v * D.w r := by
      simpa only [mixedDerivative, iteratedDeriv_zero] using
        hC₀bound v (r, θ) ⟨hr, mem_univ _⟩
    calc
      _ ≤ C₀ * scalarHeightGrading S 4 v * D.w r := hjet
      _ ≤ C₀ * scalarHeightGrading S 4 v * M :=
        mul_le_mul_of_nonneg_left (hMbound r hr) (mul_nonneg hC₀ (apply_nonneg _ _))
      _ = (C₀ * M) * scalarHeightGrading S 4 v := by ring
  · intro v p hp
    rw [radialPartial_eq_mixedDerivative_on hU (hsmooth v) hp]
    exact hCrbound v p hp
  · intro v p hp
    rw [heightAngular_eq_mixedDerivative_on hU (hsmooth v) hp]
    have hb : |mixedDerivative 0 1 ((S.height scalarBeta).decode v) p| ≤
        (Ct * M) * scalarHeightGrading S 4 v := by
      calc
        _ ≤ Ct * scalarHeightGrading S 4 v * D.w p.1 := hCtbound v p hp
        _ ≤ Ct * scalarHeightGrading S 4 v * M :=
          mul_le_mul_of_nonneg_left (hMbound p.1 hp.1) (mul_nonneg hCt (apply_nonneg _ _))
        _ = (Ct * M) * scalarHeightGrading S 4 v := by ring
    exact scalar_div_radius_bound hD hp.1 (mul_nonneg hCt hM) (apply_nonneg _ _) hb
  · intro v p hp
    rw [angularPartial_heightAngular_eq_mixedDerivative_on hU (hsmooth v) hp
      (ha.trans hp.1.1).ne']
    have hw : 0 ≤ D.w p.1 := (hD.choose_spec.1.2.2.2.2.1 p.1 hp.1).le
    have hb : |mixedDerivative 0 2 ((S.height scalarBeta).decode v) p| ≤
        Ctt * (scalarHeightGrading S 4 v * D.w p.1) := by
      simpa only [mul_assoc] using hCttbound v p hp
    simpa only [mul_assoc] using
      scalar_div_radius_bound hD hp.1 hCtt (mul_nonneg (apply_nonneg _ _) hw) hb

end ContinuousFlexibility.Statements
