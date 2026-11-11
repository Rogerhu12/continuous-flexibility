import ContinuousFlexibility.Radial.InnerRadialPotentialMultiplier
import ContinuousFlexibility.Radial.InnerRadialH1Density
import ContinuousFlexibility.Radial.InnerRadialL2Pairing
import ContinuousFlexibility.Radial.InnerRadialGreen

/-!
# True physical Green boundary pairings for smooth local fields

The energy uses the actual radial measure, signed potential and
normalized derivative. Its residual on the fixed physical affine hats
is exactly the classical outward conormal. This identifies the finite
weak interface with the physical Dirichlet-to-Neumann matrix.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff InnerProductSpace

theorem innerRadial_pairing_of_indicator (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (hab : a ≤ b) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r)
    {U V : RadialModeL2 D} {u v : ℝ → ℝ}
    (hU : (U : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator u)
    (hV : (V : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator v) :
    ⟪U, V⟫_ℝ = ∫ r in a..b, (12 * D.w r / r ^ 2) * u r * v r := by
  rw [L2.inner_def]
  calc
    _ = ∫ r, (Ioo a b).indicator (fun r => u r * v r) r ∂radialHilbertMeasure D := by
      apply integral_congr_ae
      filter_upwards [hU, hV] with r hur hvr
      rw [hur, hvr]
      by_cases hr : r ∈ Ioo a b
      · simp only [indicator_of_mem hr, RCLike.inner_apply, conj_trivial]
        ring
      · simp only [indicator_of_notMem hr, inner_zero_left]
    _ = ∫ r in Ioo a b, u r * v r ∂radialHilbertMeasure D :=
      integral_indicator measurableSet_Ioo
    _ = ∫ r in Ioo a b, (12 * D.w r / r ^ 2) * u r * v r := by
      rw [innerRadialInterval_integral D hw hcore hpos]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r _
      dsimp only
      ring
    _ = _ := by
      rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

theorem innerRadialJacobi_continuousOn_local {a b j : ℝ} (ha : 0 < a)
    {w u : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hu : ∀ r ∈ Icc a b, ContDiffAt ℝ ∞ u r) :
    ContinuousOn (radialJacobi (j ^ 2) w u) (Icc a b) := by
  have hflux : ∀ r ∈ Icc a b, ContDiffAt ℝ ∞ (fun r => w r * deriv u r) r :=
    fun r hr => hw.contDiffAt.mul ((hu r hr).derivWithin (m := ∞) (by simp))
  have hdf := innerDirichlet_deriv_continuousOn hflux
  have hpc : ContinuousOn (fun r => (j ^ 2 * deriv w r / r) * u r) (Icc a b) :=
    ((continuousOn_const.mul (contDiff_infty_iff_deriv.mp hw).2.continuous.continuousOn).div
      continuousOn_id (fun r hr => (ha.trans_le hr.1).ne')).mul
        (fun r hr => (hu r hr).continuousAt.continuousWithinAt)
  exact hdf.sub hpc

theorem innerRadial_classicalGreen {a b j : ℝ} (hab : a ≤ b)
    {w u v : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hu : ∀ r ∈ Icc a b, ContDiffAt ℝ ∞ u r)
    (hv : ∀ r ∈ Icc a b, ContDiffAt ℝ ∞ v r) :
    (∫ r in a..b, w r * deriv u r * deriv v r +
        (j ^ 2 * deriv w r / r) * u r * v r +
        radialJacobi (j ^ 2) w u r * v r) =
      v b * (w b * deriv u b) - v a * (w a * deriv u a) := by
  have hflux : ∀ r ∈ Icc a b, ContDiffAt ℝ ∞ (fun r => w r * deriv u r) r :=
    fun r hr => hw.contDiffAt.mul ((hu r hr).derivWithin (m := ∞) (by simp))
  have hfc : ContinuousOn (fun r => w r * deriv u r) (Icc a b) :=
    fun r hr => (hflux r hr).continuousAt.continuousWithinAt
  have hdf := innerDirichlet_deriv_continuousOn hflux
  have hvc : ContinuousOn v (Icc a b) :=
    fun r hr => (hv r hr).continuousAt.continuousWithinAt
  have hdv := innerDirichlet_deriv_continuousOn hv
  have hparts := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (hfc.mul hvc)
    (fun r hr => ((hflux r (Ioo_subset_Icc_self hr)).differentiableAt (by simp)).hasDerivAt.mul
      ((hv r (Ioo_subset_Icc_self hr)).differentiableAt (by simp)).hasDerivAt)
    (((hdf.mul hvc).add (hfc.mul hdv)).intervalIntegrable_of_Icc hab)
  calc
    _ = ∫ r in a..b,
        deriv (fun t => w t * deriv u t) r * v r +
          (w r * deriv u r) * deriv v r := by
      apply intervalIntegral.integral_congr
      intro r _
      unfold radialJacobi
      ring
    _ = _ := by simpa only [Pi.mul_apply, mul_comm] using hparts

theorem innerRadial_smooth_energyGreen (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j : ℝ} (hab : a ≤ b) (ha : 0 < a)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    {u v : ℝ → ℝ} (hu : ∀ r ∈ Icc a b, ContDiffAt ℝ ∞ u r)
    (hv : ∀ r ∈ Icc a b, ContDiffAt ℝ ∞ v r)
    {Q T : InnerRadialH1Pair D} {V F : RadialModeL2 D}
    (hQu : (Q.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator u)
    (hQd : (Q.2 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (innerGapGradientField u))
    (hTu : (T.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator v)
    (hTd : (T.2 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (innerGapGradientField v))
    (hV : InnerRadialPotentialClass D j a b Q.1 V)
    (hF : (F : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator
      (fun r => -radialJacobi (j ^ 2) D.w u r / (12 * D.w r / r ^ 2))) :
    ⟪Q.2, T.2⟫_ℝ + ⟪V, T.1⟫_ℝ - ⟪F, T.1⟫_ℝ =
      v b * (D.w b * deriv u b) - v a * (D.w a * deriv u a) := by
  have hpos' : ∀ r ∈ Ioo a b, 0 ≤ D.w r :=
    fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le
  have hVp : (V : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator
      (fun r => ((j ^ 2 / 12) * (r * deriv D.w r / D.w r)) * u r) := by
    filter_upwards [hV, hQu] with r hvr hur
    rw [hvr]
    by_cases hr : r ∈ Ioo a b
    · rw [indicator_of_mem hr, hur, indicator_of_mem hr, indicator_of_mem hr]
    · rw [indicator_of_notMem hr, indicator_of_notMem hr]
  have hg : ⟪Q.2, T.2⟫_ℝ = ∫ r in a..b, D.w r * deriv u r * deriv v r := by
    rw [innerRadial_pairing_of_indicator D hw.continuous hab hcore hpos' hQd hTd]
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc a b := by simpa only [uIcc_of_le hab] using hr
    have hr0 := (ha.trans_le hr'.1).ne'
    have hsqrt : Real.sqrt (12 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    unfold innerGapGradientField
    calc
      _ = (12 / (Real.sqrt 12) ^ 2) * D.w r * deriv u r * deriv v r := by
        field_simp [hr0, hsqrt]
        <;> ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]; norm_num
  have hp : ⟪V, T.1⟫_ℝ =
      ∫ r in a..b, (j ^ 2 * deriv D.w r / r) * u r * v r := by
    rw [innerRadial_pairing_of_indicator D hw.continuous hab hcore hpos' hVp hTu]
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc a b := by simpa only [uIcc_of_le hab] using hr
    field_simp [(ha.trans_le hr'.1).ne', (hpos r hr').ne']
    <;> ring
  have hf : ⟪F, T.1⟫_ℝ = -(∫ r in a..b, radialJacobi (j ^ 2) D.w u r * v r) := by
    rw [innerRadial_pairing_of_indicator D hw.continuous hab hcore hpos' hF hTu,
      ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc a b := by simpa only [uIcc_of_le hab] using hr
    field_simp [(ha.trans_le hr'.1).ne', (hpos r hr').ne']
    <;> ring
  have huc : ContinuousOn u (Icc a b) :=
    fun r hr => (hu r hr).continuousAt.continuousWithinAt
  have hvc : ContinuousOn v (Icc a b) :=
    fun r hr => (hv r hr).continuousAt.continuousWithinAt
  have hud := innerDirichlet_deriv_continuousOn hu
  have hvd := innerDirichlet_deriv_continuousOn hv
  have hI₁ : IntervalIntegrable (fun r => D.w r * deriv u r * deriv v r) volume a b :=
    ((hw.continuous.continuousOn.mul hud).mul hvd).intervalIntegrable_of_Icc hab
  have hI₂ : IntervalIntegrable (fun r => (j ^ 2 * deriv D.w r / r) * u r * v r) volume a b :=
    ((((continuousOn_const.mul
      (contDiff_infty_iff_deriv.mp hw).2.continuous.continuousOn).div continuousOn_id
        (fun r hr => (ha.trans_le hr.1).ne')).mul huc).mul hvc).intervalIntegrable_of_Icc hab
  have hI₃ : IntervalIntegrable (fun r => radialJacobi (j ^ 2) D.w u r * v r) volume a b :=
    ((innerRadialJacobi_continuousOn_local ha hw hu).mul hvc).intervalIntegrable_of_Icc hab
  rw [hg, hp, hf, sub_neg_eq_add, ← intervalIntegral.integral_add hI₁ hI₂,
    ← intervalIntegral.integral_add (hI₁.add hI₂) hI₃]
  exact innerRadial_classicalGreen hab hw hu hv

theorem innerRadialWeakResidual_smooth (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j : ℝ} (hab : a ≤ b) (ha : 0 < a)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    {u v : ℝ → ℝ} (hu : ∀ r ∈ Icc a b, ContDiffAt ℝ ∞ u r)
    (hv : ∀ r ∈ Icc a b, ContDiffAt ℝ ∞ v r)
    {Q T : InnerRadialH1Pair D} {V F G : RadialModeL2 D} (scalar : ℝ)
    (hQu : (Q.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator u)
    (hQd : (Q.2 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (innerGapGradientField u))
    (hTu : (T.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator v)
    (hTd : (T.2 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (innerGapGradientField v))
    (hV : InnerRadialPotentialClass D j a b Q.1 V)
    (hF : ((F - scalar • G : RadialModeL2 D) : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator
        (fun r => -radialJacobi (j ^ 2) D.w u r / (12 * D.w r / r ^ 2))) :
    innerRadialWeakResidual D Q V F G scalar T =
      v b * (D.w b * deriv u b) - v a * (D.w a * deriv u a) := by
  have h := innerRadial_smooth_energyGreen D hw hab ha hcore hpos hu hv hQu hQd hTu hTd hV hF
  rw [inner_sub_left, real_inner_smul_left] at h
  change ⟪Q.2, T.2⟫_ℝ + ⟪V, T.1⟫_ℝ + scalar * ⟪G, T.1⟫_ℝ - ⟪F, T.1⟫_ℝ = _
  linarith

/-- Evaluation on the actual fixed affine unit hat is precisely the
outward classical conormal at that endpoint. -/
theorem innerRadialWeakResidual_affineUnit (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j : ℝ} (hab : a < b) (ha : 0 < a)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    {u : ℝ → ℝ} (hu : ∀ r ∈ Icc a b, ContDiffAt ℝ ∞ u r)
    {Q : InnerRadialH1Pair D} {V F G : RadialModeL2 D} (scalar : ℝ)
    (hQu : (Q.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator u)
    (hQd : (Q.2 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (innerGapGradientField u))
    (hV : InnerRadialPotentialClass D j a b Q.1 V)
    (hF : ((F - scalar • G : RadialModeL2 D) : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator
        (fun r => -radialJacobi (j ^ 2) D.w u r / (12 * D.w r / r ^ 2)))
    (i : Fin 2) :
    innerRadialWeakResidual D Q V F G scalar
      (innerRadialAffineUnitPair D hw.continuous ha hcore hpos i) =
      bufferSign i * (D.w (if i = 0 then a else b) *
        deriv u (if i = 0 then a else b)) := by
  have h := innerRadialWeakResidual_smooth D hw hab.le ha hcore hpos hu
    (fun _ _ => (innerIntervalAffineLift_contDiff a b (innerEndpointValues i)).contDiffAt)
    scalar hQu hQd
    (innerRadialAffineUnitPair_value_ae D hw.continuous ha hcore hpos i)
    (innerRadialAffineUnitPair_gradient_ae D hw.continuous ha hcore hpos i) hV hF
  have he := innerIntervalAffineLift_endpoints hab (innerEndpointValues i)
  rw [he.1, he.2] at h
  rw [h]
  fin_cases i <;> norm_num [bufferSign, innerEndpointValues]

/-- The full fixed affine lift pairs its prescribed endpoint values
with the two true outgoing conormals. -/
theorem innerRadialWeakResidual_affineLift (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j : ℝ} (hab : a < b) (ha : 0 < a)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    {u : ℝ → ℝ} (hu : ∀ r ∈ Icc a b, ContDiffAt ℝ ∞ u r)
    {Q : InnerRadialH1Pair D} {V F G : RadialModeL2 D} (scalar : ℝ)
    (hQu : (Q.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator u)
    (hQd : (Q.2 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (innerGapGradientField u))
    (hV : InnerRadialPotentialClass D j a b Q.1 V)
    (hF : ((F - scalar • G : RadialModeL2 D) : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator
        (fun r => -radialJacobi (j ^ 2) D.w u r / (12 * D.w r / r ^ 2)))
    (z : Fin 2 → ℝ) :
    innerRadialWeakResidual D Q V F G scalar
      (innerRadialAffineLift D hw.continuous ha hcore hpos z) =
      z 1 * (D.w b * deriv u b) - z 0 * (D.w a * deriv u a) := by
  rw [innerRadialAffineLift_apply, map_add, map_smul, map_smul,
    innerRadialWeakResidual_affineUnit D hw hab ha hcore hpos hu scalar hQu hQd hV hF 0,
    innerRadialWeakResidual_affineUnit D hw hab ha hcore hpos hu scalar hQu hQd hV hF 1]
  norm_num [bufferSign, smul_eq_mul]
  <;> ring

end ContinuousFlexibility.Radial
