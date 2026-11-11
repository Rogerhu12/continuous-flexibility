import ContinuousFlexibility.Radial.InnerRadialL2Mass
import ContinuousFlexibility.Statements.RadialTargets
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# The physical energy coordinates on a positive gap

The derivative coordinate is r u' / sqrt(12), and the potential coordinate
is sqrt(j² r w' / (12 w)) u. Both lie in the existing radial L² measure.
Their squared Hilbert norm is exactly the radial energy. This identity
turns the scalar radial coercivity theorem into a bound on a closed
energy space without changing the physical source measure.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

def innerGapGradientField (u : ℝ → ℝ) (r : ℝ) : ℝ :=
  (r / Real.sqrt 12) * deriv u r

def innerGapPotentialField (w : ℝ → ℝ) (j : ℝ) (u : ℝ → ℝ) (r : ℝ) : ℝ :=
  Real.sqrt ((j ^ 2 / 12) * (r * deriv w r / w r)) * u r

theorem innerGapGradientField_continuous {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) :
    Continuous (innerGapGradientField u) :=
  (continuous_id.div_const _).mul (contDiff_infty_iff_deriv.mp hu).2.continuous

theorem innerGapPotentialField_continuousOn {a b : ℝ} {w u : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hpos : ∀ r ∈ Icc a b, 0 < w r) (j : ℝ) :
    ContinuousOn (innerGapPotentialField w j u) (Icc a b) := by
  have hc : ContinuousOn (fun r => r * deriv w r / w r) (Icc a b) :=
    (continuous_id.mul (contDiff_infty_iff_deriv.mp hw).2.continuous).continuousOn.div
      hw.continuous.continuousOn (fun r hr => (hpos r hr).ne')
  exact (Real.continuous_sqrt.comp_continuousOn (continuousOn_const.mul hc)).mul
    hu.continuous.continuousOn

theorem innerRadialGapDensity_continuousOn {a b : ℝ} (ha : 0 < a)
    {w : ℝ → ℝ} (hw : Continuous w) :
    ContinuousOn (fun r => 12 * w r / r ^ 2) (Icc a b) :=
  (continuousOn_const.mul hw.continuousOn).div (continuousOn_id.pow 2)
    (fun r hr => pow_ne_zero 2 (ha.trans_le hr.1).ne')

/-- The exact pointwise physical-energy identity. -/
theorem innerGapEnergy_weighted_square {r j : ℝ} {w u : ℝ → ℝ}
    (hr : 0 < r) (hw : 0 < w r) (hslope : 0 ≤ r * deriv w r / w r) :
    (12 * w r / r ^ 2) * innerGapGradientField u r ^ 2 +
        (12 * w r / r ^ 2) * innerGapPotentialField w j u r ^ 2 =
      w r * deriv u r ^ 2 + j ^ 2 * deriv w r / r * u r ^ 2 := by
  have hα : 0 ≤ (j ^ 2 / 12) * (r * deriv w r / w r) :=
    mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) hslope
  simp only [innerGapGradientField, innerGapPotentialField, mul_pow, div_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12), Real.sq_sqrt hα]
  field_simp [hr.ne', hw.ne'] <;> ring

abbrev InnerGapEnergyPair (D : ReferenceData) :=
  WithLp 2 (RadialModeL2 D × RadialModeL2 D)

/-- Actual energy coordinates, with zero extension into the same μ_D. -/
def innerGapEnergyPair (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (j : ℝ)
    (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) : InnerGapEnergyPair D :=
  WithLp.toLp 2
    (innerRadialIntervalToLp D hw.continuous ha hcore
      (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) (innerGapGradientField u)
      (innerGapGradientField_continuous hu).continuousOn,
    innerRadialIntervalToLp D hw.continuous ha hcore
      (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) (innerGapPotentialField D.w j u)
      (innerGapPotentialField_continuousOn hw hu hpos j))

theorem innerGapEnergyPair_fst (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (j : ℝ) (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) :
    (innerGapEnergyPair D hw ha hcore hpos j u hu).fst =
      innerRadialIntervalToLp D hw.continuous ha hcore
        (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) (innerGapGradientField u)
        (innerGapGradientField_continuous hu).continuousOn := by
  simp only [innerGapEnergyPair, WithLp.toLp_fst]

theorem innerGapEnergyPair_snd (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (j : ℝ) (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) :
    (innerGapEnergyPair D hw ha hcore hpos j u hu).snd =
      innerRadialIntervalToLp D hw.continuous ha hcore
        (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) (innerGapPotentialField D.w j u)
        (innerGapPotentialField_continuousOn hw hu hpos j) := by
  simp only [innerGapEnergyPair, WithLp.toLp_snd]

theorem innerGapEnergyPair_fst_ae (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (j : ℝ) (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) :
    (innerGapEnergyPair D hw ha hcore hpos j u hu).fst =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (innerGapGradientField u) := by
  rw [innerGapEnergyPair_fst]
  exact innerRadialIntervalToLp_ae D hw.continuous ha hcore
    (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) _ _

theorem innerGapEnergyPair_snd_ae (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (j : ℝ) (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) :
    (innerGapEnergyPair D hw ha hcore hpos j u hu).snd =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (innerGapPotentialField D.w j u) := by
  rw [innerGapEnergyPair_snd]
  exact innerRadialIntervalToLp_ae D hw.continuous ha hcore
    (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) _ _

/-- The Hilbert norm of the two energy coordinates is the full physical
radial energy, including the potential term. -/
theorem innerGapEnergyPair_norm_sq (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv D.w r / D.w r)
    (j : ℝ) (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) :
    ‖innerGapEnergyPair D hw ha hcore hpos j u hu‖ ^ 2 =
      innerRadialGapEnergy D.w u j a b := by
  rw [WithLp.prod_norm_sq_eq_of_L2, innerGapEnergyPair_fst, innerGapEnergyPair_snd,
    innerRadialIntervalToLp_norm_sq D hw.continuous hab,
    innerRadialIntervalToLp_norm_sq D hw.continuous hab]
  have hρ := innerRadialGapDensity_continuousOn (b := b) ha hw.continuous
  have hd : ContinuousOn (innerGapGradientField u) (Icc a b) :=
    (innerGapGradientField_continuous hu).continuousOn
  have hq := innerGapPotentialField_continuousOn hw hu hpos j
  unfold innerRadialGapMass innerRadialGapEnergy
  rw [← intervalIntegral.integral_add
    ((hρ.mul (hd.pow 2)).intervalIntegrable_of_Icc hab)
    ((hρ.mul (hq.pow 2)).intervalIntegrable_of_Icc hab)]
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r ∈ Icc a b := by simpa only [uIcc_of_le hab] using hr
  exact innerGapEnergy_weighted_square (ha.trans_le hr'.1) (hpos r hr') (hslope r hr')

theorem innerGapEnergyPair_coercive (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b s : ℝ} (hab : a ≤ b) (ha : 0 < a) (hs : 0 ≤ s)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, s ≤ r * deriv D.w r / D.w r)
    (j : ℝ) (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) :
    ((s / 12) * j ^ 2) *
        ‖innerRadialIntervalToLp D hw.continuous ha hcore
          (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) u hu.continuous.continuousOn‖ ^ 2 ≤
      ‖innerGapEnergyPair D hw ha hcore hpos j u hu‖ ^ 2 := by
  rw [innerRadialIntervalToLp_norm_sq D hw.continuous hab,
    innerGapEnergyPair_norm_sq D hw hab ha hcore hpos
      (fun r hr => hs.trans (hslope r hr))]
  exact innerRadialGap_coercive hab ha hw hu hpos hslope j

end ContinuousFlexibility.Radial
