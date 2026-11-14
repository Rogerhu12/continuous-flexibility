module

public import ContinuousFlexibility.Radial.CentralAuxiliaryBorder

/-!
# Actual compact columns in the central radial Hilbert space

A smooth compact radial column supported at positive radii defines its
Riesz vector by division by the actual spectral density.  The radius
change proves membership in the weighted `L²` space and identifies its
row with the ordinary radial integral.  These statements apply to the
metric-variation column constructed in `CentralTrueBorder`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace

def centralCompactColumnFunction (scale : ℝ) (g : ℝ → ℝ) (r : ℝ) : ℝ :=
  g r / centralRadialVarpi scale r

def centralCompactColumnSourceFunction (scale : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv centralRadius x / (centralRadialAmplitude scale x * centralDensityRoot x) *
    centralRadialTestPullback g x

theorem centralCompactColumnFunction_transform {scale : ℝ} (hscale : 0 < scale)
    (g : ℝ → ℝ) (x : ℝ) :
    centralRadialAmplitude scale x * centralCompactColumnFunction scale g (centralRadius x) =
      centralCompactColumnSourceFunction scale g x := by
  have ha := (centralRadialAmplitude_pos hscale x).ne'
  have hd := (deriv_centralRadius_pos x).ne'
  have hr := (centralDensityRoot_pos x).ne'
  have hvarpi : centralRadialVarpi scale (centralRadius x) =
      centralRadialAmplitude scale x ^ 2 / deriv centralRadius x := by
    apply (eq_div_iff hd).mpr
    simpa only [mul_comm] using (centralRadialVarpi_pullback_density scale x).trans
      (centralRadialAmplitude_sq hscale x).symm
  rw [centralCompactColumnFunction, centralCompactColumnSourceFunction,
    centralRadialTestPullback, hvarpi]
  field_simp [ha, hd, hr]

theorem contDiff_centralCompactColumnSourceFunction {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (centralCompactColumnSourceFunction scale g) := by
  have hd : ContDiff ℝ ∞ (deriv centralRadius) :=
    (contDiff_infty_iff_deriv.mp contDiff_centralRadius).2
  have ha : ContDiff ℝ ∞ (centralRadialAmplitude scale) :=
    contDiff_const.mul (contDiff_centralDensityRoot.mul contDiff_centralRadiusLogDerivative)
  exact (hd.div (ha.mul contDiff_centralDensityRoot) (fun x =>
    mul_ne_zero (centralRadialAmplitude_pos hscale x).ne'
      (centralDensityRoot_pos x).ne')).mul (contDiff_centralRadialTestPullback hg)

theorem centralCompactColumnSourceFunction_hasCompactSupport (scale : ℝ)
    {g : ℝ → ℝ} (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi 0) :
    HasCompactSupport (centralCompactColumnSourceFunction scale g) :=
  (centralRadialTestPullback_hasCompactSupport hc hp).mul_left

theorem centralCompactColumnFunction_memLp {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0) :
    MemLp (centralCompactColumnFunction scale g) 2 (centralRadialSpectralMeasure scale) := by
  rw [centralRadial_memLp_iff hscale]
  have heq : (fun x => centralRadialAmplitude scale x *
      centralCompactColumnFunction scale g (centralRadius x)) =
        centralCompactColumnSourceFunction scale g :=
    funext (centralCompactColumnFunction_transform hscale g)
  rw [heq]
  exact (contDiff_centralCompactColumnSourceFunction hscale hg).continuous.memLp_of_hasCompactSupport
    (centralCompactColumnSourceFunction_hasCompactSupport scale hc hp)

def centralCompactColumn {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0) : CentralRadialHilbert scale :=
  (centralCompactColumnFunction_memLp hscale hg hc hp).toLp
    (centralCompactColumnFunction scale g)

theorem centralCompactColumn_ae {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0) :
    ((centralCompactColumn hscale hg hc hp : CentralRadialHilbert scale) : ℝ → ℝ)
      =ᵐ[centralRadialSpectralMeasure scale] centralCompactColumnFunction scale g :=
  (centralCompactColumnFunction_memLp hscale hg hc hp).coeFn_toLp

theorem centralCompactColumn_density {scale : ℝ} (hscale : 0 < scale)
    (g : ℝ → ℝ) (x : ℝ) :
    centralRadialPullbackDensity scale x *
      centralCompactColumnFunction scale g (centralRadius x) =
        deriv centralRadius x * g (centralRadius x) := by
  rw [← centralRadialVarpi_pullback_density, centralCompactColumnFunction]
  field_simp [(centralRadialVarpi_pos hscale (centralRadius_pos x)).ne']

theorem centralCompactColumn_row_integrable {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0) (u : CentralRadialHilbert scale) :
    IntegrableOn (fun r => g r * u r) (Ioi 0) := by
  rw [centralRadius_integrable_iff]
  have h := (centralRadialSpectral_integrable_iff hscale _).mp
    ((centralCompactColumnFunction_memLp hscale hg hc hp).integrable_mul (Lp.memLp u))
  convert h using 1
  funext x
  simpa only [Pi.mul_apply, mul_assoc] using congrArg (fun q : ℝ => q * u (centralRadius x))
    (centralCompactColumn_density hscale g x).symm

/-- The actual Hilbert pairing is precisely the row in ordinary `dr`. -/
theorem centralCompactColumn_row_pairing {scale : ℝ} (hscale : 0 < scale)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hp : tsupport g ⊆ Ioi 0) (u : CentralRadialHilbert scale) :
    ⟪centralCompactColumn hscale hg hc hp, u⟫_ℝ =
      ∫ r in Ioi 0, g r * u r := by
  have hi : ⟪centralCompactColumn hscale hg hc hp, u⟫_ℝ =
      ∫ r, centralCompactColumn hscale hg hc hp r * u r ∂centralRadialSpectralMeasure scale := by
    rw [L2.inner_def]
    congr 1
    funext r
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  rw [hi]
  have ha : (fun r => centralCompactColumn hscale hg hc hp r * u r)
      =ᵐ[centralRadialSpectralMeasure scale]
        (fun r => centralCompactColumnFunction scale g r * u r) := by
    filter_upwards [centralCompactColumn_ae hscale hg hc hp] with r hr
    rw [hr]
  rw [integral_congr_ae ha, centralRadialSpectral_integral_change hscale,
    centralRadius_integral_change]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    simpa only [mul_assoc] using congrArg (fun q : ℝ => q * u (centralRadius x))
      (centralCompactColumn_density hscale g x))

end ContinuousFlexibility.Radial
