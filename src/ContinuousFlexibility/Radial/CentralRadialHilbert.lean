module

public import ContinuousFlexibility.Radial.CentralRadialMeasure
public import ContinuousFlexibility.Radial.CentralModel
public import ContinuousFlexibility.Radial.HermiteBasis

/-!
# Quotient-safe central radial Hilbert transform

The normalized transform is `sqrt (12*c) * s * nu * u(R)`. The positive
Jacobian and density prove that it is independent of representatives, and
the inverse is constructed on actual `Lp` classes. Smooth forcing identities
retain the factor `1/12`. An oscillator reduced inverse is not declared to
be the radial orthogonal reduced inverse: their kernel normalizations differ.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace

set_option backward.isDefEq.respectTransparency false

abbrev CentralRadialHilbert (c : ℝ) := Lp ℝ 2 (centralRadialSpectralMeasure c)

def centralRadialAmplitude (c x : ℝ) : ℝ :=
  Real.sqrt (12 * c) * (centralDensityRoot x * centralRadiusLogDerivative x)

theorem continuous_centralRadialAmplitude (c : ℝ) :
    Continuous (centralRadialAmplitude c) :=
  continuous_const.mul
    (contDiff_centralDensityRoot.continuous.mul contDiff_centralRadiusLogDerivative.continuous)

theorem centralRadialAmplitude_pos {c : ℝ} (hc : 0 < c) (x : ℝ) :
    0 < centralRadialAmplitude c x :=
  mul_pos (Real.sqrt_pos.mpr (mul_pos (by norm_num) hc))
    (mul_pos (centralDensityRoot_pos x) (centralRadiusLogDerivative_pos x))

theorem centralRadialAmplitude_sq {c : ℝ} (hc : 0 < c) (x : ℝ) :
    centralRadialAmplitude c x ^ 2 = centralRadialPullbackDensity c x := by
  unfold centralRadialAmplitude centralRadialPullbackDensity
  rw [mul_pow, Real.sq_sqrt (by positivity)]

private theorem centralPullback_ac {c : ℝ} (hc : 0 < c) :
    volume ≪ volume.withDensity
      (fun x => ENNReal.ofReal (centralRadialPullbackDensity c x)) := by
  apply withDensity_absolutelyContinuous'
    (continuous_centralRadialPullbackDensity c).measurable.ennreal_ofReal.aemeasurable
  exact Eventually.of_forall (fun x => ne_of_gt
    (ENNReal.ofReal_pos.mpr (centralRadialPullbackDensity_pos hc x)))

/-- A physical radial a.e. identity remains a.e. after the actual radius pullback. -/
theorem centralRadial_pullback_ae {c : ℝ} (hc : 0 < c) {f g : ℝ → ℝ}
    (hfg : f =ᵐ[centralRadialSpectralMeasure c] g) :
    (fun x => f (centralRadius x)) =ᵐ[volume] (fun x => g (centralRadius x)) := by
  apply (centralPullback_ac hc).ae_eq
  exact ae_eq_comp contDiff_centralRadius.continuous.measurable.aemeasurable
    (by simpa only [centralRadialSpectralMeasure_map] using hfg)

/-- The positive square-density multiplier changes the measure, not the space
by an unjustified bounded multiplier. -/
theorem centralRadialPullback_memLp_iff {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ) :
    MemLp f 2 (volume.withDensity
      (fun x => ENNReal.ofReal (centralRadialPullbackDensity c x))) ↔
      MemLp (fun x => centralRadialAmplitude c x * f x) 2 volume := by
  have hd := (continuous_centralRadialPullbackDensity c).measurable.ennreal_ofReal
  have ha : AEStronglyMeasurable (centralRadialAmplitude c) volume :=
    (continuous_centralRadialAmplitude c).aestronglyMeasurable
  have hi : Continuous (fun x => (centralRadialAmplitude c x)⁻¹) :=
    (continuous_centralRadialAmplitude c).inv₀ (fun x => (centralRadialAmplitude_pos hc x).ne')
  have hfinite : ∀ᵐ x ∂volume,
      ENNReal.ofReal (centralRadialPullbackDensity c x) < (∞ : ℝ≥0∞) := by simp
  constructor
  · intro hf
    have hfm := AEStronglyMeasurable.mono_ac (centralPullback_ac hc) hf.aestronglyMeasurable
    have hafm : AEStronglyMeasurable (fun x => centralRadialAmplitude c x * f x) volume :=
      ha.mul hfm
    apply (memLp_two_iff_integrable_sq hafm).mpr
    have h := (integrable_withDensity_iff_integrable_smul' hd hfinite).mp hf.integrable_sq
    convert h using 1
    funext x
    rw [ENNReal.toReal_ofReal (centralRadialPullbackDensity_pos hc x).le,
      ← centralRadialAmplitude_sq hc]
    simp only [smul_eq_mul]
    ring
  · intro hf
    have hfm : AEStronglyMeasurable f volume := by
      have h := hi.aestronglyMeasurable.mul hf.aestronglyMeasurable
      convert h using 1
      funext x
      exact (inv_mul_cancel_left₀ (centralRadialAmplitude_pos hc x).ne' (f x)).symm
    have hfd : AEStronglyMeasurable f (volume.withDensity
        (fun x => ENNReal.ofReal (centralRadialPullbackDensity c x))) :=
      AEStronglyMeasurable.mono_ac (withDensity_absolutelyContinuous volume
        (fun x => ENNReal.ofReal (centralRadialPullbackDensity c x))) hfm
    apply (memLp_two_iff_integrable_sq hfd).mpr
    apply (integrable_withDensity_iff_integrable_smul' hd hfinite).mpr
    convert hf.integrable_sq using 1
    funext x
    rw [ENNReal.toReal_ofReal (centralRadialPullbackDensity_pos hc x).le,
      ← centralRadialAmplitude_sq hc]
    simp only [smul_eq_mul]
    ring

theorem centralRadial_memLp_iff {c : ℝ} (hc : 0 < c) (u : ℝ → ℝ) :
    MemLp u 2 (centralRadialSpectralMeasure c) ↔
      MemLp (fun x => centralRadialAmplitude c x * u (centralRadius x)) 2 volume := by
  rw [← centralRadialSpectralMeasure_map,
    measurableEmbedding_centralRadius.memLp_map_measure_iff]
  exact centralRadialPullback_memLp_iff hc _

private theorem radialL2_norm_sq {μ : Measure ℝ} (f : Lp ℝ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext x
  simp only [RCLike.inner_apply, conj_trivial]
  ring

private theorem radialToLp_norm_sq {μ : Measure ℝ} {f : ℝ → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [radialL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

private def centralRadialTransform {c : ℝ} (hc : 0 < c) :
    CentralRadialHilbert c →ₗᵢ[ℝ] HermiteL2 where
  toFun u := ((centralRadial_memLp_iff hc u).mp (Lp.memLp u)).toLp _
  map_add' u v := by
    apply Lp.ext
    filter_upwards
      [((centralRadial_memLp_iff hc
          ((u + v : CentralRadialHilbert c) : ℝ → ℝ)).mp (Lp.memLp (u + v))).coeFn_toLp,
        ((centralRadial_memLp_iff hc u).mp (Lp.memLp u)).coeFn_toLp,
        ((centralRadial_memLp_iff hc v).mp (Lp.memLp v)).coeFn_toLp,
        Lp.coeFn_add
          (((centralRadial_memLp_iff hc u).mp (Lp.memLp u)).toLp _)
          (((centralRadial_memLp_iff hc v).mp (Lp.memLp v)).toLp _),
        centralRadial_pullback_ae hc (Lp.coeFn_add u v)] with x hx hu hv hs ha
    simp only [Pi.add_apply] at hs ha
    rw [hx, hs, hu, hv, ha]
    ring
  map_smul' a u := by
    apply Lp.ext
    filter_upwards
      [((centralRadial_memLp_iff hc
          ((a • u : CentralRadialHilbert c) : ℝ → ℝ)).mp (Lp.memLp (a • u))).coeFn_toLp,
        ((centralRadial_memLp_iff hc u).mp (Lp.memLp u)).coeFn_toLp,
        Lp.coeFn_smul a (((centralRadial_memLp_iff hc u).mp (Lp.memLp u)).toLp _),
        centralRadial_pullback_ae hc (Lp.coeFn_smul a u)] with x hx hu hs ha
    simp only [Pi.smul_apply, smul_eq_mul] at hs ha
    simp only [RingHom.id_apply]
    rw [hx, hs, hu, ha]
    ring
  norm_map' u := by
    change ‖((centralRadial_memLp_iff hc u).mp (Lp.memLp u)).toLp _‖ = ‖u‖
    have ht := radialToLp_norm_sq ((centralRadial_memLp_iff hc u).mp (Lp.memLp u))
    have hu := radialL2_norm_sq u
    rw [centralRadialSpectral_integral_change hc] at hu
    have hi : (∫ x, (centralRadialAmplitude c x * u (centralRadius x)) ^ 2) =
        ∫ x, centralRadialPullbackDensity c x * u (centralRadius x) ^ 2 := by
      congr 1
      funext x
      rw [mul_pow, centralRadialAmplitude_sq hc]
    rw [hi] at ht
    nlinarith [norm_nonneg u,
      norm_nonneg (((centralRadial_memLp_iff hc u).mp (Lp.memLp u)).toLp _)]

private theorem centralRadialTransform_ae {c : ℝ} (hc : 0 < c)
    (u : CentralRadialHilbert c) :
    centralRadialTransform hc u =ᵐ[volume]
      (fun x => centralRadialAmplitude c x * u (centralRadius x)) :=
  ((centralRadial_memLp_iff hc u).mp (Lp.memLp u)).coeFn_toLp

private theorem centralRadialTransform_surjective {c : ℝ} (hc : 0 < c) :
    Function.Surjective (centralRadialTransform hc) := by
  intro f
  let hm := (Lp.memLp f).aestronglyMeasurable
  let f0 := hm.mk f
  have hf0 : MemLp f0 2 volume := MemLp.ae_eq hm.ae_eq_mk (Lp.memLp f)
  let X := measurableEmbedding_centralRadius.invFun
  have hXR : ∀ x, X (centralRadius x) = x :=
    measurableEmbedding_centralRadius.leftInverse_invFun
  let u : ℝ → ℝ := fun r => f0 (X r) / centralRadialAmplitude c (X r)
  have hu : MemLp u 2 (centralRadialSpectralMeasure c) := by
    rw [centralRadial_memLp_iff hc]
    convert hf0 using 1
    funext x
    dsimp [u]
    rw [hXR]
    field_simp [(centralRadialAmplitude_pos hc x).ne']
  refine ⟨hu.toLp u, ?_⟩
  apply Lp.ext
  filter_upwards [centralRadialTransform_ae hc (hu.toLp u),
    centralRadial_pullback_ae hc hu.coeFn_toLp, hm.ae_eq_mk] with x hx hu hf
  rw [hx, hu]
  dsimp [u]
  rw [hXR]
  change f x = f0 x at hf
  rw [← hf]
  field_simp [(centralRadialAmplitude_pos hc x).ne']

/-- The actual normalized Hilbert equivalence, including both directions on
`Lp` equivalence classes. -/
def centralRadialHilbertEquiv {c : ℝ} (hc : 0 < c) :
    CentralRadialHilbert c ≃ₗᵢ[ℝ] HermiteL2 :=
  LinearIsometryEquiv.ofSurjective (centralRadialTransform hc)
    (centralRadialTransform_surjective hc)

theorem centralRadialHilbertEquiv_ae {c : ℝ} (hc : 0 < c)
    (u : CentralRadialHilbert c) :
    centralRadialHilbertEquiv hc u =ᵐ[volume]
      (fun x => centralRadialAmplitude c x * u (centralRadius x)) :=
  centralRadialTransform_ae hc u

theorem centralRadialHilbertEquiv_symm_pullback_ae {c : ℝ} (hc : 0 < c)
    (f : HermiteL2) :
    (fun x => (centralRadialHilbertEquiv hc).symm f (centralRadius x)) =ᵐ[volume]
      (fun x => f x / centralRadialAmplitude c x) := by
  have h := centralRadialHilbertEquiv_ae hc ((centralRadialHilbertEquiv hc).symm f)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  filter_upwards [h] with x hx
  apply (eq_div_iff (centralRadialAmplitude_pos hc x).ne').mpr
  nlinarith [hx]

def centralRadialHeight (ψ : ℝ → ℝ) (r : ℝ) : ℝ :=
  ψ (centralModelCoordinate r) / centralDensityRoot (centralModelCoordinate r)

theorem centralRadialHeight_pullback (ψ : ℝ → ℝ) (x : ℝ) :
    centralRadialHeight ψ (centralRadius x) = ψ x / centralDensityRoot x := by
  simp only [centralRadialHeight, centralModelCoordinate_radius]

theorem centralRadialHeight_memLp {c : ℝ} (hc : 0 < c) {ψ : ℝ → ℝ}
    (hψ : MemLp (fun x => centralRadiusLogDerivative x * ψ x) 2 volume) :
    MemLp (centralRadialHeight ψ) 2 (centralRadialSpectralMeasure c) := by
  rw [centralRadial_memLp_iff hc]
  convert hψ.const_mul (Real.sqrt (12 * c)) using 1
  funext x
  rw [centralRadialHeight_pullback]
  unfold centralRadialAmplitude
  field_simp [(centralDensityRoot_pos x).ne']

/-- Actual height transport. In particular the oscillator ground is sent to
`sqrt (12*c) * nu * ground`, not to the unweighted oscillator ground. -/
theorem centralRadialHilbertEquiv_height {c : ℝ} (hc : 0 < c) {ψ : ℝ → ℝ}
    (hψ : MemLp (fun x => centralRadiusLogDerivative x * ψ x) 2 volume) :
    centralRadialHilbertEquiv hc
        ((centralRadialHeight_memLp hc hψ).toLp (centralRadialHeight ψ)) =
      Real.sqrt (12 * c) • hψ.toLp (fun x => centralRadiusLogDerivative x * ψ x) := by
  apply Lp.ext
  filter_upwards
    [centralRadialHilbertEquiv_ae hc ((centralRadialHeight_memLp hc hψ).toLp _),
      centralRadial_pullback_ae hc (centralRadialHeight_memLp hc hψ).coeFn_toLp,
      Lp.coeFn_smul (Real.sqrt (12 * c))
        (hψ.toLp (fun x => centralRadiusLogDerivative x * ψ x)), hψ.coeFn_toLp]
    with x hx hu hs hψx
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hx, hu, centralRadialHeight_pullback, hs, hψx]
  unfold centralRadialAmplitude
  field_simp [(centralDensityRoot_pos x).ne']

theorem centralRadialHeight_norm_sq {c : ℝ} (hc : 0 < c) {ψ : ℝ → ℝ}
    (hψ : MemLp (fun x => centralRadiusLogDerivative x * ψ x) 2 volume) :
    ‖(centralRadialHeight_memLp hc hψ).toLp (centralRadialHeight ψ)‖ ^ 2 =
      12 * c * ‖hψ.toLp (fun x => centralRadiusLogDerivative x * ψ x)‖ ^ 2 := by
  have h := congrArg (fun f : HermiteL2 => ‖f‖ ^ 2)
    (centralRadialHilbertEquiv_height hc hψ)
  have hsqrt : Real.sqrt (12 * c) ^ 2 = 12 * c :=
    Real.sq_sqrt (mul_pos (by norm_num) hc).le
  simpa only [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, hsqrt] using h

theorem contDiffAt_centralRadialHeight {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (x : ℝ) :
    ContDiffAt ℝ ∞ (centralRadialHeight ψ) (centralRadius x) := by
  have hX := contDiffAt_centralModelCoordinate x
  exact (hψ.contDiffAt.comp _ hX).div
    (contDiff_centralDensityRoot.contDiffAt.comp _ hX)
    (by simpa only [centralModelCoordinate_radius] using (centralDensityRoot_pos x).ne')

/-- The arbitrary smooth height satisfies the actual radial differential
identity for the constructed profile and radius. -/
theorem radialJacobi_centralRadialHeight {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (j c x : ℝ) :
    radialJacobi (j ^ 2) (centralRadialProfile c) (centralRadialHeight ψ) (centralRadius x) =
      -(c * centralDensityRoot x / deriv centralRadius x) *
        liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot ψ x := by
  have hR := contDiff_centralRadius.differentiable (by simp)
  have hs := contDiff_centralDensityRoot.differentiable (by simp)
  have hR₂ := (contDiff_infty_iff_deriv.mp contDiff_centralRadius).2.differentiable (by simp) x
  have hs₂ := (contDiff_infty_iff_deriv.mp contDiff_centralDensityRoot).2.differentiable (by simp) x
  have hψ₂ := (contDiff_infty_iff_deriv.mp hψ).2.differentiable (by simp) x
  have hw := contDiffAt_centralRadialProfile c x
  have hu := contDiffAt_centralRadialHeight hψ x
  have hflux : DifferentiableAt ℝ
      (fun r => centralRadialProfile c r * deriv (centralRadialHeight ψ) r) (centralRadius x) :=
    (hw.mul (hu.derivWithin (m := ∞) (by simp))).differentiableAt (by simp)
  exact radialJacobi_liouville (Eventually.of_forall hR) (Eventually.of_forall hs)
    (Eventually.of_forall (hψ.differentiable (by simp)))
    (Eventually.of_forall (fun t =>
      (contDiffAt_centralRadialHeight hψ t).differentiableAt (by simp)))
    hR₂ hs₂ hψ₂ (hw.differentiableAt (by simp)) hflux
    (centralRadius_pos x).ne' (deriv_centralRadius_pos x).ne' (centralDensityRoot_pos x).ne'
    (Eventually.of_forall (centralRadialProfile_pullback c))
    (Eventually.of_forall (centralRadialHeight_pullback ψ))

theorem centralRadial_ordinary_forcing_iff {c : ℝ} (hc : c ≠ 0)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (j x : ℝ) (f : ℝ → ℝ) :
    radialJacobi (j ^ 2) (centralRadialProfile c) (centralRadialHeight ψ) (centralRadius x) =
        f (centralRadius x) ↔
      liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot ψ x =
        liouvilleSource c centralRadius centralDensityRoot f x :=
  liouville_forcing_iff hc (centralDensityRoot_pos x).ne' (deriv_centralRadius_pos x).ne'
    (radialJacobi_centralRadialHeight hψ j c x)

/-- The physical differential expression `B_j = -varpi⁻¹ L_j`. This definition
does not assert a closed operator domain. -/
def centralRadialSpectralExpression (j c : ℝ) (u : ℝ → ℝ) (r : ℝ) : ℝ :=
  -(centralRadialVarpi c r)⁻¹ * radialJacobi (j ^ 2) (centralRadialProfile c) u r

theorem centralRadialSpectralExpression_height {c : ℝ} (hc : 0 < c)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (j x : ℝ) :
    centralRadialSpectralExpression j c (centralRadialHeight ψ) (centralRadius x) =
      liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot ψ x /
        (12 * centralDensityRoot x * centralRadiusLogDerivative x ^ 2) := by
  unfold centralRadialSpectralExpression
  rw [radialJacobi_centralRadialHeight hψ]
  unfold centralRadialVarpi centralRadiusLogDerivative
  rw [centralRadialProfile_pullback]
  field_simp [hc.ne', (centralDensityRoot_pos x).ne', (centralRadius_pos x).ne',
    (deriv_centralRadius_pos x).ne']

theorem centralRadial_spectral_forcing_iff {c : ℝ} (hc : 0 < c)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (j x : ℝ) (F : ℝ → ℝ) :
    centralRadialSpectralExpression j c (centralRadialHeight ψ) (centralRadius x) =
        F (centralRadius x) ↔
      liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot ψ x =
        12 * centralDensityRoot x * centralRadiusLogDerivative x ^ 2 * F (centralRadius x) := by
  rw [centralRadialSpectralExpression_height hc hψ]
  rw [div_eq_iff (mul_ne_zero (mul_ne_zero (by norm_num) (centralDensityRoot_pos x).ne')
    (pow_ne_zero 2 (centralRadiusLogDerivative_pos x).ne'))]
  constructor <;> intro h <;> nlinarith [h]

/-- The normalized differential transform retains the factor `1/12`. -/
theorem centralRadialSpectralExpression_normalized {c : ℝ} (hc : 0 < c)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (j x : ℝ) :
    centralRadialAmplitude c x *
        centralRadialSpectralExpression j c (centralRadialHeight ψ) (centralRadius x) =
      (1 / 12 : ℝ) * (centralRadiusLogDerivative x)⁻¹ * Real.sqrt (12 * c) *
        liouvilleSchrodinger (j ^ 2) centralRadius centralDensityRoot ψ x := by
  rw [centralRadialSpectralExpression_height hc hψ]
  unfold centralRadialAmplitude
  field_simp [(centralDensityRoot_pos x).ne', (centralRadiusLogDerivative_pos x).ne']

/-- The actual growth theorem supplies weighted L² membership for every
physical oscillator energy vector. -/
theorem memLp_centralRadialWeight {ψ : ℝ → ℝ} (hψ : MemLp ψ 2 volume)
    (hxψ : MemLp (fun x : ℝ => x * ψ x) 2 volume) :
    MemLp (fun x => centralRadiusLogDerivative x * ψ x) 2 volume := by
  have hm := contDiff_centralRadiusLogDerivative.continuous.aestronglyMeasurable.mul
    hψ.aestronglyMeasurable
  apply (hψ.norm.add hxψ.norm).of_le_mul hm (c := centralRadiusWeightConstant)
  filter_upwards with x
  calc
    ‖centralRadiusLogDerivative x * ψ x‖ =
        ‖centralRadiusLogDerivative x‖ * ‖ψ x‖ := norm_mul _ _
    _ ≤ centralRadiusWeightConstant * (1 + |x|) * ‖ψ x‖ :=
      mul_le_mul_of_nonneg_right (centralRadiusLogDerivative_norm_le_linear x) (norm_nonneg _)
    _ = centralRadiusWeightConstant * ‖(fun x => ‖ψ x‖ + ‖x * ψ x‖) x‖ := by
      rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg (ψ x)) (norm_nonneg (x * ψ x)))]
      simp only [norm_mul, Real.norm_eq_abs]
      ring

theorem memLp_centralRadialWeightedGround :
    MemLp (fun x => centralRadiusLogDerivative x * centralOscillatorGround x) 2 volume := by
  apply memLp_centralRadialWeight
  · simpa only [oscillatorGround_two] using (memLp_oscillatorGround (j := 2) (by norm_num))
  · simpa only [oscillatorGround_two] using (memLp_mul_oscillatorGround (j := 2) (by norm_num))

theorem centralRadialHeight_ground_eq :
    centralRadialHeight centralOscillatorGround = centralKernelHeight := by
  funext r
  unfold centralRadialHeight centralOscillatorGround centralDensityRoot centralKernelHeight
  rw [← Real.exp_sub]
  congr 1
  ring

theorem memLp_centralKernelHeight {c : ℝ} (hc : 0 < c) :
    MemLp centralKernelHeight 2 (centralRadialSpectralMeasure c) := by
  rw [← centralRadialHeight_ground_eq]
  exact centralRadialHeight_memLp hc memLp_centralRadialWeightedGround

/-- The actual radial zero mode has the weighted ground as its Hilbert image.
This is the kernel direction that a radial orthogonal reduction must use. -/
theorem centralRadialHilbertEquiv_kernel {c : ℝ} (hc : 0 < c) :
    centralRadialHilbertEquiv hc ((memLp_centralKernelHeight hc).toLp centralKernelHeight) =
      Real.sqrt (12 * c) • memLp_centralRadialWeightedGround.toLp
        (fun x => centralRadiusLogDerivative x * centralOscillatorGround x) := by
  simpa only [centralRadialHeight_ground_eq] using
    centralRadialHilbertEquiv_height hc memLp_centralRadialWeightedGround

end ContinuousFlexibility.Radial
