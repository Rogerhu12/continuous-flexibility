import ContinuousFlexibility.Radial.CentralRadialWeakTransport
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# A genuine compact auxiliary border for the central second mode

The compact column and its row use ordinary radial measure. Their actual
weighted-Hilbert representatives have fixed images under every positive
height scaling. This is the auxiliary border, not the later column obtained
by differentiating the final metric.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false

def centralAuxiliaryBump : ContDiffBump (1 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

def centralAuxiliaryDensity : ℝ → ℝ := centralAuxiliaryBump.normed volume

theorem contDiff_centralAuxiliaryDensity : ContDiff ℝ ∞ centralAuxiliaryDensity :=
  centralAuxiliaryBump.contDiff_normed

theorem centralAuxiliaryDensity_hasCompactSupport : HasCompactSupport centralAuxiliaryDensity :=
  centralAuxiliaryBump.hasCompactSupport_normed

theorem centralAuxiliaryDensity_tsupport_positive : tsupport centralAuxiliaryDensity ⊆ Ioi 0 := by
  change tsupport (centralAuxiliaryBump.normed volume) ⊆ Ioi (0 : ℝ)
  rw [centralAuxiliaryBump.tsupport_normed_eq]
  intro r hr
  rw [Real.closedBall_eq_Icc] at hr
  change 1 - (1 / 2 : ℝ) ≤ r ∧ r ≤ 1 + (1 / 2 : ℝ) at hr
  change 0 < r
  linarith only [hr.1]

/-- The actual compact radial function, normalized in ordinary `dr`. -/
def centralAuxiliaryFunction (r : ℝ) : ℝ :=
  centralAuxiliaryDensity r / centralKernelHeight r

theorem centralAuxiliaryFunction_nonneg (r : ℝ) : 0 ≤ centralAuxiliaryFunction r :=
  div_nonneg (centralAuxiliaryBump.nonneg_normed r) (centralKernelHeight_pos r).le

theorem centralAuxiliaryFunction_tsupport_subset :
    tsupport centralAuxiliaryFunction ⊆ tsupport centralAuxiliaryDensity := by
  apply closure_mono
  intro r hr
  change centralAuxiliaryFunction r ≠ 0 at hr
  change centralAuxiliaryDensity r ≠ 0
  intro hz
  exact hr (by rw [centralAuxiliaryFunction, hz, zero_div])

theorem centralAuxiliaryFunction_tsupport_positive : tsupport centralAuxiliaryFunction ⊆ Ioi 0 :=
  centralAuxiliaryFunction_tsupport_subset.trans centralAuxiliaryDensity_tsupport_positive

theorem centralAuxiliaryFunction_hasCompactSupport : HasCompactSupport centralAuxiliaryFunction :=
  centralAuxiliaryDensity_hasCompactSupport.of_isClosed_subset
    (isClosed_tsupport _) centralAuxiliaryFunction_tsupport_subset

theorem contDiff_centralAuxiliaryFunction : ContDiff ℝ ∞ centralAuxiliaryFunction := by
  apply contDiff_iff_contDiffAt.mpr
  intro r
  by_cases hr : 0 < r
  · have hφ := contDiffAt_centralKernelHeight (centralModelCoordinate r)
    rw [centralRadius_modelCoordinate hr] at hφ
    exact contDiff_centralAuxiliaryDensity.contDiffAt.div hφ (centralKernelHeight_pos r).ne'
  · have hn : r ∉ tsupport centralAuxiliaryFunction :=
      fun h => hr (centralAuxiliaryFunction_tsupport_positive h)
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) r).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hn)

theorem centralAuxiliaryFunction_mul_kernel (r : ℝ) :
    centralAuxiliaryFunction r * centralKernelHeight r = centralAuxiliaryDensity r :=
  div_mul_cancel₀ _ (centralKernelHeight_pos r).ne'

theorem centralAuxiliaryFunction_pairing :
    (∫ r : ℝ, centralAuxiliaryFunction r * centralKernelHeight r) = 1 := by
  have heq : (fun r : ℝ => centralAuxiliaryFunction r * centralKernelHeight r) =
      centralAuxiliaryDensity := funext centralAuxiliaryFunction_mul_kernel
  rw [heq]
  exact centralAuxiliaryBump.integral_normed

theorem centralAuxiliaryFunction_pairing_positive :
    (∫ r in Ioi (0 : ℝ), centralAuxiliaryFunction r * centralKernelHeight r) = 1 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun r hr => by
    have hz : r ∉ tsupport centralAuxiliaryFunction :=
      fun h => hr (centralAuxiliaryFunction_tsupport_positive h)
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul])]
  exact centralAuxiliaryFunction_pairing

def centralAuxiliarySourceFunction (x : ℝ) : ℝ :=
  centralRadius x / (sqrt 12 * centralDensityRoot x ^ 2) *
    centralRadialTestPullback centralAuxiliaryFunction x

theorem centralAuxiliarySourceFunction_apply (x : ℝ) :
    centralAuxiliarySourceFunction x =
      centralRadius x / (sqrt 12 * centralDensityRoot x) *
        centralAuxiliaryFunction (centralRadius x) := by
  unfold centralAuxiliarySourceFunction centralRadialTestPullback
  field_simp [(centralDensityRoot_pos x).ne']

theorem contDiff_centralAuxiliarySourceFunction : ContDiff ℝ ∞ centralAuxiliarySourceFunction :=
  (contDiff_centralRadius.div (contDiff_const.mul (contDiff_centralDensityRoot.pow 2))
    (fun x => mul_ne_zero (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 12)).ne'
      (pow_ne_zero 2 (centralDensityRoot_pos x).ne'))).mul
    (contDiff_centralRadialTestPullback contDiff_centralAuxiliaryFunction)

theorem centralAuxiliarySourceFunction_hasCompactSupport :
    HasCompactSupport centralAuxiliarySourceFunction :=
  (centralRadialTestPullback_hasCompactSupport centralAuxiliaryFunction_hasCompactSupport
    centralAuxiliaryFunction_tsupport_positive).mul_left

theorem centralAuxiliarySourceFunction_memLp : MemLp centralAuxiliarySourceFunction 2 volume :=
  contDiff_centralAuxiliarySourceFunction.continuous.memLp_of_hasCompactSupport
    centralAuxiliarySourceFunction_hasCompactSupport

def centralAuxiliarySourceVector : HermiteL2 :=
  centralAuxiliarySourceFunction_memLp.toLp centralAuxiliarySourceFunction

theorem centralAuxiliarySourceVector_ae :
    (centralAuxiliarySourceVector : ℝ → ℝ) =ᵐ[volume] centralAuxiliarySourceFunction :=
  centralAuxiliarySourceFunction_memLp.coeFn_toLp

/-- The positive Riesz column; the operator `B=-varpi⁻¹ L` uses its
negative as the column corresponding to `L u + c g = f`. -/
def centralAuxiliaryColumnFunction (scale r : ℝ) : ℝ :=
  sqrt scale * centralAuxiliaryFunction r / centralRadialVarpi scale r

private theorem auxiliary_sqrt_scale {scale : ℝ} (hscale : 0 < scale) :
    sqrt (12 * scale) * sqrt scale / (12 * scale) = (sqrt 12)⁻¹ := by
  have h12 : sqrt (12 : ℝ) ^ 2 = 12 := sq_sqrt (by norm_num)
  have hp : sqrt (12 * scale) * sqrt scale = sqrt 12 * scale := by
    rw [sqrt_mul (by norm_num : (0 : ℝ) ≤ 12)]
    calc
      (sqrt 12 * sqrt scale) * sqrt scale = sqrt 12 * (sqrt scale) ^ 2 := by ring
      _ = _ := by rw [sq_sqrt hscale.le]
  rw [hp]
  calc
    (sqrt 12 * scale) / (12 * scale) = sqrt 12 / 12 := by field_simp [hscale.ne']
    _ = _ := by
      apply mul_left_cancel₀ (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 12)).ne'
      calc
        sqrt 12 * (sqrt 12 / 12) = (sqrt 12) ^ 2 / 12 := by ring
        _ = 1 := by rw [h12]; norm_num
        _ = sqrt 12 * (sqrt 12)⁻¹ :=
          (mul_inv_cancel₀ (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 12)).ne').symm

theorem centralAuxiliaryColumnFunction_transform {scale : ℝ} (hscale : 0 < scale) (x : ℝ) :
    centralRadialAmplitude scale x * centralAuxiliaryColumnFunction scale (centralRadius x) =
      centralAuxiliarySourceFunction x := by
  rw [centralAuxiliarySourceFunction_apply]
  calc
    _ = (sqrt (12 * scale) * sqrt scale / (12 * scale)) *
        (centralRadius x / centralDensityRoot x) * centralAuxiliaryFunction (centralRadius x) := by
      unfold centralRadialAmplitude centralAuxiliaryColumnFunction centralRadialVarpi
      rw [centralRadialProfile_pullback]
      unfold centralRadiusLogDerivative
      field_simp [hscale.ne', (centralRadius_pos x).ne', (centralDensityRoot_pos x).ne',
        (deriv_centralRadius_pos x).ne']
    _ = _ := by rw [auxiliary_sqrt_scale hscale]; ring

theorem centralAuxiliaryColumnFunction_memLp {scale : ℝ} (hscale : 0 < scale) :
    MemLp (centralAuxiliaryColumnFunction scale) 2 (centralRadialSpectralMeasure scale) := by
  rw [centralRadial_memLp_iff hscale]
  have heq : (fun x => centralRadialAmplitude scale x *
      centralAuxiliaryColumnFunction scale (centralRadius x)) = centralAuxiliarySourceFunction :=
    funext (centralAuxiliaryColumnFunction_transform hscale)
  rw [heq]
  exact centralAuxiliarySourceFunction_memLp

def centralAuxiliaryColumn {scale : ℝ} (hscale : 0 < scale) : CentralRadialHilbert scale :=
  (centralAuxiliaryColumnFunction_memLp hscale).toLp (centralAuxiliaryColumnFunction scale)

theorem centralAuxiliaryColumn_transform {scale : ℝ} (hscale : 0 < scale) :
    centralRadialHilbertEquiv hscale (centralAuxiliaryColumn hscale) = centralAuxiliarySourceVector := by
  apply Lp.ext
  filter_upwards [centralRadialHilbertEquiv_ae hscale (centralAuxiliaryColumn hscale),
    centralRadial_pullback_ae hscale (centralAuxiliaryColumnFunction_memLp hscale).coeFn_toLp,
    centralAuxiliarySourceVector_ae] with x ht hc hs
  change centralAuxiliaryColumn hscale (centralRadius x) =
    centralAuxiliaryColumnFunction scale (centralRadius x) at hc
  rw [ht, hc, centralAuxiliaryColumnFunction_transform hscale, hs]

theorem centralAuxiliaryColumn_norm {scale : ℝ} (hscale : 0 < scale) :
    ‖centralAuxiliaryColumn hscale‖ = ‖centralAuxiliarySourceVector‖ := by
  rw [← (centralRadialHilbertEquiv hscale).norm_map, centralAuxiliaryColumn_transform]

private theorem auxiliary_inner_integral {μ : Measure ℝ} (u v : Lp ℝ 2 μ) :
    ⟪u, v⟫_ℝ = ∫ r, u r * v r ∂μ := by
  rw [L2.inner_def]
  congr 1
  funext r
  simp only [RCLike.inner_apply, conj_trivial]
  ring

private theorem auxiliary_column_density {scale : ℝ} (hscale : 0 < scale) (x : ℝ) :
    centralRadialPullbackDensity scale x * centralAuxiliaryColumnFunction scale (centralRadius x) =
      deriv centralRadius x * (sqrt scale * centralAuxiliaryFunction (centralRadius x)) := by
  rw [← centralRadialVarpi_pullback_density]
  unfold centralAuxiliaryColumnFunction
  field_simp [(centralRadialVarpi_pos hscale (centralRadius_pos x)).ne']

theorem centralAuxiliaryRow_integrable {scale : ℝ} (hscale : 0 < scale) (u : CentralRadialHilbert scale) :
    IntegrableOn (fun r => sqrt scale * centralAuxiliaryFunction r * u r) (Ioi 0) := by
  rw [centralRadius_integrable_iff]
  have h := (centralRadialSpectral_integrable_iff hscale _).mp
    ((centralAuxiliaryColumnFunction_memLp hscale).integrable_mul (Lp.memLp u))
  convert h using 1
  funext x
  simpa only [Pi.mul_apply, mul_assoc] using congrArg (fun q : ℝ => q * u (centralRadius x))
    (auxiliary_column_density hscale x).symm

theorem centralAuxiliaryRow_pairing {scale : ℝ} (hscale : 0 < scale) (u : CentralRadialHilbert scale) :
    ⟪centralAuxiliaryColumn hscale, u⟫_ℝ =
      ∫ r in Ioi 0, sqrt scale * centralAuxiliaryFunction r * u r := by
  rw [auxiliary_inner_integral]
  have hc : (fun r => centralAuxiliaryColumn hscale r * u r) =ᵐ[centralRadialSpectralMeasure scale]
      (fun r => centralAuxiliaryColumnFunction scale r * u r) := by
    filter_upwards [(centralAuxiliaryColumnFunction_memLp hscale).coeFn_toLp] with r hr
    change centralAuxiliaryColumn hscale r = centralAuxiliaryColumnFunction scale r at hr
    rw [hr]
  rw [integral_congr_ae hc, centralRadialSpectral_integral_change hscale, centralRadius_integral_change]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    simpa only [mul_assoc] using congrArg (fun q : ℝ => q * u (centralRadius x))
      (auxiliary_column_density hscale x))

def centralAuxiliaryRow {scale : ℝ} (hscale : 0 < scale) : StrongDual ℝ (CentralRadialHilbert scale) :=
  innerSL ℝ (centralAuxiliaryColumn hscale)

theorem centralAuxiliaryRow_norm {scale : ℝ} (hscale : 0 < scale) :
    ‖centralAuxiliaryRow hscale‖ = ‖centralAuxiliarySourceVector‖ := by
  rw [centralAuxiliaryRow, innerSL_apply_norm, centralAuxiliaryColumn_norm]

theorem centralAuxiliaryRow_transport {scale : ℝ} (hscale : 0 < scale) (u : CentralRadialHilbert scale) :
    ⟪centralAuxiliarySourceVector, centralRadialHilbertEquiv hscale u⟫_ℝ =
      ∫ r in Ioi 0, sqrt scale * centralAuxiliaryFunction r * u r := by
  rw [← centralAuxiliaryColumn_transform hscale,
    (centralRadialHilbertEquiv hscale).inner_map_map, centralAuxiliaryRow_pairing]

/-- The Gaussian normalization is retained explicitly. -/
def centralAuxiliaryKernelScale : ℝ := sqrt 12 * oscillatorHermiteNorm 2 0

theorem centralAuxiliaryKernelScale_pos : 0 < centralAuxiliaryKernelScale :=
  mul_pos (sqrt_pos.mpr (by norm_num)) (oscillatorHermiteNorm_pos (by norm_num) 0)

def centralAuxiliaryKernelVector : HermiteL2 :=
  centralAuxiliaryKernelScale • centralRadialKernelVector

private theorem auxiliary_ground_normalization (x : ℝ) :
    oscillatorHermiteNorm 2 0 * normalizedOscillatorHermite 2 0 x = centralOscillatorGround x := by
  have hm : oscillatorHermiteMode 2 0 x = centralOscillatorGround x := by
    rw [oscillatorHermiteMode_eq]
    simp only [hermitePolynomial_zero, Polynomial.eval_one, one_mul]
    unfold centralOscillatorGround
    congr 1
    ring
  unfold normalizedOscillatorHermite
  rw [hm]
  field_simp [(oscillatorHermiteNorm_pos (by norm_num : (0 : ℝ) < 2) 0).ne']

theorem centralAuxiliaryKernelVector_ae :
    (centralAuxiliaryKernelVector : ℝ → ℝ) =ᵐ[volume]
      (fun x => sqrt 12 * centralRadiusLogDerivative x * centralOscillatorGround x) := by
  filter_upwards [Lp.coeFn_smul centralAuxiliaryKernelScale centralRadialKernelVector,
    centralRadialKernelVector_hasWeight, hermiteL2Vector_coeFn (by norm_num : (0 : ℝ) < 2) 0]
    with x hs hk he
  change centralRadialKernelVector x =
    centralRadiusLogDerivative x * centralRadialGroundVector x at hk
  change centralRadialGroundVector x = normalizedOscillatorHermite 2 0 x at he
  change (centralAuxiliaryKernelScale • centralRadialKernelVector) x = _
  rw [hs]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hk, he]
  unfold centralAuxiliaryKernelScale
  calc
    _ = sqrt 12 * centralRadiusLogDerivative x *
        (oscillatorHermiteNorm 2 0 * normalizedOscillatorHermite 2 0 x) := by ring
    _ = _ := by rw [auxiliary_ground_normalization]

theorem centralAuxiliaryKernelVector_graph :
    (centralAuxiliaryKernelVector, 0) ∈ centralRadialClosedGraph 2 := by
  have h := (centralRadialClosedGraph 2).smul_mem centralAuxiliaryKernelScale
    centralRadialKernelVector_graph
  simpa only [centralAuxiliaryKernelVector, Prod.smul_mk, smul_zero] using h

theorem centralAuxiliarySource_kernel_pairing :
    ⟪centralAuxiliarySourceVector, centralAuxiliaryKernelVector⟫_ℝ = 1 := by
  rw [auxiliary_inner_integral]
  have heq : (fun x => centralAuxiliarySourceVector x * centralAuxiliaryKernelVector x) =ᵐ[volume]
      (fun x => deriv centralRadius x *
        (centralAuxiliaryFunction (centralRadius x) * centralKernelHeight (centralRadius x))) := by
    filter_upwards [centralAuxiliarySourceVector_ae, centralAuxiliaryKernelVector_ae] with x hs hk
    rw [hs, hk, centralAuxiliarySourceFunction_apply, centralKernelHeight_liouville_pullback]
    unfold centralRadiusLogDerivative
    field_simp [(centralRadius_pos x).ne', (centralDensityRoot_pos x).ne',
      (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 12)).ne']
  rw [integral_congr_ae heq, ← centralRadius_integral_change
    (fun r => centralAuxiliaryFunction r * centralKernelHeight r)]
  exact centralAuxiliaryFunction_pairing_positive

def centralAuxiliaryKernelFunction (scale r : ℝ) : ℝ := centralKernelHeight r / sqrt scale

theorem centralAuxiliaryKernelFunction_memLp {scale : ℝ} (hscale : 0 < scale) :
    MemLp (centralAuxiliaryKernelFunction scale) 2 (centralRadialSpectralMeasure scale) := by
  change MemLp (fun r => centralKernelHeight r / sqrt scale) 2 (centralRadialSpectralMeasure scale)
  simpa only [div_eq_mul_inv] using
    (memLp_centralKernelHeight hscale).mul_const (sqrt scale)⁻¹

def centralAuxiliaryKernel {scale : ℝ} (hscale : 0 < scale) : CentralRadialHilbert scale :=
  (centralAuxiliaryKernelFunction_memLp hscale).toLp (centralAuxiliaryKernelFunction scale)

theorem centralAuxiliaryKernel_transform {scale : ℝ} (hscale : 0 < scale) :
    centralRadialHilbertEquiv hscale (centralAuxiliaryKernel hscale) = centralAuxiliaryKernelVector := by
  apply Lp.ext
  filter_upwards [centralRadialHilbertEquiv_ae hscale (centralAuxiliaryKernel hscale),
    centralRadial_pullback_ae hscale (centralAuxiliaryKernelFunction_memLp hscale).coeFn_toLp,
    centralAuxiliaryKernelVector_ae] with x ht hc hk
  change centralAuxiliaryKernel hscale (centralRadius x) =
    centralAuxiliaryKernelFunction scale (centralRadius x) at hc
  rw [ht, hc, hk]
  unfold centralAuxiliaryKernelFunction centralRadialAmplitude
  rw [centralKernelHeight_liouville_pullback, sqrt_mul (by norm_num : (0 : ℝ) ≤ 12)]
  field_simp [(sqrt_pos.mpr hscale).ne', (centralDensityRoot_pos x).ne']

theorem centralAuxiliaryKernel_norm {scale : ℝ} (hscale : 0 < scale) :
    ‖centralAuxiliaryKernel hscale‖ = ‖centralAuxiliaryKernelVector‖ := by
  rw [← (centralRadialHilbertEquiv hscale).norm_map, centralAuxiliaryKernel_transform]

theorem centralAuxiliary_scaled_pairing {scale : ℝ} (hscale : 0 < scale) :
    (∫ r in Ioi 0, (sqrt scale * centralAuxiliaryFunction r) * centralAuxiliaryKernelFunction scale r) = 1 := by
  have heq : (fun r => (sqrt scale * centralAuxiliaryFunction r) * centralAuxiliaryKernelFunction scale r) =
      (fun r => centralAuxiliaryFunction r * centralKernelHeight r) := by
    funext r
    unfold centralAuxiliaryKernelFunction
    field_simp [(sqrt_pos.mpr hscale).ne']
  rw [heq]
  exact centralAuxiliaryFunction_pairing_positive

theorem centralAuxiliaryRow_kernel {scale : ℝ} (hscale : 0 < scale) :
    centralAuxiliaryRow hscale (centralAuxiliaryKernel hscale) = 1 := by
  change ⟪centralAuxiliaryColumn hscale, centralAuxiliaryKernel hscale⟫_ℝ = 1
  calc
    _ = ⟪centralRadialHilbertEquiv hscale (centralAuxiliaryColumn hscale),
        centralRadialHilbertEquiv hscale (centralAuxiliaryKernel hscale)⟫_ℝ :=
      ((centralRadialHilbertEquiv hscale).inner_map_map _ _).symm
    _ = 1 := by rw [centralAuxiliaryColumn_transform, centralAuxiliaryKernel_transform,
      centralAuxiliarySource_kernel_pairing]

def centralAuxiliaryBorderColumn {scale : ℝ} (hscale : 0 < scale) : ℝ →L[ℝ] CentralRadialHilbert scale :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (-centralAuxiliaryColumn hscale)

theorem centralAuxiliaryBorderColumn_bound {scale : ℝ} (hscale : 0 < scale) (c : ℝ) :
    ‖centralAuxiliaryBorderColumn hscale c‖ = |c| * ‖centralAuxiliarySourceVector‖ := by
  change ‖c • (-centralAuxiliaryColumn hscale)‖ = _
  rw [norm_smul, norm_neg, centralAuxiliaryColumn_norm, Real.norm_eq_abs]

theorem centralAuxiliaryBorderColumn_pairing {scale : ℝ} (hscale : 0 < scale)
    (c : ℝ) (u : CentralRadialHilbert scale) :
    ⟪centralAuxiliaryBorderColumn hscale c, u⟫_ℝ = -c * centralAuxiliaryRow hscale u := by
  change ⟪c • (-centralAuxiliaryColumn hscale), u⟫_ℝ = -c * ⟪centralAuxiliaryColumn hscale, u⟫_ℝ
  rw [real_inner_smul_left, inner_neg_left]
  ring

def centralAuxiliaryCorrectedSource : HermiteL2 →L[ℝ] HermiteL2 :=
  ContinuousLinearMap.id ℝ HermiteL2 -
    (innerSL ℝ centralAuxiliaryKernelVector).smulRight centralAuxiliarySourceVector

theorem centralAuxiliaryCorrectedSource_apply (F : HermiteL2) :
    centralAuxiliaryCorrectedSource F =
      F - ⟪F, centralAuxiliaryKernelVector⟫_ℝ • centralAuxiliarySourceVector := by
  change F - ⟪centralAuxiliaryKernelVector, F⟫_ℝ • centralAuxiliarySourceVector = _
  rw [real_inner_comm centralAuxiliaryKernelVector F]

theorem centralAuxiliaryCorrectedSource_compat (F : HermiteL2) :
    ⟪centralAuxiliaryCorrectedSource F, centralRadialKernelVector⟫_ℝ = 0 := by
  have hK : ⟪centralAuxiliaryCorrectedSource F, centralAuxiliaryKernelVector⟫_ℝ = 0 := by
    rw [centralAuxiliaryCorrectedSource_apply, inner_sub_left, real_inner_smul_left,
      centralAuxiliarySource_kernel_pairing, mul_one, sub_self]
  rw [centralAuxiliaryKernelVector, real_inner_smul_right] at hK
  exact (mul_eq_zero.mp hK).resolve_left centralAuxiliaryKernelScale_pos.ne'

private theorem auxiliary_row_kernel_ne_zero :
    ⟪centralAuxiliarySourceVector, centralRadialKernelVector⟫_ℝ ≠ 0 := by
  intro hz
  have h := centralAuxiliarySource_kernel_pairing
  rw [centralAuxiliaryKernelVector, real_inner_smul_right, hz, mul_zero] at h
  norm_num at h

def centralAuxiliaryUnrowedInverse : HermiteL2 →L[ℝ] HermiteL2 :=
  centralRadialReducedHilbertInverse.comp centralAuxiliaryCorrectedSource

def centralAuxiliaryOutput : (HermiteL2 × ℝ) →L[ℝ] HermiteL2 :=
  let A := centralAuxiliaryUnrowedInverse.comp (ContinuousLinearMap.fst ℝ HermiteL2 ℝ)
  A + ((ContinuousLinearMap.snd ℝ HermiteL2 ℝ) -
    (innerSL ℝ centralAuxiliarySourceVector).comp A).smulRight centralAuxiliaryKernelVector

def centralAuxiliaryScalar : (HermiteL2 × ℝ) →L[ℝ] ℝ :=
  -((innerSL ℝ centralAuxiliaryKernelVector).comp (ContinuousLinearMap.fst ℝ HermiteL2 ℝ))

/-- The scalar has the sign required by the physical block `(L,+g;row,0)`:
in the `B=-varpi⁻¹ L` graph its column is the negative Riesz column. -/
def centralAuxiliaryInverse : (HermiteL2 × ℝ) →L[ℝ] (HermiteL2 × ℝ) :=
  centralAuxiliaryOutput.prod centralAuxiliaryScalar

theorem centralAuxiliaryOutput_apply (F : HermiteL2) (t : ℝ) :
    centralAuxiliaryOutput (F, t) =
      centralRadialReducedHilbertInverse (centralAuxiliaryCorrectedSource F) +
        (t - ⟪centralAuxiliarySourceVector,
          centralRadialReducedHilbertInverse (centralAuxiliaryCorrectedSource F)⟫_ℝ) •
          centralAuxiliaryKernelVector := rfl

theorem centralAuxiliaryScalar_apply (F : HermiteL2) (t : ℝ) :
    centralAuxiliaryScalar (F, t) = -⟪F, centralAuxiliaryKernelVector⟫_ℝ := by
  change -⟪centralAuxiliaryKernelVector, F⟫_ℝ = _
  rw [real_inner_comm centralAuxiliaryKernelVector F]

theorem centralAuxiliaryInverse_apply (F : HermiteL2) (t : ℝ) :
    centralAuxiliaryInverse (F, t) = (centralAuxiliaryOutput (F, t), -⟪F, centralAuxiliaryKernelVector⟫_ℝ) := by
  change (centralAuxiliaryOutput (F, t), centralAuxiliaryScalar (F, t)) = _
  rw [centralAuxiliaryScalar_apply]

def CentralAuxiliaryNormalizedEquation (F : HermiteL2) (t : ℝ) (u : HermiteL2) (c : ℝ) : Prop :=
  (u, F + c • centralAuxiliarySourceVector) ∈ centralRadialClosedGraph 2 ∧
    ⟪centralAuxiliarySourceVector, u⟫_ℝ = t

/-- Every source has an actual graph solution after the genuine compact
column removes the true kernel obstruction. The output row is prescribed. -/
theorem centralAuxiliaryInverse_solves (F : HermiteL2) (t : ℝ) :
    CentralAuxiliaryNormalizedEquation F t
      (centralAuxiliaryInverse (F, t)).1 (centralAuxiliaryInverse (F, t)).2 := by
  rw [centralAuxiliaryInverse_apply]
  change (centralAuxiliaryOutput (F, t), F + (-⟪F, centralAuxiliaryKernelVector⟫_ℝ) •
      centralAuxiliarySourceVector) ∈ centralRadialClosedGraph 2 ∧
    ⟪centralAuxiliarySourceVector, centralAuxiliaryOutput (F, t)⟫_ℝ = t
  have hbase := centralRadialReducedHilbertInverse_graph_compatible
    (centralAuxiliaryCorrectedSource F) (centralAuxiliaryCorrectedSource_compat F)
  have hsum := (centralRadialClosedGraph 2).add_mem hbase
    ((centralRadialClosedGraph 2).smul_mem
      (t - ⟪centralAuxiliarySourceVector,
        centralRadialReducedHilbertInverse (centralAuxiliaryCorrectedSource F)⟫_ℝ)
      centralAuxiliaryKernelVector_graph)
  constructor
  · rw [centralAuxiliaryOutput_apply]
    have hc : F + (-⟪F, centralAuxiliaryKernelVector⟫_ℝ) • centralAuxiliarySourceVector =
        centralAuxiliaryCorrectedSource F := by
      rw [centralAuxiliaryCorrectedSource_apply, neg_smul, sub_eq_add_neg]
    rw [hc]
    simpa only [Prod.add_def, Prod.smul_mk, smul_zero, add_zero] using hsum
  · rw [centralAuxiliaryOutput_apply, inner_add_right, real_inner_smul_right,
      centralAuxiliarySource_kernel_pairing, mul_one]
    ring

/-- This is uniqueness in the actual closed graph, rather than a domain
defined to be the image of the inverse. -/
theorem centralAuxiliaryInverse_unique (F : HermiteL2) (t : ℝ) (u : HermiteL2) (c : ℝ)
    (hu : CentralAuxiliaryNormalizedEquation F t u c) :
    (u, c) = centralAuxiliaryInverse (F, t) := by
  have hs := centralAuxiliaryInverse_solves F t
  have hcompat := centralRadialClosedGraph_two_compat u
    (F + c • centralAuxiliarySourceVector) hu.1
  have hK : ⟪F + c • centralAuxiliarySourceVector, centralAuxiliaryKernelVector⟫_ℝ = 0 := by
    rw [centralAuxiliaryKernelVector, real_inner_smul_right, hcompat, mul_zero]
  rw [inner_add_left, real_inner_smul_left, centralAuxiliarySource_kernel_pairing, mul_one] at hK
  have hc : c = (centralAuxiliaryInverse (F, t)).2 := by
    rw [centralAuxiliaryInverse_apply]
    change c = -⟪F, centralAuxiliaryKernelVector⟫_ℝ
    linarith only [hK]
  have hsame : ((centralAuxiliaryInverse (F, t)).1, F + c • centralAuxiliarySourceVector) ∈
      centralRadialClosedGraph 2 := by
    rw [hc]
    exact hs.1
  have hd := (centralRadialClosedGraph 2).sub_mem hu.1 hsame
  change (u - (centralAuxiliaryInverse (F, t)).1,
    (F + c • centralAuxiliarySourceVector) - (F + c • centralAuxiliarySourceVector)) ∈ _ at hd
  rw [sub_self] at hd
  obtain ⟨a, ha⟩ := (centralRadialClosedGraph_two_kernel_iff _).mp hd
  have hrow : ⟪centralAuxiliarySourceVector, u - (centralAuxiliaryInverse (F, t)).1⟫_ℝ = 0 := by
    rw [inner_sub_right, hu.2, hs.2, sub_self]
  rw [ha, real_inner_smul_right] at hrow
  have haz : a = 0 := (mul_eq_zero.mp hrow).resolve_right auxiliary_row_kernel_ne_zero
  have heq : u = (centralAuxiliaryInverse (F, t)).1 := by
    rw [haz, zero_smul] at ha
    exact sub_eq_zero.mp ha
  exact Prod.ext heq hc

def centralAuxiliaryPairEquiv {scale : ℝ} (hscale : 0 < scale) :
    (CentralRadialHilbert scale × ℝ) ≃ₗᵢ[ℝ] (HermiteL2 × ℝ) where
  toLinearEquiv := (centralRadialHilbertEquiv hscale).toLinearEquiv.prodCongr (LinearEquiv.refl ℝ ℝ)
  norm_map' p := by
    change max ‖centralRadialHilbertEquiv hscale p.1‖ ‖p.2‖ = max ‖p.1‖ ‖p.2‖
    rw [(centralRadialHilbertEquiv hscale).norm_map]

theorem centralAuxiliaryPairEquiv_apply {scale : ℝ} (hscale : 0 < scale)
    (u : CentralRadialHilbert scale) (c : ℝ) :
    centralAuxiliaryPairEquiv hscale (u, c) = (centralRadialHilbertEquiv hscale u, c) := rfl

/-- The actual distributional block. The positive ordinary column `gscale`
corresponds to the negative Hilbert column in `B=-varpi⁻¹ L`. -/
def CentralAuxiliaryPhysicalEquation {scale : ℝ} (hscale : 0 < scale)
    (F : CentralRadialHilbert scale) (t : ℝ) (u : CentralRadialHilbert scale) (c : ℝ) : Prop :=
  CentralRadialDistributionEquation scale 2 u (F + c • centralAuxiliaryColumn hscale) ∧
    (∫ r in Ioi 0, sqrt scale * centralAuxiliaryFunction r * u r) = t

theorem centralAuxiliaryPhysicalEquation_iff {scale : ℝ} (hscale : 0 < scale)
    (F : CentralRadialHilbert scale) (t : ℝ) (u : CentralRadialHilbert scale) (c : ℝ) :
    CentralAuxiliaryPhysicalEquation hscale F t u c ↔
      CentralAuxiliaryNormalizedEquation (centralRadialHilbertEquiv hscale F) t
        (centralRadialHilbertEquiv hscale u) c := by
  unfold CentralAuxiliaryPhysicalEquation CentralAuxiliaryNormalizedEquation
  rw [centralRadialDistributionEquation_iff_graph hscale, map_add, map_smul,
    centralAuxiliaryColumn_transform, ← centralAuxiliaryRow_transport hscale]

def centralAuxiliaryPhysicalInverse {scale : ℝ} (hscale : 0 < scale) :
    (CentralRadialHilbert scale × ℝ) →L[ℝ] (CentralRadialHilbert scale × ℝ) :=
  (centralAuxiliaryPairEquiv hscale).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (centralAuxiliaryInverse.comp
      (centralAuxiliaryPairEquiv hscale).toContinuousLinearEquiv.toContinuousLinearMap)

theorem centralAuxiliaryPhysicalInverse_apply {scale : ℝ} (hscale : 0 < scale)
    (p : CentralRadialHilbert scale × ℝ) :
    centralAuxiliaryPhysicalInverse hscale p =
      (centralAuxiliaryPairEquiv hscale).symm (centralAuxiliaryInverse (centralAuxiliaryPairEquiv hscale p)) := rfl

theorem centralAuxiliaryPhysicalInverse_transform {scale : ℝ} (hscale : 0 < scale)
    (p : CentralRadialHilbert scale × ℝ) :
    centralAuxiliaryPairEquiv hscale (centralAuxiliaryPhysicalInverse hscale p) =
      centralAuxiliaryInverse (centralAuxiliaryPairEquiv hscale p) := by
  rw [centralAuxiliaryPhysicalInverse_apply, LinearIsometryEquiv.apply_symm_apply]

/-- This solves the genuine ordinary-radial compact-test equation for
every weighted Hilbert source, together with its actual `dr` row. -/
theorem centralAuxiliaryPhysicalInverse_solves {scale : ℝ} (hscale : 0 < scale)
    (F : CentralRadialHilbert scale) (t : ℝ) :
    CentralAuxiliaryPhysicalEquation hscale F t
      (centralAuxiliaryPhysicalInverse hscale (F, t)).1 (centralAuxiliaryPhysicalInverse hscale (F, t)).2 := by
  apply (centralAuxiliaryPhysicalEquation_iff hscale F t _ _).mpr
  have hs := centralAuxiliaryInverse_solves (centralRadialHilbertEquiv hscale F) t
  have ht := centralAuxiliaryPhysicalInverse_transform hscale (F, t)
  change (centralRadialHilbertEquiv hscale (centralAuxiliaryPhysicalInverse hscale (F, t)).1,
      (centralAuxiliaryPhysicalInverse hscale (F, t)).2) =
    centralAuxiliaryInverse (centralRadialHilbertEquiv hscale F, t) at ht
  rw [← ht] at hs
  exact hs

theorem centralAuxiliaryPhysicalInverse_unique {scale : ℝ} (hscale : 0 < scale)
    (F : CentralRadialHilbert scale) (t : ℝ) (u : CentralRadialHilbert scale) (c : ℝ)
    (hu : CentralAuxiliaryPhysicalEquation hscale F t u c) :
    (u, c) = centralAuxiliaryPhysicalInverse hscale (F, t) := by
  apply (centralAuxiliaryPairEquiv hscale).injective
  rw [centralAuxiliaryPhysicalInverse_transform]
  change (centralRadialHilbertEquiv hscale u, c) =
    centralAuxiliaryInverse (centralRadialHilbertEquiv hscale F, t)
  exact centralAuxiliaryInverse_unique _ t _ c ((centralAuxiliaryPhysicalEquation_iff hscale F t u c).mp hu)

/-- The same finite constant works at every positive height scale. Both
directions of the transport are genuine linear isometries. -/
theorem centralAuxiliaryPhysicalInverse_uniform_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (scale : ℝ) (hscale : 0 < scale) (p : CentralRadialHilbert scale × ℝ),
      ‖centralAuxiliaryPhysicalInverse hscale p‖ ≤ C * ‖p‖ := by
  refine ⟨‖centralAuxiliaryInverse‖, norm_nonneg _, ?_⟩
  intro scale hscale p
  calc
    _ = ‖centralAuxiliaryInverse (centralAuxiliaryPairEquiv hscale p)‖ := by
      rw [← (centralAuxiliaryPairEquiv hscale).norm_map, centralAuxiliaryPhysicalInverse_transform]
    _ ≤ ‖centralAuxiliaryInverse‖ * ‖centralAuxiliaryPairEquiv hscale p‖ :=
      centralAuxiliaryInverse.le_opNorm _
    _ = _ := by rw [(centralAuxiliaryPairEquiv hscale).norm_map]

end ContinuousFlexibility.Radial
