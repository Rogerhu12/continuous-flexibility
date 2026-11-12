import ContinuousFlexibility.Analysis.N06ReferenceNormalTransport
import ContinuousFlexibility.Analysis.N05CanonicalPhysicalChange

/-!
# Actual L2 control of the transported reference normal derivative

The physical functions are arbitrary L2 representatives on the actual
half-period piece. The inverse chart transports their measurable classes,
and the genuine Jacobian formula controls their squares. Only the first
radial coordinate and height bounds enter the estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss m : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- The genuine inverse chart transports the measurable class of a raw
physical L2 representative; pointwise measurability is not required. -/
theorem n06_reference_inverseChart_aestronglyMeasurable
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hangle : ∀ p ∈ physicalPieceOpen S K z m, (K.chart z m p).2 = p.2)
    {f : PolarPoint → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)))) :
    AEStronglyMeasurable (fun p => f (K.inverseChart z m p)) (canonicalMeasure S K m) := by
  have hcharts := h04.1.charts z hz hs m
  have hmeas : MeasurableSet
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)) :=
    (h04.1.domains z hz hs m).1.measurableSet.inter
      (MeasurableSet.univ.prod measurableSet_Ioc)
  have hpull : (fun p => f (K.inverseChart z m p)) =ᵐ[canonicalMeasure S K m]
      (fun p => hf.mk f (K.inverseChart z m p)) := by
    apply (n05_canonicalChart_ae_iff h04 hz hs m hangle _).mpr
    simp only [n05PhysicalPieceHalfPeriod]
    filter_upwards [hf.ae_eq_mk,
      ae_restrict_mem hmeas] with p hp hpU
    rw [hcharts.2.2.1 p hpU.1]
    exact hp
  have hinverse : AEMeasurable (K.inverseChart z m) (canonicalMeasure S K m) :=
    (hcharts.2.2.2.2.2.1.continuousOn.mono
      (fun p hp => ⟨hp.1, mem_univ _⟩)).aemeasurable
        (measurableSet_Ioo.prod measurableSet_Ioc)
  exact (hf.measurable_mk.comp_aemeasurable hinverse).aestronglyMeasurable.congr hpull.symm

/-- A radial multiplier is transported with the actual absolute Jacobian.
The coefficient hypothesis is a pointwise bound on the primitive multiplier,
not an assumed bound on the transported L2 function. -/
theorem n06_reference_radial_multiplier_lp
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hΩ : physicalPieceOpen S K z m = referencePhysicalPieceOpen S K m)
    {Y a : ℝ → ℝ}
    (hY : ContDiffOn ℝ ∞ Y (Ioo (K.physicalLeft m) (K.physicalRight m)))
    (hchart : ∀ p ∈ referencePhysicalPieceOpen S K m, K.chart z m p = (Y p.1, p.2))
    (ha : ContinuousOn a (Ioo (K.physicalLeft m) (K.physicalRight m)))
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ r ∈ Ioo (K.physicalLeft m) (K.physicalRight m),
      |deriv Y r| * a r ^ 2 ≤ B)
    {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (volume.restrict
      (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi))) :
    MemLp (fun p => a (K.inverseChart z m p).1 * f (K.inverseChart z m p)) 2
      (canonicalMeasure S K m) ∧
    (∫ p, (a (K.inverseChart z m p).1 * f (K.inverseChart z m p)) ^ 2
      ∂canonicalMeasure S K m) ≤ B *
        ∫ p, f p ^ 2 ∂volume.restrict
          (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi) := by
  let μ : Measure PolarPoint := volume.restrict
    (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi)
  let g : PolarPoint → ℝ := fun p => a (K.inverseChart z m p).1 * f (K.inverseChart z m p)
  have hcharts := h04.1.charts z hz hs m
  rw [hΩ] at hcharts
  have hangle (p : PolarPoint) (hp : p ∈ physicalPieceOpen S K z m) :
      (K.chart z m p).2 = p.2 := by
    have hpRef : p ∈ referencePhysicalPieceOpen S K m := by simpa only [hΩ] using hp
    simpa only using (congrArg (fun q : PolarPoint => q.2) (hchart p hpRef))
  have hmeasure : volume.restrict
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)) = μ := by
    simp only [hΩ, referencePhysicalPieceOpen, prod_inter_prod, inter_univ, univ_inter, μ]
  have haComp : ContinuousOn (fun p => a (K.inverseChart z m p).1) (canonicalOpen S K m) :=
    ha.comp' hcharts.2.2.2.2.2.1.continuousOn.fst (fun p hp => (hcharts.2.1 hp).1)
  have haCan : AEStronglyMeasurable (fun p => a (K.inverseChart z m p).1)
      (canonicalMeasure S K m) :=
    (haComp.mono (fun p hp => ⟨hp.1, mem_univ _⟩)).aestronglyMeasurable
      (measurableSet_Ioo.prod measurableSet_Ioc)
  have hg : AEStronglyMeasurable g (canonicalMeasure S K m) := haCan.mul
    (n06_reference_inverseChart_aestronglyMeasurable h04 hz hs hangle
      (by simpa only [hmeasure] using hf.aestronglyMeasurable))
  have haPhys : AEStronglyMeasurable (fun p : PolarPoint => a p.1) μ :=
    (ha.comp' continuous_fst.continuousOn (fun p hp => hp.1)).aestronglyMeasurable
      (measurableSet_Ioo.prod measurableSet_Ioc)
  have hYd : ContinuousOn (deriv Y) (Ioo (K.physicalLeft m) (K.physicalRight m)) :=
    hY.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)
  have hJPhys : AEStronglyMeasurable (fun p : PolarPoint => |deriv Y p.1|) μ :=
    (hYd.abs.comp' continuous_fst.continuousOn (fun p hp => hp.1)).aestronglyMeasurable
      (measurableSet_Ioo.prod measurableSet_Ioc)
  have hwMeas : AEStronglyMeasurable (fun p => |deriv Y p.1| * (a p.1 * f p) ^ 2) μ :=
    hJPhys.mul ((haPhys.mul hf.aestronglyMeasurable).pow 2)
  have hdom : ∀ᵐ p ∂μ, |deriv Y p.1| * (a p.1 * f p) ^ 2 ≤ B * f p ^ 2 := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    calc
      _ = (|deriv Y p.1| * a p.1 ^ 2) * f p ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hbound p.1 hp.1) (sq_nonneg _)
  have hweight : Integrable (fun p => |deriv Y p.1| * (a p.1 * f p) ^ 2) μ := by
    apply (hf.integrable_sq.const_mul B).mono' hwMeas
    filter_upwards [hdom] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
    exact hp
  have heq : (fun p => |planeJacobian (K.chart z m) p| * g (K.chart z m p) ^ 2)
      =ᵐ[μ] (fun p => |deriv Y p.1| * (a p.1 * f p) ^ 2) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    have hpo : p ∈ referencePhysicalPieceOpen S K m := ⟨hp.1, mem_univ _⟩
    simp only [g, hcharts.2.2.1 p hpo, n06_reference_radial_jacobian hY hchart hpo]
  have hgSq : Integrable (fun p => g p ^ 2) (canonicalMeasure S K m) :=
    (n05_canonicalChart_integrable_iff h04 hz hs m hangle (fun p => g p ^ 2)).mpr
      (by simpa only [n05PhysicalPieceHalfPeriod, hmeasure] using hweight.congr heq.symm)
  refine ⟨(memLp_two_iff_integrable_sq hg).mpr hgSq, ?_⟩
  calc
    _ = ∫ p, |planeJacobian (K.chart z m) p| * g (K.chart z m p) ^ 2 ∂μ := by
      simpa only [n05PhysicalPieceHalfPeriod, hmeasure] using
        n05_canonicalChart_integral h04 hz hs m hangle (fun p => g p ^ 2)
    _ = ∫ p, |deriv Y p.1| * (a p.1 * f p) ^ 2 ∂μ := integral_congr_ae heq
    _ ≤ ∫ p, B * f p ^ 2 ∂μ :=
      integral_mono_ae hweight (hf.integrable_sq.const_mul B) hdom
    _ = _ := integral_const_mul B (fun p => f p ^ 2)

private theorem n06_abs_mul_inv_sq {x : ℝ} (hx : x ≠ 0) :
    |x| * (x⁻¹) ^ 2 = |x⁻¹| := by
  calc
    _ = |x| * (|x|⁻¹) ^ 2 := by rw [← sq_abs (x⁻¹), abs_inv]
    _ = |x|⁻¹ := by
      rw [pow_two, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hx), one_mul]
    _ = _ := (abs_inv x).symm

private theorem n06_normal_multiplier_square_bounds
    {H dH J B : ℝ} (_hB : 0 ≤ B) (hJ : J ≠ 0)
    (hHi : |H⁻¹| ≤ B) (hdH : |dH| ≤ B) (hJi : |J⁻¹| ≤ B) :
    |J| * (H⁻¹ * J⁻¹) ^ 2 ≤ B ^ 3 ∧
      |J| * (-dH * (H⁻¹) ^ 2 * J⁻¹) ^ 2 ≤ B ^ 7 := by
  have hH2 : (H⁻¹) ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs (H⁻¹)]
    exact pow_le_pow_left₀ (abs_nonneg _) hHi 2
  have hH4 : (H⁻¹) ^ 4 ≤ B ^ 4 := by
    calc
      _ = ((H⁻¹) ^ 2) ^ 2 := by ring
      _ ≤ (B ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hH2 2
      _ = _ := by ring
  have hdH2 : dH ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs dH]
    exact pow_le_pow_left₀ (abs_nonneg _) hdH 2
  constructor
  · calc
      _ = (H⁻¹) ^ 2 * (|J| * (J⁻¹) ^ 2) := by ring
      _ = (H⁻¹) ^ 2 * |J⁻¹| := by rw [n06_abs_mul_inv_sq hJ]
      _ ≤ B ^ 2 * B := mul_le_mul hH2 hJi (abs_nonneg _) (sq_nonneg _)
      _ = _ := by ring
  · calc
      _ = (dH ^ 2 * (H⁻¹) ^ 4) * (|J| * (J⁻¹) ^ 2) := by ring
      _ = (dH ^ 2 * (H⁻¹) ^ 4) * |J⁻¹| := by rw [n06_abs_mul_inv_sq hJ]
      _ ≤ (B ^ 2 * B ^ 4) * B :=
        mul_le_mul (mul_le_mul hdH2 hH4 (by positivity) (sq_nonneg _)) hJi
          (abs_nonneg _) (by positivity)
      _ = _ := by ring

/-- The actual height and displayed normal derivative are canonical L2
functions. The constants use precisely the primitive first-jet bounds. -/
theorem n06_reference_height_normal_lp
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hΩ : physicalPieceOpen S K z m = referencePhysicalPieceOpen S K m)
    {Y h : ℝ → ℝ}
    (hY : ContDiffOn ℝ ∞ Y (Ioo (K.physicalLeft m) (K.physicalRight m)))
    (hh : ContDiffOn ℝ ∞ h (Ioo (K.physicalLeft m) (K.physicalRight m)))
    (hchart : ∀ p ∈ referencePhysicalPieceOpen S K m, K.chart z m p = (Y p.1, p.2))
    (hheight : ∀ p ∈ referencePhysicalPieceOpen S K m, K.height z m p = h p.1)
    {B : ℝ} (hB : 0 ≤ B)
    (hcoeff : ∀ r ∈ Ioo (K.physicalLeft m) (K.physicalRight m),
      |h r| + |(h r)⁻¹| + |deriv h r| + |deriv Y r| + |(deriv Y r)⁻¹| ≤ B)
    {w dw : PolarPoint → ℝ}
    (hw : MemLp w 2 (volume.restrict
      (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi)))
    (hdw : MemLp dw 2 (volume.restrict
      (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi))) :
    (MemLp (canonicalHeight S K z m w) 2 (canonicalMeasure S K m) ∧
      (∫ p, canonicalHeight S K z m w p ^ 2 ∂canonicalMeasure S K m) ≤
        B ^ 3 * ∫ p, w p ^ 2 ∂volume.restrict
          (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi)) ∧
    (MemLp (n06ReferenceNormalField S K z m Y h w dw) 2 (canonicalMeasure S K m) ∧
      (∫ p, n06ReferenceNormalField S K z m Y h w dw p ^ 2 ∂canonicalMeasure S K m) ≤
        2 * (B ^ 3 * (∫ p, dw p ^ 2 ∂volume.restrict
            (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi)) +
          B ^ 7 * ∫ p, w p ^ 2 ∂volume.restrict
            (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi))) := by
  have hcharts := h04.1.charts z hz hs m
  rw [hΩ] at hcharts
  have hh0 (r : ℝ) (hr : r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)) : h r ≠ 0 := by
    have he := (hcharts.2.2.2.2.2.2.2 (r, 0) ⟨hr, mem_univ _⟩).1.ne'
    rwa [hheight (r, 0) ⟨hr, mem_univ _⟩] at he
  have hY0 (r : ℝ) (hr : r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)) :
      deriv Y r ≠ 0 := by
    have hp : (r, (0 : ℝ)) ∈ referencePhysicalPieceOpen S K m := ⟨hr, mem_univ _⟩
    have he := (hcharts.2.2.2.2.2.2.2 (r, 0) hp).2.1
    rwa [n06_reference_radial_jacobian hY hchart hp] at he
  have hc (r : ℝ) (hr : r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)) :
      |(h r)⁻¹| ≤ B ∧ |deriv h r| ≤ B ∧ |deriv Y r| ≤ B ∧ |(deriv Y r)⁻¹| ≤ B := by
    have he := hcoeff r hr
    have h0 := abs_nonneg (h r)
    have h1 := abs_nonneg ((h r)⁻¹)
    have h2 := abs_nonneg (deriv h r)
    have h3 := abs_nonneg (deriv Y r)
    have h4 := abs_nonneg ((deriv Y r)⁻¹)
    exact ⟨by linarith only [he, h0, h2, h3, h4],
      by linarith only [he, h0, h1, h3, h4],
      by linarith only [he, h0, h1, h2, h4],
      by linarith only [he, h0, h1, h2, h3]⟩
  have hhi : ContinuousOn (fun r => (h r)⁻¹)
      (Ioo (K.physicalLeft m) (K.physicalRight m)) := hh.continuousOn.inv₀ hh0
  have hYd : ContinuousOn (deriv Y) (Ioo (K.physicalLeft m) (K.physicalRight m)) :=
    hY.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)
  have hYi : ContinuousOn (fun r => (deriv Y r)⁻¹)
      (Ioo (K.physicalLeft m) (K.physicalRight m)) := hYd.inv₀ hY0
  have hhd : ContinuousOn (deriv h) (Ioo (K.physicalLeft m) (K.physicalRight m)) :=
    hh.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)
  let a : ℝ → ℝ := fun r => (h r)⁻¹ * (deriv Y r)⁻¹
  let b : ℝ → ℝ := fun r => -deriv h r * ((h r)⁻¹) ^ 2 * (deriv Y r)⁻¹
  have ha : ContinuousOn a (Ioo (K.physicalLeft m) (K.physicalRight m)) := hhi.mul hYi
  have hb : ContinuousOn b (Ioo (K.physicalLeft m) (K.physicalRight m)) :=
    (hhd.neg.mul (hhi.pow 2)).mul hYi
  have hweight (r : ℝ) (hr : r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)) :
      |deriv Y r| * a r ^ 2 ≤ B ^ 3 ∧ |deriv Y r| * b r ^ 2 ≤ B ^ 7 :=
    n06_normal_multiplier_square_bounds hB (hY0 r hr)
      (hc r hr).1 (hc r hr).2.1 (hc r hr).2.2.2
  have hheightWeight (r : ℝ) (hr : r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)) :
      |deriv Y r| * ((h r)⁻¹) ^ 2 ≤ B ^ 3 := by
    have hsquare : ((h r)⁻¹) ^ 2 ≤ B ^ 2 := by
      rw [← sq_abs ((h r)⁻¹)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hc r hr).1 2
    calc
      _ ≤ B * B ^ 2 := mul_le_mul (hc r hr).2.2.1 hsquare (sq_nonneg _) hB
      _ = _ := by ring
  obtain ⟨hZ, hZbound⟩ := n06_reference_radial_multiplier_lp h04 hz hs hΩ hY hchart hhi
    (by positivity : 0 ≤ B ^ 3) hheightWeight hw
  have hWrep : (fun p => (h (K.inverseChart z m p).1)⁻¹ * w (K.inverseChart z m p))
      =ᵐ[canonicalMeasure S K m] canonicalHeight S K z m w := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    have hx := hcharts.2.1 ⟨hp.1, mem_univ _⟩
    simp only [canonicalHeight, hheight _ hx, div_eq_mul_inv, mul_comm]
  have hWL : MemLp (canonicalHeight S K z m w) 2 (canonicalMeasure S K m) :=
    MemLp.ae_eq hWrep hZ
  have hWbound : (∫ p, canonicalHeight S K z m w p ^ 2 ∂canonicalMeasure S K m) ≤
      B ^ 3 * ∫ p, w p ^ 2 ∂volume.restrict
        (Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi) := by
    refine (integral_congr_ae ?_).trans_le hZbound
    filter_upwards [hWrep] with p hp
    rw [hp]
  obtain ⟨hA, hAbound⟩ := n06_reference_radial_multiplier_lp h04 hz hs hΩ hY hchart ha
    (by positivity : 0 ≤ B ^ 3) (fun r hr => (hweight r hr).1) hdw
  obtain ⟨hBfield, hBbound⟩ := n06_reference_radial_multiplier_lp h04 hz hs hΩ hY hchart hb
    (by positivity : 0 ≤ B ^ 7) (fun r hr => (hweight r hr).2) hw
  let A : PolarPoint → ℝ := fun p => a (K.inverseChart z m p).1 * dw (K.inverseChart z m p)
  let F : PolarPoint → ℝ := fun p => b (K.inverseChart z m p).1 * w (K.inverseChart z m p)
  have hrep : (fun p => A p + F p) =ᵐ[canonicalMeasure S K m]
      n06ReferenceNormalField S K z m Y h w dw := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    have hx := hcharts.2.1 ⟨hp.1, mem_univ _⟩
    dsimp only [A, F, a, b, n06ReferenceNormalField, canonicalHeight]
    rw [hheight _ hx]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hsumL : MemLp (fun p => A p + F p) 2 (canonicalMeasure S K m) := hA.add hBfield
  have hGL : MemLp (n06ReferenceNormalField S K z m Y h w dw) 2 (canonicalMeasure S K m) :=
    MemLp.ae_eq hrep hsumL
  refine ⟨⟨hWL, hWbound⟩, hGL, ?_⟩
  have hiA : Integrable (fun p => A p ^ 2) (canonicalMeasure S K m) := hA.integrable_sq
  have hiF : Integrable (fun p => F p ^ 2) (canonicalMeasure S K m) := hBfield.integrable_sq
  have hiMajor : Integrable (fun p => 2 * (A p ^ 2 + F p ^ 2))
      (canonicalMeasure S K m) := (hiA.add hiF).const_mul 2
  have hsumIntegral : (∫ p, A p ^ 2 + F p ^ 2 ∂canonicalMeasure S K m) =
      (∫ p, A p ^ 2 ∂canonicalMeasure S K m) + ∫ p, F p ^ 2 ∂canonicalMeasure S K m :=
    integral_add hiA hiF
  calc
    _ = ∫ p, (A p + F p) ^ 2 ∂canonicalMeasure S K m := by
      apply integral_congr_ae
      filter_upwards [hrep] with p hp
      rw [hp]
    _ ≤ ∫ p, 2 * (A p ^ 2 + F p ^ 2) ∂canonicalMeasure S K m := by
      apply integral_mono_ae hsumL.integrable_sq hiMajor
      filter_upwards with p
      nlinarith only [sq_nonneg (A p - F p)]
    _ = 2 * ((∫ p, A p ^ 2 ∂canonicalMeasure S K m) +
        ∫ p, F p ^ 2 ∂canonicalMeasure S K m) := by
      rw [integral_const_mul, hsumIntegral]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hAbound hBbound) (by norm_num)

/-- Primitive coordinate bounds supply both canonical L2 premises of the
weak transport theorem, so the displayed derivative is no longer assumed
to belong to L2. The unknown still has only its original physical weak derivative. -/
theorem n06_reference_normal_transport_of_bounds
    (h04 : N04Properties D T S C L K base loss ε) (hab : D.a ≤ D.b)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hΩ : physicalPieceOpen S K z m = referencePhysicalPieceOpen S K m)
    {Y h : ℝ → ℝ}
    (hY : ContDiffOn ℝ ∞ Y (Ioo (K.physicalLeft m) (K.physicalRight m)))
    (hh : ContDiffOn ℝ ∞ h (Ioo (K.physicalLeft m) (K.physicalRight m)))
    (hchart : ∀ p ∈ referencePhysicalPieceOpen S K m, K.chart z m p = (Y p.1, p.2))
    (hheight : ∀ p ∈ referencePhysicalPieceOpen S K m, K.height z m p = h p.1)
    {B : ℝ} (hB : 0 ≤ B)
    (hcoeff : ∀ r ∈ Ioo (K.physicalLeft m) (K.physicalRight m),
      |h r| + |(h r)⁻¹| + |deriv h r| + |deriv Y r| + |(deriv Y r)⁻¹| ≤ B)
    {w dw : PolarPoint → ℝ} (hweak : WeakNormalDerivative D w dw)
    (hw : MemLp w 2 (radialPhysicalMeasure D))
    (hdw : MemLp dw 2 (radialPhysicalMeasure D))
    (hwp : Function.Periodic w (0, Real.pi))
    (hdwp : Function.Periodic dw (0, Real.pi)) :
    MemLp (n06ReferenceNormalField S K z m Y h w dw) 2 (canonicalMeasure S K m) ∧
      ∀ φ, CanonicalTest S K m φ →
        (∫ p, n06ReferenceNormalField S K z m Y h w dw p * φ p ∂canonicalMeasure S K m) =
        -(∫ p, canonicalHeight S K z m w p * mixedDerivative 1 0 φ p
          ∂canonicalMeasure S K m) := by
  have hK := (n06_N04_qualitative_parts h04).1
  have hsub : Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi ⊆
      radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi) := by
    intro p hp
    exact ⟨(hK.referenceBounds m).2.2 hp.1, hp.2.1,
      hp.2.2.trans (by linarith [Real.pi_pos])⟩
  have hwPiece := MemLp.mono_measure (Measure.restrict_mono hsub le_rfl) hw
  have hdwPiece := MemLp.mono_measure (Measure.restrict_mono hsub le_rfl) hdw
  obtain ⟨⟨hW, _⟩, hG, _⟩ :=
    n06_reference_height_normal_lp h04 hz hs hΩ hY hh hchart hheight hB hcoeff hwPiece hdwPiece
  exact ⟨hG, n06_reference_normal_transport hK hab hz hs hΩ hY hh hchart hheight
    hweak hw hdw hwp hdwp hW hG⟩

end ContinuousFlexibility.Analysis
