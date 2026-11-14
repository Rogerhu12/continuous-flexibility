module

public import ContinuousFlexibility.Scalar.WeightedAngularPrimitiveJets
public import ContinuousFlexibility.Analysis.CircleJetClosedGraph
public import ContinuousFlexibility.Analysis.CylinderTestPairing

/-!
# The cylinder L² bound for angular integration

The actual integral from zero is bounded on each angular interval by
Cauchy--Schwarz. Fubini then gives its cylinder operator bound with constant
`π`, without losing a radial or angular derivative.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

theorem scalar_angleMeasure_mass : angleMeasure univ = ENNReal.ofReal Real.pi := by
  rw [angleMeasure, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]

theorem scalar_integral_angle_const (c : ℝ) :
    (∫ _ : ℝ, c ∂angleMeasure) = Real.pi * c := by
  simp only [integral_const, measureReal_def, scalar_angleMeasure_mass,
    ENNReal.toReal_ofReal Real.pi_pos.le, smul_eq_mul]

private theorem scalar_integral_angle_abs_le {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ t, |g t| ∂angleMeasure) ≤
      Real.sqrt Real.pi * Real.sqrt (∫ t, g t ^ 2 ∂angleMeasure) := by
  let : IsFiniteMeasure angleMeasure :=
    ⟨by rw [scalar_angleMeasure_mass]; exact ENNReal.ofReal_lt_top⟩
  have h1 : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) angleMeasure :=
    memLp_const 1
  have hg2 : MemLp g (ENNReal.ofReal 2) angleMeasure := by
    simpa using memLp_angleMeasure_of_continuous hg
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two h1 hg2
  have hmass : (∫ _ : ℝ, ‖(1 : ℝ)‖ ^ (2 : ℝ) ∂angleMeasure) = Real.pi := by
    simpa only [norm_one, Real.one_rpow, mul_one] using scalar_integral_angle_const 1
  have hsq : (∫ t, ‖g t‖ ^ (2 : ℝ) ∂angleMeasure) =
      ∫ t, g t ^ 2 ∂angleMeasure := by
    simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [hmass, hsq, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  simpa only [norm_one, one_mul, Real.norm_eq_abs] using h

theorem scalarAngularPrimitive_sq_le {f : PolarPoint → ℝ} (hf : Continuous f)
    (r : ℝ) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    scalarAngularPrimitive f (r, θ) ^ 2 ≤
      Real.pi * ∫ t, f (r, t) ^ 2 ∂angleMeasure := by
  let : IsFiniteMeasure angleMeasure :=
    ⟨by rw [scalar_angleMeasure_mass]; exact ENNReal.ofReal_lt_top⟩
  have hs : Continuous (fun t : ℝ => f (r, t)) :=
    hf.comp (continuous_const.prodMk continuous_id)
  have hsi : Integrable (fun t => f (r, t)) angleMeasure :=
    (memLp_angleMeasure_of_continuous hs).integrable (by norm_num)
  have habs : |scalarAngularPrimitive f (r, θ)| ≤ ∫ t, |f (r, t)| ∂angleMeasure := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..θ, |f (r, t)| := by
        simpa only [scalarAngularPrimitive, Real.norm_eq_abs] using
          (intervalIntegral.norm_integral_le_integral_norm (f := fun t => f (r, t)) hθ.1)
      _ ≤ ∫ t, |f (r, t)| ∂angleMeasure := by
        rw [intervalIntegral.integral_of_le hθ.1]
        apply setIntegral_mono_set hsi.norm (Filter.Eventually.of_forall (fun t => abs_nonneg _))
        exact Filter.Eventually.of_forall fun t ht => ⟨ht.1, ht.2.trans hθ.2⟩
  have hbound := habs.trans (scalar_integral_angle_abs_le hs)
  calc
    _ = |scalarAngularPrimitive f (r, θ)| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.sqrt Real.pi * Real.sqrt (∫ t, f (r, t) ^ 2 ∂angleMeasure)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hbound 2
    _ = Real.pi * ∫ t, f (r, t) ^ 2 ∂angleMeasure := by
      rw [mul_pow, Real.sq_sqrt Real.pi_pos.le,
        Real.sq_sqrt (integral_nonneg fun t => sq_nonneg _)]

theorem scalar_eLpNorm_two_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal ^ 2 = ∫ t, f t ^ 2 ∂μ := by
  have he := hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)
  have htwo : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  rw [htwo] at he
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs] at he
  have hs : eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (∫ t, f t ^ 2 ∂μ)) := by
    simpa only [Real.sqrt_eq_rpow, one_div] using he
  rw [hs, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    Real.sq_sqrt (integral_nonneg fun t => sq_nonneg _)]

/-- Angular integration is a bounded operator on the actual material cylinder. -/
theorem scalarAngularPrimitive_memLp_and_norm_le {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (hmem : MemLp f 2 materialCylinderMeasure) :
    MemLp (scalarAngularPrimitive f) 2 materialCylinderMeasure ∧
      (eLpNorm (scalarAngularPrimitive f) 2 materialCylinderMeasure).toReal ≤
        Real.pi * (eLpNorm f 2 materialCylinderMeasure).toReal := by
  let : IsFiniteMeasure angleMeasure :=
    ⟨by rw [scalar_angleMeasure_mass]; exact ENNReal.ofReal_lt_top⟩
  let G : ℝ → ℝ := fun r => Real.pi * ∫ t, f (r, t) ^ 2 ∂angleMeasure
  have hsq : Integrable (fun p : PolarPoint => f p ^ 2)
      ((volume : Measure ℝ).prod angleMeasure) := by
    rw [← materialCylinderMeasure_eq_prod]
    exact hmem.integrable_sq
  have hG : Integrable G volume := hsq.integral_prod_left.const_mul Real.pi
  have hGp : Integrable (fun p : PolarPoint => G p.1) materialCylinderMeasure := by
    rw [materialCylinderMeasure_eq_prod]
    exact hG.comp_fst angleMeasure
  have hbound : ∀ᵐ p ∂materialCylinderMeasure,
      scalarAngularPrimitive f p ^ 2 ≤ G p.1 := by
    filter_upwards [ae_restrict_mem (MeasurableSet.prod MeasurableSet.univ measurableSet_Ioc)] with p hp
    exact scalarAngularPrimitive_sq_le hf.continuous p.1 ⟨hp.2.1.le, hp.2.2⟩
  have hFint : Integrable (fun p => scalarAngularPrimitive f p ^ 2)
      materialCylinderMeasure := by
    apply hGp.mono' ((scalarAngularPrimitive_contDiff hf).pow 2).continuous.aestronglyMeasurable
    filter_upwards [hbound] with p hp
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (scalarAngularPrimitive f p))] using hp
  have hF : MemLp (scalarAngularPrimitive f) 2 materialCylinderMeasure :=
    (memLp_two_iff_integrable_sq
      (scalarAngularPrimitive_contDiff hf).continuous.aestronglyMeasurable).mpr hFint
  have hGint : (∫ p, G p.1 ∂materialCylinderMeasure) =
      Real.pi ^ 2 * ∫ p, f p ^ 2 ∂materialCylinderMeasure := by
    simp only [materialCylinderMeasure_eq_prod]
    rw [integral_prod (fun p : PolarPoint => G p.1) (hG.comp_fst angleMeasure)]
    simp only [scalar_integral_angle_const, G, ← mul_assoc, ← pow_two]
    rw [integral_const_mul, ← integral_prod (fun p : PolarPoint => f p ^ 2) hsq]
  have hint : (eLpNorm (scalarAngularPrimitive f) 2 materialCylinderMeasure).toReal ^ 2 ≤
      Real.pi ^ 2 * (eLpNorm f 2 materialCylinderMeasure).toReal ^ 2 := by
    rw [scalar_eLpNorm_two_sq hF, scalar_eLpNorm_two_sq hmem, ← hGint]
    exact integral_mono_ae hFint hGp hbound
  refine ⟨hF, ?_⟩
  have hn : 0 ≤ (eLpNorm (scalarAngularPrimitive f) 2 materialCylinderMeasure).toReal :=
    ENNReal.toReal_nonneg
  have hm : 0 ≤ (eLpNorm f 2 materialCylinderMeasure).toReal := ENNReal.toReal_nonneg
  apply (sq_le_sq₀ hn (mul_nonneg Real.pi_pos.le hm)).mp
  simpa only [mul_pow] using hint

end ContinuousFlexibility.Statements
