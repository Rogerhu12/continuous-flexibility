import ContinuousFlexibility.Scalar.HeightDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith

/-!
# Local pointwise bounds on the material cylinder

The fundamental theorem of calculus controls a value by the average and
the derivative on an interval. Applying this estimate in both coordinates
gives an integral over the material window. Cauchy--Schwarz then gives the
four local `L²` norms with a constant independent of the window position.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff ENNReal

set_option backward.isDefEq.respectTransparency false

/-- The endpoint value estimate includes both endpoints of the interval. -/
theorem abs_le_interval_average_add_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b) :
    |f t| ≤ (b - a)⁻¹ * (∫ y in Ioc a b, |f y|) +
      ∫ y in Ioc a b, |deriv f y| := by
  let A : ℝ := ∫ y in Ioc a b, |deriv f y|
  have hdf := (contDiff_infty_iff_deriv.mp hf).2
  have hA : IntegrableOn (fun y => |deriv f y|) (Ioc a b) volume :=
    hdf.continuous.abs.integrableOn_Ioc
  have hordered (u v : ℝ) (hau : a ≤ u) (hvb : v ≤ b) (huv : u ≤ v) :
      |f v - f u| ≤ A := by
    have he : (∫ y in u..v, deriv f y) = f v - f u :=
      intervalIntegral.integral_deriv_eq_sub (fun y _ => hf.differentiable (by simp) y)
        (hdf.continuous.intervalIntegrable u v)
    calc
      |f v - f u| = ‖∫ y in u..v, deriv f y‖ := by rw [he, Real.norm_eq_abs]
      _ ≤ ∫ y in u..v, |deriv f y| := by
        simpa only [Real.norm_eq_abs] using
          (intervalIntegral.norm_integral_le_integral_norm (f := deriv f) huv)
      _ ≤ A := by
        rw [intervalIntegral.integral_of_le huv]
        exact setIntegral_mono_set hA (Eventually.of_forall fun _ => abs_nonneg _)
          (Eventually.of_forall fun _ hy => ⟨hau.trans_lt hy.1, hy.2.trans hvb⟩)
  have hpoint (y : ℝ) (hy : y ∈ Ioc a b) : |f t| ≤ |f y| + A := by
    have hdiff : |f t - f y| ≤ A := by
      by_cases hyt : y ≤ t
      · exact hordered y t hy.1.le ht.2 hyt
      · rw [abs_sub_comm]
        exact hordered t y ht.1 hy.2 (le_of_not_ge hyt)
    calc
      |f t| = |f t - f y + f y| := by rw [sub_add_cancel]
      _ ≤ |f t - f y| + |f y| := abs_add_le _ _
      _ ≤ |f y| + A := by linarith
  have hleft : IntegrableOn (fun _ : ℝ => |f t|) (Ioc a b) volume :=
    continuous_const.integrableOn_Ioc
  have hfi : IntegrableOn (fun y => |f y|) (Ioc a b) volume :=
    hf.continuous.abs.integrableOn_Ioc
  have hconst : IntegrableOn (fun _ : ℝ => A) (Ioc a b) volume :=
    continuous_const.integrableOn_Ioc
  have hm := setIntegral_mono_on hleft (hfi.add hconst) measurableSet_Ioc hpoint
  change (∫ y in Ioc a b, |f t|) ≤ ∫ y in Ioc a b, |f y| + A at hm
  rw [integral_add hfi hconst, setIntegral_const, setIntegral_const] at hm
  simp only [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le),
    smul_eq_mul] at hm
  have hlen : 0 < b - a := sub_pos.mpr hab
  calc
    |f t| = (b - a)⁻¹ * ((b - a) * |f t|) := by
      rw [← mul_assoc, inv_mul_cancel₀ hlen.ne', one_mul]
    _ ≤ (b - a)⁻¹ * ((∫ y in Ioc a b, |f y|) + (b - a) * A) :=
      mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hlen.le)
    _ = _ := by rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hlen.ne', one_mul]

theorem deriv_cylinder_radial_slice {g : PolarPoint → ℝ} (hg : Differentiable ℝ g)
    (x θ : ℝ) : deriv (fun y : ℝ => g (y, θ)) x = radialPartial g (x, θ) :=
  ((hg (x, θ)).hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x θ))).deriv

theorem deriv_cylinder_angular_slice {g : PolarPoint → ℝ} (hg : Differentiable ℝ g)
    (x θ : ℝ) : deriv (fun t : ℝ => g (x, t)) θ = angularPartial g (x, θ) :=
  ((hg (x, θ)).hasFDerivAt.comp_hasDerivAt θ
    ((hasDerivAt_const θ x).prodMk (hasDerivAt_id θ))).deriv

theorem contDiff_cylinder_radialPartial {g : PolarPoint → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (radialPartial g) :=
  contDiff_iff_contDiffAt.mpr (fun _ => contDiffAt_radialPartial hg.contDiffAt (by simp))

theorem contDiff_cylinder_angularPartial {g : PolarPoint → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (angularPartial g) :=
  contDiff_iff_contDiffAt.mpr (fun _ => contDiffAt_angularPartial hg.contDiffAt (by simp))

theorem deriv_cylinder_mixed_slice {g : PolarPoint → ℝ} (hg : ContDiff ℝ ∞ g) (x θ : ℝ) :
    deriv (fun y : ℝ => deriv (fun t : ℝ => g (y, t)) θ) x =
      radialPartial (angularPartial g) (x, θ) := by
  have he : (fun y : ℝ => deriv (fun t : ℝ => g (y, t)) θ) =
      fun y : ℝ => angularPartial g (y, θ) :=
    funext (fun y => deriv_cylinder_angular_slice (hg.differentiable (by simp)) y θ)
  rw [he]
  exact deriv_cylinder_radial_slice ((contDiff_cylinder_angularPartial hg).differentiable (by simp)) x θ

def cylinderWindow (x : ℝ) : Set PolarPoint := Ioc x (x + 1) ×ˢ Ioc 0 Real.pi

def cylinderWindowMeasure (x : ℝ) : Measure PolarPoint := volume.restrict (cylinderWindow x)

def cylinderWindowL2Norm (x : ℝ) (g : PolarPoint → ℝ) : ℝ :=
  (eLpNorm g 2 (cylinderWindowMeasure x)).toReal

theorem cylinderWindowMeasure_eq_prod (x : ℝ) :
    cylinderWindowMeasure x =
      (volume.restrict (Ioc x (x + 1))).prod (volume.restrict (Ioc 0 Real.pi)) := by
  rw [Measure.prod_restrict, cylinderWindowMeasure, cylinderWindow, Measure.volume_eq_prod]

/-- The window is a restriction in the first coordinate of the material
cylinder measure `volume.restrict (univ ×ˢ Ioc 0 π)`. -/
theorem cylinderWindowMeasure_eq_restrict_strip (x : ℝ) :
    cylinderWindowMeasure x =
      (volume.restrict ((univ : Set ℝ) ×ˢ Ioc 0 Real.pi)).restrict
        (Ioc x (x + 1) ×ˢ (univ : Set ℝ)) := by
  rw [cylinderWindowMeasure, Measure.restrict_restrict (measurableSet_Ioc.prod MeasurableSet.univ)]
  congr 1
  ext p
  simp [cylinderWindow]

theorem cylinderWindowMeasure_univ (x : ℝ) :
    cylinderWindowMeasure x univ = ENNReal.ofReal Real.pi := by
  rw [cylinderWindowMeasure, Measure.restrict_apply_univ, cylinderWindow, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioc]
  have hlen : x + 1 - x = 1 := by ring
  rw [hlen, sub_zero, ENNReal.ofReal_one, one_mul]

private theorem continuous_integrableOn_cylinderWindow {g : PolarPoint → ℝ}
    (hg : Continuous g) (x : ℝ) : IntegrableOn g (cylinderWindow x) volume := by
  have hi : IntegrableOn g (Icc x (x + 1) ×ˢ Icc 0 Real.pi) volume :=
    hg.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  exact hi.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

theorem continuous_memLp_cylinderWindow {g : PolarPoint → ℝ} (hg : Continuous g) (x : ℝ) :
    MemLp g 2 (cylinderWindowMeasure x) :=
  (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr
    (continuous_integrableOn_cylinderWindow (hg.pow 2) x)

private theorem integral_angle_slice_abs_le {g : PolarPoint → ℝ} (hg : ContDiff ℝ ∞ g) (x : ℝ) :
    (∫ t in Ioc 0 Real.pi, |g (x, t)|) ≤
      (∫ p in cylinderWindow x, |g p|) + ∫ p in cylinderWindow x, |radialPartial g p| := by
  let μ := volume.restrict (Ioc x (x + 1))
  let ν := volume.restrict (Ioc 0 Real.pi)
  have hmeasure : μ.prod ν = cylinderWindowMeasure x := (cylinderWindowMeasure_eq_prod x).symm
  have hi : Integrable (fun p => |g p|) (μ.prod ν) := by
    rw [hmeasure]
    exact continuous_integrableOn_cylinderWindow hg.continuous.abs x
  have hid : Integrable (fun p => |radialPartial g p|) (μ.prod ν) := by
    rw [hmeasure]
    exact continuous_integrableOn_cylinderWindow (contDiff_cylinder_radialPartial hg).continuous.abs x
  have hslice : Integrable (fun t => |g (x, t)|) ν :=
    (hg.continuous.comp (continuous_const.prodMk continuous_id)).abs.integrableOn_Ioc
  have hpoint (t : ℝ) : |g (x, t)| ≤
      (∫ y, |g (y, t)| ∂μ) + ∫ y, |radialPartial g (y, t)| ∂μ := by
    have hgt : ContDiff ℝ ∞ (fun y : ℝ => g (y, t)) :=
      hg.comp (contDiff_id.prodMk contDiff_const)
    have h := abs_le_interval_average_add_deriv hgt
      (show x < x + 1 by linarith) (show x ∈ Icc x (x + 1) from ⟨le_rfl, by linarith⟩)
    have hlen : x + 1 - x = 1 := by ring
    simpa only [hlen, inv_one, one_mul,
      deriv_cylinder_radial_slice (hg.differentiable (by simp))] using h
  have h := integral_mono hslice (hi.integral_prod_right.add hid.integral_prod_right) hpoint
  change (∫ t, |g (x, t)| ∂ν) ≤
    ∫ t, ((∫ y, |g (y, t)| ∂μ) + ∫ y, |radialPartial g (y, t)| ∂μ) ∂ν at h
  rw [integral_add hi.integral_prod_right hid.integral_prod_right,
    ← integral_prod_symm (fun p => |g p|) hi,
    ← integral_prod_symm (fun p => |radialPartial g p|) hid, hmeasure] at h
  exact h

/-- The four actual local `L¹` terms controlling a point on the cylinder. -/
theorem abs_le_cylinderWindow_L1 {g : PolarPoint → ℝ} (hg : ContDiff ℝ ∞ g)
    (x θ : ℝ) (hθ : θ ∈ Icc 0 Real.pi) :
    |g (x, θ)| ≤ (∫ p in cylinderWindow x, |g p|) +
      (∫ p in cylinderWindow x, |radialPartial g p|) +
      (∫ p in cylinderWindow x, |angularPartial g p|) +
      ∫ p in cylinderWindow x, |radialPartial (angularPartial g) p| := by
  have hgx : ContDiff ℝ ∞ (fun t : ℝ => g (x, t)) :=
    hg.comp (contDiff_const.prodMk contDiff_id)
  have h := abs_le_interval_average_add_deriv hgx Real.pi_pos hθ
  simp only [sub_zero, deriv_cylinder_angular_slice (hg.differentiable (by simp))] at h
  have hπ : Real.pi⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.one_le_pi_div_two])
  have hfirst : 0 ≤ ∫ t in Ioc 0 Real.pi, |g (x, t)| := integral_nonneg (fun _ => abs_nonneg _)
  calc
    |g (x, θ)| ≤ Real.pi⁻¹ * (∫ t in Ioc 0 Real.pi, |g (x, t)|) +
        ∫ t in Ioc 0 Real.pi, |angularPartial g (x, t)| := h
    _ ≤ (∫ t in Ioc 0 Real.pi, |g (x, t)|) + ∫ t in Ioc 0 Real.pi, |angularPartial g (x, t)| := by
      exact add_le_add ((mul_le_mul_of_nonneg_right hπ hfirst).trans_eq (one_mul _)) le_rfl
    _ ≤ ((∫ p in cylinderWindow x, |g p|) + (∫ p in cylinderWindow x, |radialPartial g p|)) +
        ((∫ p in cylinderWindow x, |angularPartial g p|) +
          ∫ p in cylinderWindow x, |radialPartial (angularPartial g) p|) :=
      add_le_add (integral_angle_slice_abs_le hg x)
        (integral_angle_slice_abs_le (contDiff_cylinder_angularPartial hg) x)
    _ = _ := by ring

theorem integral_cylinderWindow_abs_le_L2 {g : PolarPoint → ℝ} (hg : Continuous g) (x : ℝ) :
    (∫ p in cylinderWindow x, |g p|) ≤ Real.sqrt Real.pi * cylinderWindowL2Norm x g := by
  let μ := cylinderWindowMeasure x
  let : IsFiniteMeasure μ := ⟨by simp only [μ, cylinderWindowMeasure_univ, ENNReal.ofReal_lt_top]⟩
  have hm : MemLp g 2 μ := continuous_memLp_cylinderWindow hg x
  have h1 : MemLp (fun _ : PolarPoint => (1 : ℝ)) (ENNReal.ofReal 2) μ := memLp_const 1
  have hm' : MemLp g (ENNReal.ofReal 2) μ := by simpa using hm
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two h1 hm'
  have hmass : (∫ _ : PolarPoint, ‖(1 : ℝ)‖ ^ (2 : ℝ) ∂μ) = Real.pi := by
    calc
      (∫ _ : PolarPoint, ‖(1 : ℝ)‖ ^ (2 : ℝ) ∂μ) = ∫ _ : PolarPoint, (1 : ℝ) ∂μ := by simp
      _ = (μ univ).toReal := by simp [integral_const, measureReal_def]
      _ = Real.pi := by
        change (cylinderWindowMeasure x univ).toReal = Real.pi
        rw [cylinderWindowMeasure_univ, ENNReal.toReal_ofReal Real.pi_pos.le]
  rw [hmass] at h
  have hnonneg : 0 ≤ ∫ p, ‖g p‖ ^ (2 : ℝ) ∂μ :=
    integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hnorm : (eLpNorm g 2 μ).toReal = (∫ p, ‖g p‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
    rw [hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
    have htwo : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
    rw [htwo, ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _), one_div]
  change (∫ p, |g p| ∂μ) ≤ Real.sqrt Real.pi * (eLpNorm g 2 μ).toReal
  rw [hnorm, Real.sqrt_eq_rpow]
  simpa only [norm_one, one_mul, Real.norm_eq_abs] using h

/-- A pointwise cylinder bound by actual local `L²` norms, with uniform
constant `√π`. Angular endpoints are included in the conclusion. -/
theorem abs_le_cylinderWindow_L2 {g : PolarPoint → ℝ} (hg : ContDiff ℝ ∞ g)
    (x θ : ℝ) (hθ : θ ∈ Icc 0 Real.pi) :
    |g (x, θ)| ≤ Real.sqrt Real.pi *
      (cylinderWindowL2Norm x g + cylinderWindowL2Norm x (radialPartial g) +
        cylinderWindowL2Norm x (angularPartial g) +
        cylinderWindowL2Norm x (radialPartial (angularPartial g))) := by
  have hrad := contDiff_cylinder_radialPartial hg
  have hang := contDiff_cylinder_angularPartial hg
  have hmix := contDiff_cylinder_radialPartial hang
  rw [mul_add, mul_add, mul_add]
  exact (abs_le_cylinderWindow_L1 hg x θ hθ).trans
    (add_le_add (add_le_add (add_le_add
      (integral_cylinderWindow_abs_le_L2 hg.continuous x)
      (integral_cylinderWindow_abs_le_L2 hrad.continuous x))
      (integral_cylinderWindow_abs_le_L2 hang.continuous x))
      (integral_cylinderWindow_abs_le_L2 hmix.continuous x))

end ContinuousFlexibility.Analysis
