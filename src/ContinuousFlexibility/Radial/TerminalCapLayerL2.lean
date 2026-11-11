import ContinuousFlexibility.Radial.TerminalCapLift
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Terminal source layers in the actual radial weighted measure

The density 12 w / r² bounds the mass of the cutoff layer by its physical
length. Continuous fields supported on that layer therefore belong to
the actual radial L² space, with an explicit seminorm bound. The final
theorem applies this to the genuine Jacobi source from TerminalCapLift
and derives its envelope from the original coefficient and jet bounds.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff ENNReal

/-- The outer restriction in the radial measure can only decrease the
mass of the physical layer; the density estimate supplies the bound. -/
theorem terminalCapLayer_measure_le (D : Statements.ReferenceData)
    {a b P : ℝ} (hP : 0 ≤ P)
    (hρ : ∀ r ∈ Icc a b, 12 * D.w r / r ^ 2 ≤ P) :
    Statements.radialHilbertMeasure D (Icc a b) ≤ ENNReal.ofReal (P * (b - a)) := by
  rw [Statements.radialHilbertMeasure, withDensity_apply _ measurableSet_Icc]
  calc
    _ ≤ ∫⁻ _ in Icc a b, ENNReal.ofReal P ∂volume.restrict (Statements.radialCore D) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact ENNReal.ofReal_le_ofReal (hρ r hr)
    _ = ENNReal.ofReal P * (volume.restrict (Statements.radialCore D)) (Icc a b) :=
      setLIntegral_const _ _
    _ ≤ ENNReal.ofReal P * volume (Icc a b) :=
      mul_le_mul_of_nonneg_left (Measure.restrict_apply_le (μ := volume)
        (Statements.radialCore D) (Icc a b)) zero_le
    _ = ENNReal.ofReal (P * (b - a)) := by
      rw [Real.volume_Icc, ← ENNReal.ofReal_mul hP]

/-- A coefficient bound and a positive left radius give the density
bound; it is not supplied as a measure-comparison hypothesis. -/
theorem terminalCapLayer_density_le (D : Statements.ReferenceData)
    {a b W : ℝ} (ha : 0 < a) (hW : 0 ≤ W)
    (hw : ∀ r ∈ Icc a b, |D.w r| ≤ W) :
    ∀ r ∈ Icc a b, 12 * D.w r / r ^ 2 ≤ 12 * W / a ^ 2 := by
  intro r hr
  have hr₀ : 0 < r := ha.trans_le hr.1
  calc
    _ ≤ 12 * W / r ^ 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hw r hr)) (by norm_num))
        (sq_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hW)
      (sq_pos_of_pos ha) ((sq_le_sq₀ ha.le hr₀.le).mpr hr.1)

theorem terminalCapLayer_measure_le_of_coefficient (D : Statements.ReferenceData)
    {a b W : ℝ} (ha : 0 < a) (hW : 0 ≤ W)
    (hw : ∀ r ∈ Icc a b, |D.w r| ≤ W) :
    Statements.radialHilbertMeasure D (Icc a b) ≤
      ENNReal.ofReal ((12 * W / a ^ 2) * (b - a)) :=
  terminalCapLayer_measure_le D (by positivity) (terminalCapLayer_density_le D ha hW hw)

/-- Pointwise control on a genuine finite physical layer constructs
membership in L² and the quantitative seminorm bound simultaneously. -/
theorem terminalCapLayer_memLp_eLpNorm (D : Statements.ReferenceData)
    {a b P M : ℝ} (hab : a ≤ b) (hP : 0 ≤ P) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a b))
    (hsupport : Function.support f ⊆ Icc a b)
    (hρ : ∀ r ∈ Icc a b, 12 * D.w r / r ^ 2 ≤ P)
    (hbound : ∀ r ∈ Icc a b, |f r| ≤ M) :
    MemLp f 2 (Statements.radialHilbertMeasure D) ∧
      eLpNorm f 2 (Statements.radialHilbertMeasure D) ≤
        ENNReal.ofReal (M * sqrt (P * (b - a))) := by
  let μ : Measure ℝ := Statements.radialHilbertMeasure D
  have hi : (Icc a b).indicator f = f := by
    funext r
    by_cases hr : r ∈ Icc a b
    · rw [indicator_of_mem hr]
    · rw [indicator_of_notMem hr]
      symm
      by_contra hn
      exact hr (hsupport hn)
  have hmeas : AEStronglyMeasurable f (μ.restrict (Icc a b)) :=
    hf.aestronglyMeasurable measurableSet_Icc
  have hb : ∀ᵐ r ∂μ.restrict (Icc a b), ‖f r‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    simpa only [Real.norm_eq_abs] using hbound r hr
  have hraw : eLpNorm f 2 (μ.restrict (Icc a b)) ≤
      μ (Icc a b) ^ (1 / 2 : ℝ) * ENNReal.ofReal M := by
    simpa only [Measure.restrict_apply_univ,
      show (2 : ℝ≥0∞).toReal⁻¹ = (1 / 2 : ℝ) by norm_num] using
      (eLpNorm_le_of_ae_bound (p := 2) hmeas hb)
  have hmass := terminalCapLayer_measure_le D hP hρ
  have hmass₀ : 0 ≤ P * (b - a) := mul_nonneg hP (sub_nonneg.mpr hab)
  have hnorm : eLpNorm f 2 μ ≤ ENNReal.ofReal (M * sqrt (P * (b - a))) := by
    calc
      _ = eLpNorm f 2 (μ.restrict (Icc a b)) := by
        rw [← eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc, hi]
      _ ≤ μ (Icc a b) ^ (1 / 2 : ℝ) * ENNReal.ofReal M := hraw
      _ ≤ ENNReal.ofReal (P * (b - a)) ^ (1 / 2 : ℝ) * ENNReal.ofReal M :=
        mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow hmass (by norm_num)) zero_le
      _ = ENNReal.ofReal (sqrt (P * (b - a))) * ENNReal.ofReal M := by
        rw [ENNReal.ofReal_rpow_of_nonneg hmass₀ (by norm_num), ← sqrt_eq_rpow]
      _ = ENNReal.ofReal (M * sqrt (P * (b - a))) := by
        rw [← ENNReal.ofReal_mul (sqrt_nonneg _)]
        congr 1
        ring
  exact ⟨hnorm.trans_lt ENNReal.ofReal_lt_top, hnorm⟩

theorem terminalCapResidual_continuous (lam : ℝ) {w χ u : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u) :
    Continuous (terminalCapResidual lam w χ u) := by
  have hwd : Continuous (deriv w) := (contDiff_infty_iff_deriv.mp hw).2.continuous
  have hχd : Continuous (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2.continuous
  have hχdd : Continuous (deriv (deriv χ)) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hχ).2).2.continuous
  have hud : Continuous (deriv u) := (contDiff_infty_iff_deriv.mp hu).2.continuous
  unfold terminalCapResidual
  exact ((((continuous_const.mul hw.continuous).mul hχd).mul hud).add
    (((hwd.mul hχd).add (hw.continuous.mul hχdd)).mul hu.continuous)).neg.div_const _

theorem terminalCapHilbertSource_continuousOn (lam : ℝ) {w χ u : ℝ → ℝ} {K : Set ℝ}
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u)
    (hw₀ : ∀ r ∈ K, w r ≠ 0) :
    ContinuousOn (terminalCapHilbertSource lam w χ u) K := by
  unfold terminalCapHilbertSource
  exact ((continuousOn_id.pow 2).div (continuousOn_const.mul hw.continuous.continuousOn)
    (fun r hr => mul_ne_zero (by norm_num) (hw₀ r hr))).mul
      (terminalCapResidual_continuous lam hw hχ hu).continuousOn

def terminalCapSourceEnvelope (lam R W W₁ C₁ C₂ A B σ : ℝ) : ℝ :=
  R * ((2 * W * C₁ * B + (W₁ * C₁ + W * C₂) * A) / sqrt lam) * exp (-σ)

/-- The normalized actual Hilbert source belongs to the original radial
L² space. The source envelope is proved from the raw coefficient and jet
bounds; the layer mass is proved from the same coefficient and radius. -/
theorem terminalCapHilbertSource_layer_L2 (D : Statements.ReferenceData)
    {a b lam R W W₁ C₁ C₂ A B σ : ℝ} {χ u : ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hlam : 0 < lam) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hw : ContDiff ℝ ∞ D.w) (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u)
    (hw₀ : ∀ r ∈ Icc a b, D.w r ≠ 0)
    (hlayer : tsupport (deriv χ) ⊆ Icc a b)
    (hreciprocal : ∀ r ∈ Icc a b, |r ^ 2 / (12 * D.w r)| ≤ R)
    (hcoefficient : ∀ r ∈ Icc a b, |D.w r| ≤ W)
    (hcoefficient₁ : ∀ r ∈ Icc a b, |deriv D.w r| ≤ W₁)
    (hcutoff₁ : ∀ r ∈ Icc a b, |deriv χ r| ≤ C₁)
    (hcutoff₂ : ∀ r ∈ Icc a b, |deriv (deriv χ) r| ≤ C₂)
    (hheight : ∀ r ∈ Icc a b, |u r| ≤ A * exp (-σ))
    (hderivative : ∀ r ∈ Icc a b, |deriv u r| ≤ B * exp (-σ)) :
    MemLp (terminalCapHilbertSource lam D.w χ u) 2 (Statements.radialHilbertMeasure D) ∧
      eLpNorm (terminalCapHilbertSource lam D.w χ u) 2 (Statements.radialHilbertMeasure D) ≤
        ENNReal.ofReal (terminalCapSourceEnvelope lam R W W₁ C₁ C₂ A B σ *
          sqrt ((12 * W / a ^ 2) * (b - a))) := by
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hR : 0 ≤ R := (abs_nonneg _).trans (hreciprocal a haI)
  have hW : 0 ≤ W := (abs_nonneg _).trans (hcoefficient a haI)
  have hW₁ : 0 ≤ W₁ := (abs_nonneg _).trans (hcoefficient₁ a haI)
  have hC₁ : 0 ≤ C₁ := (abs_nonneg _).trans (hcutoff₁ a haI)
  have hC₂ : 0 ≤ C₂ := (abs_nonneg _).trans (hcutoff₂ a haI)
  have hM : 0 ≤ terminalCapSourceEnvelope lam R W W₁ C₁ C₂ A B σ := by
    dsimp only [terminalCapSourceEnvelope]
    positivity
  apply terminalCapLayer_memLp_eLpNorm D hab (by positivity) hM
    (terminalCapHilbertSource lam D.w χ u)
    (terminalCapHilbertSource_continuousOn lam hw hχ hu hw₀)
    ((terminalCapHilbertSource_support lam D.w χ u).trans hlayer)
    (terminalCapLayer_density_le D ha hW hcoefficient)
  intro r hr
  exact terminalCapHilbertSource_abs_le hlam (hreciprocal r hr)
    (hcoefficient r hr) (hcoefficient₁ r hr) (hcutoff₁ r hr) (hcutoff₂ r hr)
    (hheight r hr) (hderivative r hr)

end ContinuousFlexibility.Radial
