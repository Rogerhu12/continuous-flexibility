import ContinuousFlexibility.Analysis.N01aOpticalVariation
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A quantitative interval on which the optical control is active

A lower travel margin forces the actual radicand to reach a positive
level. A bound for its first derivative supplies an interval of controlled
length around such a point. Integrating the positive variation kernel on
that interval gives a lower bound for the normalizing denominator.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

theorem n01aOpticalRadicand_lipschitz {q : ℝ → ℝ} {l h K : ℝ}
    (hq : ∀ r ∈ Icc l h, DifferentiableAt ℝ q r)
    (hbound : ∀ r ∈ Icc l h, |deriv q r| ≤ K)
    {x y : ℝ} (hx : x ∈ Icc l h) (hy : y ∈ Icc l h) :
    |q y - q x| ≤ K * |y - x| := by
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_deriv_le hq
      (fun r hr => by simpa only [Real.norm_eq_abs] using hbound r hr)
      convex_Icc hx hy

/-- A radicand peak yields an interval strictly inside both turning points.
Only its actual first derivative and its endpoint values enter the estimate. -/
theorem n01aOpticalPeak_interval {q : ℝ → ℝ} {l h δ K p : ℝ}
    (hδ : 0 < δ) (hK : 0 < K)
    (hq : ∀ r ∈ Icc l h, DifferentiableAt ℝ q r)
    (hbound : ∀ r ∈ Icc l h, |deriv q r| ≤ K)
    (hleft : q l = 0) (hright : q h = 0)
    (hp : p ∈ Icc l h) (hpeak : 4 * δ ≤ q p) :
    l < p - δ / K ∧ p + δ / K < h ∧
      ∀ r ∈ Icc (p - δ / K) (p + δ / K), 2 * δ ≤ q r := by
  have hlh : l ≤ h := hp.1.trans hp.2
  have hdistL := n01aOpticalRadicand_lipschitz hq hbound
    (left_mem_Icc.mpr hlh) hp
  rw [hleft, sub_zero, abs_of_nonneg (sub_nonneg.mpr hp.1)] at hdistL
  have hdistR := n01aOpticalRadicand_lipschitz hq hbound hp
    (right_mem_Icc.mpr hlh)
  rw [hright, zero_sub, abs_neg, abs_of_nonneg (sub_nonneg.mpr hp.2)] at hdistR
  have hqL : q p ≤ K * (p - l) := (le_abs_self _).trans hdistL
  have hqR : q p ≤ K * (h - p) := (le_abs_self _).trans hdistR
  have hρ : 0 < δ / K := div_pos hδ hK
  have hρL : δ / K < p - l := (div_lt_iff₀ hK).mpr (by nlinarith)
  have hρR : δ / K < h - p := (div_lt_iff₀ hK).mpr (by nlinarith)
  have hL : l < p - δ / K := by linarith
  have hR : p + δ / K < h := by linarith
  refine ⟨hL, hR, fun r hr => ?_⟩
  have hr' : r ∈ Icc l h := ⟨hL.le.trans hr.1, hr.2.trans hR.le⟩
  have hdr := n01aOpticalRadicand_lipschitz hq hbound hp hr'
  have habs : |r - p| ≤ δ / K := abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hcancel : K * (δ / K) = δ := by field_simp [hK.ne']
  have hosc : |q r - q p| ≤ δ := by
    calc
      |q r - q p| ≤ K * |r - p| := hdr
      _ ≤ K * (δ / K) := mul_le_mul_of_nonneg_left habs hK.le
      _ = δ := hcancel
  have hlo := (abs_le.mp hosc).1
  linarith

/-- The travel margin forces a peak above four times the cutoff scale. -/
theorem exists_n01aOpticalPeak {q : ℝ → ℝ} {l h L δ : ℝ}
    (hlh : l < h) (hL : 0 < L) (hwidth : h - l ≤ L) (hδ : 0 < δ)
    (hq : ContinuousOn q (Icc l h))
    (htravel : 4 * L * Real.sqrt δ ≤ ∫ r in l..h, Real.sqrt (q r)) :
    ∃ p ∈ Icc l h, 4 * δ ≤ q p := by
  by_contra hex
  push_neg at hex
  have hint := hq.sqrt.intervalIntegrable_of_Icc (μ := volume) hlh.le
  have hconst : Continuous (fun _ : ℝ => Real.sqrt (4 * δ)) := continuous_const
  have hupper := intervalIntegral.integral_mono_on (μ := volume) hlh.le hint
    (hconst.intervalIntegrable l h)
    (fun r hr => Real.sqrt_le_sqrt (hex r hr).le)
  have hsqrt : Real.sqrt (4 * δ) = 2 * Real.sqrt δ := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [intervalIntegral.integral_const, smul_eq_mul, hsqrt] at hupper
  have hupperL := mul_le_mul_of_nonneg_right hwidth
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg δ))
  have hpositive := mul_pos hL (Real.sqrt_pos.mpr hδ)
  nlinarith

theorem n01aOpticalKernel_lower {w : ℝ → ℝ} {δ K β r : ℝ}
    (hδ : 0 < δ) (hK : 0 < K) (hr : 0 < r) (hrβ : r ≤ β)
    (hlevel : 2 * δ ≤ n01aOpticalRadicand w r)
    (hupper : n01aOpticalRadicand w r ≤ K ^ 2) :
    1 / (β * K) ≤ n01aOpticalKernel w δ r := by
  have hq : 0 < n01aOpticalRadicand w r := (mul_pos (by norm_num) hδ).trans_le hlevel
  have hβ : 0 < β := hr.trans_le hrβ
  have hcutoff : 1 ≤ n01aOpticalCutoff (n01aOpticalRadicand w r / δ) :=
    one_le_n01aOpticalCutoff ((le_div_iff₀ hδ).mpr hlevel)
  have hsqrt : Real.sqrt (n01aOpticalRadicand w r) ≤ K :=
    Real.sqrt_le_iff.mpr ⟨hK.le, hupper⟩
  have hdenom : 0 < r * Real.sqrt (n01aOpticalRadicand w r) :=
    mul_pos hr (Real.sqrt_pos.mpr hq)
  have hdenom_upper : r * Real.sqrt (n01aOpticalRadicand w r) ≤ β * K :=
    mul_le_mul hrβ hsqrt (Real.sqrt_nonneg _) hβ.le
  exact (one_div_le_one_div_of_le hdenom hdenom_upper).trans
    (div_le_div_of_nonneg_right hcutoff hdenom.le)

/-- An explicit lower bound for the absolute raw first variation. -/
theorem n01aOpticalRawControl_variation_lower {w : ℝ → ℝ} {l h δ K β p : ℝ}
    (hl : 0 < l) (hδ : 0 < δ) (hK : 0 < K) (hhβ : h ≤ β)
    (hw : ContDiff ℝ ∞ w) (hpos : ∀ r ∈ Icc l h, 0 < w r)
    (hrootL : deriv w l = 0) (hrootR : deriv w h = 0)
    (hbound : ∀ r ∈ Icc l h, |deriv (n01aOpticalRadicand w) r| ≤ K)
    (hupper : ∀ r ∈ Icc l h, n01aOpticalRadicand w r ≤ K ^ 2)
    (hp : p ∈ Icc l h) (hpeak : 4 * δ ≤ n01aOpticalRadicand w p) :
    δ / (β * K ^ 2) ≤ (1 / 2 : ℝ) * ∫ r in l..h, n01aOpticalKernel w δ r := by
  have hq : ∀ r ∈ Icc l h, DifferentiableAt ℝ (n01aOpticalRadicand w) r :=
    fun r hr => (contDiffAt_n01aOpticalRadicand hw
      (hl.trans_le hr.1).ne' (hpos r hr).ne').differentiableAt (by simp)
  obtain ⟨hL, hR, hband⟩ := n01aOpticalPeak_interval hδ hK hq hbound
    (n01aOpticalRadicand_zero hrootL) (n01aOpticalRadicand_zero hrootR) hp hpeak
  have hρ : 0 < δ / K := div_pos hδ hK
  have hbandle : p - δ / K ≤ p + δ / K := by linarith
  have hlh : l < h := hL.trans_le (hbandle.trans hR.le)
  have hβ : 0 < β := (hl.trans hlh).trans_le hhβ
  have hsub : Icc (p - δ / K) (p + δ / K) ⊆ Icc l h :=
    Icc_subset_Icc hL.le hR.le
  have hc := continuousOn_n01aOpticalKernel hl hδ hw hpos
  have hint := hc.intervalIntegrable_of_Icc (μ := volume) hlh.le
  have hsmall := (hc.mono hsub).intervalIntegrable_of_Icc (μ := volume) hbandle
  have hconst : Continuous (fun _ : ℝ => 1 / (β * K)) := continuous_const
  have hlo := intervalIntegral.integral_mono_on (μ := volume) hbandle
    (hconst.intervalIntegrable _ _) hsmall (fun r hr =>
      n01aOpticalKernel_lower hδ hK (hl.trans_le (hsub hr).1)
        ((hsub hr).2.trans hhβ) (hband r hr) (hupper r (hsub hr)))
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc l h)] n01aOpticalKernel w δ :=
    (ae_restrict_iff' measurableSet_Ioc).mpr <| ae_of_all volume
      (fun r hr => n01aOpticalKernel_nonneg δ (hl.trans hr.1).le)
  have hext := intervalIntegral.integral_mono_interval hL.le hbandle hR.le hnonneg hint
  rw [intervalIntegral.integral_const, smul_eq_mul] at hlo
  have heq : (p + δ / K - (p - δ / K)) * (1 / (β * K)) =
      2 * (δ / (β * K ^ 2)) := by
    field_simp [hβ.ne', hK.ne']
    <;> ring
  rw [heq] at hlo
  linarith

end ContinuousFlexibility.Statements
