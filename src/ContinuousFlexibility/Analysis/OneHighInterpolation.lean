import ContinuousFlexibility.Analysis.OneHighFrequencyNorms
import Mathlib.Analysis.Convex.Segment
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Interpolation with one high factor

Hölder's inequality gives log convexity of the concrete weighted Fourier `L²`
norms. Applying this to two frequency functions and then using the weighted
arithmetic-geometric mean inequality proves the segment estimate in Lemma 7.2(i).
The argument includes both segment endpoints and permits arbitrary real orders.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem ennreal_rpow_rpow_comm (x : ℝ≥0∞) (a b : ℝ) :
    (x ^ a) ^ b = (x ^ b) ^ a := by
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_comm]

private theorem eLpNorm_two_integral {μ : Measure Ω} {f : Ω → ℂ}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ = (∫⁻ ξ, ‖f ξ‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
  simpa only [ENNReal.toReal_ofNat] using
    eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num) hf

/-- Log convexity before passing from extended nonnegative reals to real norms. -/
theorem frequencyWeighted_eLpNorm_interpolate {μ : Measure Ω} {W : Ω → ℝ}
    {f : Ω → ℂ} (hW : AEMeasurable W μ) (hWpos : ∀ᵐ ξ ∂μ, 0 < W ξ)
    (hf : AEStronglyMeasurable f μ) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) (k m : ℝ) :
    eLpNorm (frequencyWeighted W (θ * k + (1 - θ) * m) f) 2 μ ≤
      eLpNorm (frequencyWeighted W k f) 2 μ ^ θ *
        eLpNorm (frequencyWeighted W m f) 2 μ ^ (1 - θ) := by
  have hk := frequencyWeighted_aestronglyMeasurable hW hf k
  have hm := frequencyWeighted_aestronglyMeasurable hW hf m
  have hi := frequencyWeighted_aestronglyMeasurable hW hf (θ * k + (1 - θ) * m)
  have hθ' : 0 ≤ 1 - θ := sub_nonneg.mpr hθ.2
  have hpoint :
      (fun ξ => ‖frequencyWeighted W (θ * k + (1 - θ) * m) f ξ‖ₑ ^ (2 : ℝ)) =ᵐ[μ]
        (fun ξ => (‖frequencyWeighted W k f ξ‖ₑ ^ (2 : ℝ)) ^ θ *
          (‖frequencyWeighted W m f ξ‖ₑ ^ (2 : ℝ)) ^ (1 - θ)) := by
    filter_upwards [hWpos] with ξ hξ
    rw [frequencyWeighted_enorm_interpolate hξ hθ k m,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    · exact ennreal_rpow_rpow_comm _ θ 2
    · exact ennreal_rpow_rpow_comm _ (1 - θ) 2
  have hint :
      (∫⁻ ξ, ‖frequencyWeighted W (θ * k + (1 - θ) * m) f ξ‖ₑ ^ (2 : ℝ) ∂μ) ≤
        (∫⁻ ξ, ‖frequencyWeighted W k f ξ‖ₑ ^ (2 : ℝ) ∂μ) ^ θ *
          (∫⁻ ξ, ‖frequencyWeighted W m f ξ‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 - θ) := by
    rw [lintegral_congr_ae hpoint]
    exact ENNReal.lintegral_mul_norm_pow_le (hk.enorm.pow_const (2 : ℝ))
      (hm.enorm.pow_const (2 : ℝ)) hθ.1 hθ' (by ring)
  rw [eLpNorm_two_integral hi, eLpNorm_two_integral hk, eLpNorm_two_integral hm]
  calc
    _ ≤ ((∫⁻ ξ, ‖frequencyWeighted W k f ξ‖ₑ ^ (2 : ℝ) ∂μ) ^ θ *
        (∫⁻ ξ, ‖frequencyWeighted W m f ξ‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 - θ)) ^
        (1 / (2 : ℝ)) := ENNReal.rpow_le_rpow hint (by norm_num)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      congr 1
      · exact ennreal_rpow_rpow_comm _ θ (1 / 2)
      · exact ennreal_rpow_rpow_comm _ (1 - θ) (1 / 2)

/-- Membership at the two endpoint orders implies membership at every order
on their segment, including either endpoint. -/
theorem frequencyWeighted_memLp_interpolate {μ : Measure Ω} {W : Ω → ℝ}
    {f : Ω → ℂ} (hW : AEMeasurable W μ) (hWpos : ∀ᵐ ξ ∂μ, 0 < W ξ)
    {k m θ : ℝ} (hk : MemLp (frequencyWeighted W k f) 2 μ)
    (hm : MemLp (frequencyWeighted W m f) 2 μ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
    MemLp (frequencyWeighted W (θ * k + (1 - θ) * m) f) 2 μ := by
  have hf := (frequencyWeighted_aestronglyMeasurable_iff hW hWpos k).mp
    hk.aestronglyMeasurable
  apply memLp_iff.mpr
  exact (frequencyWeighted_eLpNorm_interpolate hW hWpos hf hθ k m).trans_lt
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hθ.1 hk.ne)
      (ENNReal.rpow_lt_top_of_nonneg (sub_nonneg.mpr hθ.2) hm.ne))

/-- Log convexity of the finite weighted Sobolev norms. -/
theorem frequencySobolevNorm_logConvex {μ : Measure Ω} {W : Ω → ℝ} {f : Ω → ℂ}
    (hW : AEMeasurable W μ) (hWpos : ∀ᵐ ξ ∂μ, 0 < W ξ) {k m θ : ℝ}
    (hk : MemLp (frequencyWeighted W k f) 2 μ)
    (hm : MemLp (frequencyWeighted W m f) 2 μ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
    frequencySobolevNorm μ W (θ * k + (1 - θ) * m) f ≤
      frequencySobolevNorm μ W k f ^ θ * frequencySobolevNorm μ W m f ^ (1 - θ) := by
  have hf := (frequencyWeighted_aestronglyMeasurable_iff hW hWpos k).mp
    hk.aestronglyMeasurable
  have htop : eLpNorm (frequencyWeighted W k f) 2 μ ^ θ *
      eLpNorm (frequencyWeighted W m f) 2 μ ^ (1 - θ) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hθ.1 hk.ne)
      (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr hθ.2) hm.ne)
  have h := ENNReal.toReal_mono htop
    (frequencyWeighted_eLpNorm_interpolate hW hWpos hf hθ k m)
  simpa only [frequencySobolevNorm, ENNReal.toReal_mul, ← ENNReal.toReal_rpow] using h

/-- The two-function interpolation estimate, with the common segment
parameter displayed explicitly. There is no loss in either Sobolev order. -/
theorem frequencySobolevNorm_segment_product_le {μ : Measure Ω} {W : Ω → ℝ}
    {f g : Ω → ℂ} (hW : AEMeasurable W μ) (hWpos : ∀ᵐ ξ ∂μ, 0 < W ξ)
    {k l m n i j θ : ℝ}
    (hfk : MemLp (frequencyWeighted W k f) 2 μ)
    (hfm : MemLp (frequencyWeighted W m f) 2 μ)
    (hgl : MemLp (frequencyWeighted W l g) 2 μ)
    (hgn : MemLp (frequencyWeighted W n g) 2 μ)
    (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hi : i = θ * k + (1 - θ) * m) (hj : j = θ * l + (1 - θ) * n) :
    frequencySobolevNorm μ W i f * frequencySobolevNorm μ W j g ≤
      frequencySobolevNorm μ W k f * frequencySobolevNorm μ W l g +
        frequencySobolevNorm μ W m f * frequencySobolevNorm μ W n g := by
  have hf := frequencySobolevNorm_logConvex hW hWpos hfk hfm hθ
  have hg := frequencySobolevNorm_logConvex hW hWpos hgl hgn hθ
  rw [← hi] at hf
  rw [← hj] at hg
  have hfk0 := frequencySobolevNorm_nonneg μ W k f
  have hfm0 := frequencySobolevNorm_nonneg μ W m f
  have hgl0 := frequencySobolevNorm_nonneg μ W l g
  have hgn0 := frequencySobolevNorm_nonneg μ W n g
  have hθ' : 0 ≤ 1 - θ := sub_nonneg.mpr hθ.2
  calc
    _ ≤ (frequencySobolevNorm μ W k f ^ θ *
        frequencySobolevNorm μ W m f ^ (1 - θ)) *
        (frequencySobolevNorm μ W l g ^ θ *
          frequencySobolevNorm μ W n g ^ (1 - θ)) :=
      mul_le_mul hf hg (frequencySobolevNorm_nonneg μ W j g)
        (mul_nonneg (Real.rpow_nonneg hfk0 θ) (Real.rpow_nonneg hfm0 (1 - θ)))
    _ = (frequencySobolevNorm μ W k f * frequencySobolevNorm μ W l g) ^ θ *
        (frequencySobolevNorm μ W m f * frequencySobolevNorm μ W n g) ^ (1 - θ) := by
      rw [Real.mul_rpow hfk0 hgl0, Real.mul_rpow hfm0 hgn0]
      ring
    _ ≤ θ * (frequencySobolevNorm μ W k f * frequencySobolevNorm μ W l g) +
        (1 - θ) * (frequencySobolevNorm μ W m f * frequencySobolevNorm μ W n g) :=
      Real.geom_mean_le_arith_mean2_weighted hθ.1 hθ'
        (mul_nonneg hfk0 hgl0) (mul_nonneg hfm0 hgn0) (by ring)
    _ ≤ _ := by
      apply add_le_add
      · simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hθ.2 (mul_nonneg hfk0 hgl0)
      · simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (sub_le_self 1 hθ.1) (mul_nonneg hfm0 hgn0)

/-- The geometric-segment form of Lemma 7.2(i). -/
theorem frequencySobolevNorm_product_le_of_mem_segment {μ : Measure Ω} {W : Ω → ℝ}
    {f g : Ω → ℂ} (hW : AEMeasurable W μ) (hWpos : ∀ᵐ ξ ∂μ, 0 < W ξ)
    {k l m n i j : ℝ}
    (hfk : MemLp (frequencyWeighted W k f) 2 μ)
    (hfm : MemLp (frequencyWeighted W m f) 2 μ)
    (hgl : MemLp (frequencyWeighted W l g) 2 μ)
    (hgn : MemLp (frequencyWeighted W n g) 2 μ)
    (hseg : (i, j) ∈ segment ℝ (k, l) (m, n)) :
    frequencySobolevNorm μ W i f * frequencySobolevNorm μ W j g ≤
      frequencySobolevNorm μ W k f * frequencySobolevNorm μ W l g +
        frequencySobolevNorm μ W m f * frequencySobolevNorm μ W n g := by
  rw [segment_eq_image] at hseg
  obtain ⟨t, ht, heq⟩ := hseg
  have hi : (1 - t) * k + t * m = i := by
    simpa using congrArg Prod.fst heq
  have hj : (1 - t) * l + t * n = j := by
    simpa using congrArg Prod.snd heq
  apply frequencySobolevNorm_segment_product_le hW hWpos hfk hfm hgl hgn
    (θ := 1 - t) ⟨sub_nonneg.mpr ht.2, sub_le_self 1 ht.1⟩
  · nlinarith only [hi]
  · nlinarith only [hj]

end ContinuousFlexibility.Analysis
