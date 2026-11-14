module

public import ContinuousFlexibility.Analysis.N07aOpenStripPointwiseL1
public import ContinuousFlexibility.Analysis.N07aCanonicalJetNormBounds
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Uniform point evaluation by four L² jets on the actual canonical piece

The complete length-dependent constant is explicit, so it can be kept
inside a sampled subpower envelope in the normal estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff ENNReal

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07a_canonical_integral_abs_le_L2
    (hm : K.left m < K.right m) {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (canonicalMeasure S K m)) :
    (∫ p, |f p| ∂canonicalMeasure S K m) ≤
      Real.sqrt (Real.pi * (K.right m - K.left m)) *
        (eLpNorm f 2 (canonicalMeasure S K m)).toReal := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (p := (1 : ℝ≥0∞)) (q := 2) (by norm_num) hf.aestronglyMeasurable
  rw [n07a_canonicalMeasure_univ hm] at h
  norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat, div_one,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h
  have htop : eLpNorm f 2 (canonicalMeasure S K m) *
      ENNReal.ofReal (Real.pi * (K.right m - K.left m)) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top hf.eLpNorm_ne_top (by finiteness)
  have hh := ENNReal.toReal_mono htop h
  have he : (eLpNorm f 1 (canonicalMeasure S K m)).toReal =
      ∫ p, |f p| ∂canonicalMeasure S K m := by
    rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable,
      ← integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable]
    simp only [Real.norm_eq_abs]
  rw [he, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (mul_nonneg Real.pi_pos.le (sub_pos.mpr hm).le),
    ← Real.sqrt_eq_rpow, mul_comm] at hh
  exact hh

theorem n07a_inner_rectangle_integral_abs_le_L2
    (hm : K.left m < K.right m) {a b : ℝ}
    (ha : K.left m < a) (hb : b < K.right m)
    {f : PolarPoint → ℝ} (hf : MemLp f 2 (canonicalMeasure S K m)) :
    (∫ p in Ioc a b ×ˢ Ioc 0 Real.pi, |f p|) ≤
      Real.sqrt (Real.pi * (K.right m - K.left m)) *
        (eLpNorm f 2 (canonicalMeasure S K m)).toReal := by
  letI := n07a_canonicalMeasure_finite S K m
  have hi : IntegrableOn (fun p => |f p|)
      (Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi) volume :=
    (hf.integrable (by norm_num)).abs
  apply (setIntegral_mono_set hi (Eventually.of_forall fun _ => abs_nonneg _) ?_).trans
    (n07a_canonical_integral_abs_le_L2 hm hf)
  exact Eventually.of_forall fun p hp =>
    ⟨⟨ha.trans hp.1.1, hp.1.2.trans_lt hb⟩, hp.2⟩

theorem n07a_canonicalOpen_pointwise_L2
    (hm : K.left m < K.right m) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m))
    (hper : ∀ x ∈ Ioo (K.left m) (K.right m),
      Function.Periodic (fun θ => f (x, θ)) Real.pi)
    (h0 : MemLp f 2 (canonicalMeasure S K m))
    (hr : MemLp (radialPartial f) 2 (canonicalMeasure S K m))
    (ht : MemLp (angularPartial f) 2 (canonicalMeasure S K m))
    (hrt : MemLp (radialPartial (angularPartial f)) 2 (canonicalMeasure S K m))
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    |f p| ≤ (1 + 2 * (K.right m - K.left m)⁻¹) *
      Real.sqrt (Real.pi * (K.right m - K.left m)) *
        ((eLpNorm f 2 (canonicalMeasure S K m)).toReal +
          (eLpNorm (radialPartial f) 2 (canonicalMeasure S K m)).toReal +
          (eLpNorm (angularPartial f) 2 (canonicalMeasure S K m)).toReal +
          (eLpNorm (radialPartial (angularPartial f)) 2
            (canonicalMeasure S K m)).toReal) := by
  obtain ⟨a, b, ha, hb, hab, hx, hlen⟩ := n07a_inner_interval_half_length hp.1
  obtain ⟨θ, hθ, he⟩ := (hper p.1 hp.1).exists_mem_Ico₀ Real.pi_pos p.2
  have hpoint := n07a_openStrip_pointwise_L1 hf ha hb hab hx ⟨hθ.1, hθ.2.le⟩
  have hL0 : 0 < K.right m - K.left m := sub_pos.mpr hm
  have hL1 : (b - a)⁻¹ ≤ 2 * (K.right m - K.left m)⁻¹ := by
    calc
      _ ≤ ((K.right m - K.left m) / 2)⁻¹ := inv_anti₀ (half_pos hL0) hlen
      _ = _ := by rw [inv_div, div_eq_mul_inv]
  let N := (eLpNorm f 2 (canonicalMeasure S K m)).toReal +
    (eLpNorm (radialPartial f) 2 (canonicalMeasure S K m)).toReal +
    (eLpNorm (angularPartial f) 2 (canonicalMeasure S K m)).toReal +
    (eLpNorm (radialPartial (angularPartial f)) 2 (canonicalMeasure S K m)).toReal
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hsum := add_le_add (add_le_add (add_le_add
    (n07a_inner_rectangle_integral_abs_le_L2 hm ha hb h0)
    (n07a_inner_rectangle_integral_abs_le_L2 hm ha hb hr))
    (n07a_inner_rectangle_integral_abs_le_L2 hm ha hb ht))
    (n07a_inner_rectangle_integral_abs_le_L2 hm ha hb hrt)
  have hsum' : _ ≤ Real.sqrt (Real.pi * (K.right m - K.left m)) * N :=
    hsum.trans_eq (by dsimp only [N]; ring)
  change f p = f (p.1, θ) at he
  rw [he]
  apply (hpoint.trans (mul_le_mul_of_nonneg_left hsum'
    (add_nonneg zero_le_one (inv_nonneg.mpr (sub_pos.mpr hab).le)))).trans
  exact (mul_le_mul_of_nonneg_right (add_le_add le_rfl hL1)
    (mul_nonneg (Real.sqrt_nonneg _) hN)).trans_eq (mul_assoc _ _ _).symm

end ContinuousFlexibility.Analysis
