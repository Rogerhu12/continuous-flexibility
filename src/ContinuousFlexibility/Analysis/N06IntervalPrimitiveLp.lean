import ContinuousFlexibility.Analysis.N06WeakModeRegularity
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# L2 stability of primitives on the unit interval

The integral primitive takes an L2 error to a uniformly bounded error with
the same bound on `[0,1]`. Applied successively to the first and second
derivatives, this gives a smooth approximation without endpoint conditions.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

set_option backward.isDefEq.respectTransparency false

/-- Interval integrals on the unit interval are integrals for its open-interior
measure; endpoints have zero Lebesgue mass. -/
theorem n06_unit_intervalIntegral_eq {f : ℝ → ℝ} :
    (∫ x in (0 : ℝ)..1, f x) = ∫ x, f x ∂volume.restrict (Ioo (0 : ℝ) 1) := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

/-- On a unit-mass interval the L1 norm is bounded by the L2 norm. -/
theorem n06_unit_integral_norm_le {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    (∫ x in (0 : ℝ)..1, ‖f x‖) ≤ ‖hf.toLp f‖ := by
  letI : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ⟨by simp [Measure.restrict_apply_univ, Real.volume_Ioo]⟩
  rw [n06_unit_intervalIntegral_eq, ← lpNorm_one_eq_integral_norm hf.aestronglyMeasurable,
    ← toReal_eLpNorm, Lp.norm_toLp]
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2))

/-- The actual primitive of an L2 function is bounded pointwise by its L2 norm
at every point of the closed unit interval. -/
theorem n06_unit_primitive_norm_le {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖∫ t in (0 : ℝ)..x, f t‖ ≤ ‖hf.toLp f‖ := by
  have hi : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr
      (interval_memLp_integrable hf)
  calc
    ‖∫ t in (0 : ℝ)..x, f t‖ ≤ ∫ t in (0 : ℝ)..x, ‖f t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hx.1
    _ ≤ ∫ t in (0 : ℝ)..1, ‖f t‖ :=
      intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
        (Eventually.of_forall fun _ => norm_nonneg _) hi.norm
    _ ≤ ‖hf.toLp f‖ := n06_unit_integral_norm_le hf

/-- A uniform almost-everywhere bound is an L2 norm bound on the unit interval. -/
theorem n06_unit_toLp_norm_le {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1), ‖f x‖ ≤ C) :
    ‖hf.toLp f‖ ≤ C := by
  have hbound : eLpNorm f 2 (volume.restrict (Ioo (0 : ℝ) 1)) ≤ ENNReal.ofReal C := by
    simpa [Measure.restrict_apply_univ, Real.volume_Ioo] using
      (eLpNorm_le_of_ae_bound (p := 2) hf.aestronglyMeasurable hb)
  rw [Lp.norm_toLp]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    (ENNReal.toReal_ofReal hC)

/-- The smooth primitive with prescribed value at zero. -/
def n06SmoothPrimitive (C : ℝ) (g : ℝ → ℝ) : ℝ → ℝ :=
  fun x => C + ∫ t in (0 : ℝ)..x, g t

theorem n06SmoothPrimitive_hasDerivAt (C : ℝ) {g : ℝ → ℝ}
    (hg : Continuous g) (x : ℝ) :
    HasDerivAt (n06SmoothPrimitive C g) (g x) x := by
  change HasDerivAt (fun y : ℝ => C + ∫ t in (0 : ℝ)..y, g t) (g x) x
  exact (hg.integral_hasStrictDerivAt 0 x).hasDerivAt.const_add C

theorem n06SmoothPrimitive_deriv (C : ℝ) {g : ℝ → ℝ}
    (hg : Continuous g) : deriv (n06SmoothPrimitive C g) = g :=
  funext fun x => (n06SmoothPrimitive_hasDerivAt C hg x).deriv

theorem n06SmoothPrimitive_continuous (C : ℝ) {g : ℝ → ℝ}
    (hg : Continuous g) : Continuous (n06SmoothPrimitive C g) :=
  (show Differentiable ℝ (n06SmoothPrimitive C g) from
    fun x => (n06SmoothPrimitive_hasDerivAt C hg x).differentiableAt).continuous

theorem n06SmoothPrimitive_contDiff (C : ℝ) {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (n06SmoothPrimitive C g) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (n06SmoothPrimitive_hasDerivAt C hg.continuous x).differentiableAt, ?_⟩
  rw [n06SmoothPrimitive_deriv C hg.continuous]
  exact hg

/-- Comparing a smooth primitive with an absolutely continuous function uses
the actual derivative, including both endpoint values. -/
theorem n06_primitive_sub_norm_le {v g : ℝ → ℝ}
    (hv : AbsolutelyContinuousOnInterval v 0 1) (hg : Continuous g)
    (hvd : MemLp (deriv v) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖n06SmoothPrimitive (v 0) g x - v x‖ ≤
      ‖(interval_memLp_of_continuous hg).toLp g - hvd.toLp (deriv v)‖ := by
  have hsub : uIcc (0 : ℝ) x ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le hx.1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hx.2
  have hvx : AbsolutelyContinuousOnInterval v 0 x := hv.mono hsub
  have hFTC := hvx.integral_deriv_eq_sub
  have heq : n06SmoothPrimitive (v 0) g x - v x =
      ∫ t in (0 : ℝ)..x, (g - deriv v) t := by
    simp only [Pi.sub_apply]
    rw [intervalIntegral.integral_sub (hg.intervalIntegrable 0 x)
      hvx.intervalIntegrable_deriv, hFTC]
    dsimp only [n06SmoothPrimitive]
    ring
  rw [heq]
  have hg₂ : MemLp g 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
    interval_memLp_of_continuous hg
  have hb := n06_unit_primitive_norm_le (hg₂.sub hvd) hx
  rw [MemLp.toLp_sub hg₂ hvd] at hb
  exact hb

/-- The uniform primitive error also bounds its L2 distance. -/
theorem n06_primitive_toLp_sub_norm_le {v g : ℝ → ℝ}
    (hv : AbsolutelyContinuousOnInterval v 0 1) (hg : Continuous g)
    (hv₂ : MemLp v 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hvd : MemLp (deriv v) 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ‖(interval_memLp_of_continuous (n06SmoothPrimitive_continuous (v 0) hg)).toLp
          (n06SmoothPrimitive (v 0) g) - hv₂.toLp v‖ ≤
      ‖(interval_memLp_of_continuous hg).toLp g - hvd.toLp (deriv v)‖ := by
  have hP : Continuous (n06SmoothPrimitive (v 0) g) :=
    n06SmoothPrimitive_continuous (v 0) hg
  have hP₂ : MemLp (n06SmoothPrimitive (v 0) g) 2
      (volume.restrict (Ioo (0 : ℝ) 1)) := interval_memLp_of_continuous hP
  have hb : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1),
      ‖(n06SmoothPrimitive (v 0) g - v) x‖ ≤
        ‖(interval_memLp_of_continuous hg).toLp g - hvd.toLp (deriv v)‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact n06_primitive_sub_norm_le hv hg hvd (mem_Icc_of_Ioo hx)
  have hn := n06_unit_toLp_norm_le (hP₂.sub hv₂) (norm_nonneg _) hb
  rw [MemLp.toLp_sub hP₂ hv₂] at hn
  exact hn

end ContinuousFlexibility.Analysis
