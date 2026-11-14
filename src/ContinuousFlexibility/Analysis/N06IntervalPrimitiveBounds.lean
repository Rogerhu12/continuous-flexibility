module

public import ContinuousFlexibility.Analysis.N06IntervalPrimitiveLp
public import ContinuousFlexibility.Radial.R11bModeL2

/-!
# Primitive bounds on an actual finite canonical interval

The constants below are the norm of the constant one in the original
interval L2 space. Cauchy--Schwarz therefore gives both the uniform
primitive bound and the reverse passage from a uniform bound to an L2
bound without normalizing or changing the recorded interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The finite L2 norm of one on the actual open interval. -/
def n06IntervalL2Unit (a b : ℝ) : ℝ :=
  ‖(interval_memLp_of_continuous (a := a) (b := b)
    (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))).toLp (fun _ => (1 : ℝ))‖

theorem n06IntervalL2Unit_nonneg (a b : ℝ) : 0 ≤ n06IntervalL2Unit a b := norm_nonneg _

/-- Cauchy--Schwarz with the constant one uses precisely the original L2
norm, including the actual interval length. -/
theorem n06_interval_integral_norm_le {a b : ℝ} {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo a b))) :
    (∫ x, ‖f x‖ ∂volume.restrict (Ioo a b)) ≤
      n06IntervalL2Unit a b * ‖hf.toLp f‖ := by
  have h1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Ioo a b)) :=
    interval_memLp_of_continuous continuous_const
  have hinner := real_inner_le_norm (hf.norm.toLp (fun x => ‖f x‖))
    (h1.toLp (fun _ => (1 : ℝ)))
  rw [r11b_real_inner_toLp_eq_integral] at hinner
  have hnorm : ‖hf.norm.toLp (fun x => ‖f x‖)‖ = ‖hf.toLp f‖ := by
    simp only [Lp.norm_toLp, eLpNorm_norm f hf.aestronglyMeasurable]
  simpa only [mul_one, hnorm, n06IntervalL2Unit, mul_comm] using hinner

/-- The integral from the left endpoint is uniformly controlled on the
whole closed interval by the original L2 norm. -/
theorem n06_interval_primitive_norm_le {a b : ℝ} {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    {x : ℝ} (hx : x ∈ Icc a b) :
    ‖∫ t in a..x, f t‖ ≤ n06IntervalL2Unit a b * ‖hf.toLp f‖ := by
  have hab : a ≤ b := hx.1.trans hx.2
  have hi : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr
      (interval_memLp_integrable hf)
  calc
    ‖∫ t in a..x, f t‖ ≤ ∫ t in a..x, ‖f t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hx.1
    _ ≤ ∫ t in a..b, ‖f t‖ :=
      intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
        (Eventually.of_forall fun _ => norm_nonneg _) hi.norm
    _ = ∫ t, ‖f t‖ ∂volume.restrict (Ioo a b) := by
      rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
    _ ≤ _ := n06_interval_integral_norm_le hf

/-- A uniform AE bound becomes a bound in the actual interval L2 norm. -/
theorem n06_interval_toLp_norm_le {a b C : ℝ} {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hb : ∀ᵐ x ∂volume.restrict (Ioo a b), ‖f x‖ ≤ C) :
    ‖hf.toLp f‖ ≤ C * n06IntervalL2Unit a b := by
  have h1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Ioo a b)) :=
    interval_memLp_of_continuous continuous_const
  apply Lp.norm_le_mul_norm_of_ae_le_mul
    (f := hf.toLp f) (g := h1.toLp (fun _ => (1 : ℝ)))
  filter_upwards [hf.coeFn_toLp, h1.coeFn_toLp, hb] with x hxf hx1 hx
  simpa only [hxf, hx1, norm_one, mul_one] using hx

/-- The actual primitive with its prescribed value at the recorded left
endpoint. -/
def n06IntervalPrimitive (a C : ℝ) (g : ℝ → ℝ) : ℝ → ℝ :=
  fun x => C + ∫ t in a..x, g t

theorem n06IntervalPrimitive_left (a C : ℝ) (g : ℝ → ℝ) :
    n06IntervalPrimitive a C g a = C := by
  simp [n06IntervalPrimitive]

theorem n06IntervalPrimitive_hasDerivAt (a C : ℝ) {g : ℝ → ℝ}
    (hg : Continuous g) (x : ℝ) :
    HasDerivAt (n06IntervalPrimitive a C g) (g x) x := by
  change HasDerivAt (fun y : ℝ => C + ∫ t in a..y, g t) (g x) x
  exact (hg.integral_hasStrictDerivAt a x).hasDerivAt.const_add C

theorem n06IntervalPrimitive_deriv (a C : ℝ) {g : ℝ → ℝ}
    (hg : Continuous g) : deriv (n06IntervalPrimitive a C g) = g :=
  funext fun x => (n06IntervalPrimitive_hasDerivAt a C hg x).deriv

theorem n06IntervalPrimitive_contDiff (a C : ℝ) {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (n06IntervalPrimitive a C g) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (n06IntervalPrimitive_hasDerivAt a C hg.continuous x).differentiableAt, ?_⟩
  rw [n06IntervalPrimitive_deriv a C hg.continuous]
  exact hg

/-- The primitive error controls every point of the closed interval,
including both genuine endpoint values. -/
theorem n06_interval_primitive_sub_norm_le {a b : ℝ} {v g : ℝ → ℝ}
    (hv : AbsolutelyContinuousOnInterval v a b) (hg : Continuous g)
    (hvd : MemLp (deriv v) 2 (volume.restrict (Ioo a b)))
    {x : ℝ} (hx : x ∈ Icc a b) :
    ‖n06IntervalPrimitive a (v a) g x - v x‖ ≤ n06IntervalL2Unit a b *
      ‖(interval_memLp_of_continuous (a := a) (b := b) hg).toLp g -
        hvd.toLp (deriv v)‖ := by
  have hab : a ≤ b := hx.1.trans hx.2
  have hsub : uIcc a x ⊆ uIcc a b := by
    rw [uIcc_of_le hx.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hx.2
  have hvx : AbsolutelyContinuousOnInterval v a x := hv.mono hsub
  have heq : n06IntervalPrimitive a (v a) g x - v x =
      ∫ t in a..x, (g - deriv v) t := by
    simp only [Pi.sub_apply]
    rw [intervalIntegral.integral_sub (hg.intervalIntegrable a x)
      hvx.intervalIntegrable_deriv, hvx.integral_deriv_eq_sub]
    dsimp only [n06IntervalPrimitive]
    ring
  rw [heq]
  have hg₂ : MemLp g 2 (volume.restrict (Ioo a b)) :=
    interval_memLp_of_continuous hg
  have hb := n06_interval_primitive_norm_le (hg₂.sub hvd) hx
  rw [MemLp.toLp_sub hg₂ hvd] at hb
  exact hb

/-- The same comparison also controls the primitive in L2, with one
additional factor equal to the norm of one on this interval. -/
theorem n06_interval_primitive_toLp_sub_norm_le {a b : ℝ} (hab : a ≤ b)
    {v g : ℝ → ℝ} (hv : AbsolutelyContinuousOnInterval v a b)
    (hg : ContDiff ℝ ∞ g)
    (hv₀ : MemLp v 2 (volume.restrict (Ioo a b)))
    (hv₁ : MemLp (deriv v) 2 (volume.restrict (Ioo a b))) :
    ‖(interval_memLp_of_continuous
      (n06IntervalPrimitive_contDiff a (v a) hg).continuous).toLp
        (n06IntervalPrimitive a (v a) g) - hv₀.toLp v‖ ≤
      n06IntervalL2Unit a b ^ 2 *
        ‖(interval_memLp_of_continuous (a := a) (b := b) hg.continuous).toLp g -
          hv₁.toLp (deriv v)‖ := by
  have hP : MemLp (n06IntervalPrimitive a (v a) g) 2 (volume.restrict (Ioo a b)) :=
    interval_memLp_of_continuous (n06IntervalPrimitive_contDiff a (v a) hg).continuous
  have hb : ∀ᵐ x ∂volume.restrict (Ioo a b),
      ‖(n06IntervalPrimitive a (v a) g - v) x‖ ≤ n06IntervalL2Unit a b *
        ‖(interval_memLp_of_continuous (a := a) (b := b) hg.continuous).toLp g -
          hv₁.toLp (deriv v)‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact n06_interval_primitive_sub_norm_le hv hg.continuous hv₁ (mem_Icc_of_Ioo hx)
  have hn := n06_interval_toLp_norm_le (hP.sub hv₀) hb
  rw [MemLp.toLp_sub hP hv₀] at hn
  convert hn using 1 <;> ring

end ContinuousFlexibility.Analysis
