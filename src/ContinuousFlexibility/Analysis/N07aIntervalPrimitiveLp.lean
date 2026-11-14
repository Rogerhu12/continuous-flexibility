module

public import ContinuousFlexibility.Analysis.IntervalL1Primitive
public import ContinuousFlexibility.Analysis.SmoothCompactL2MeanDensity

/-!
# The actual integral primitive as a bounded map on interval L²

The primitive uses zero extension outside the unit interval. Its ordinary
continuous representative and its distributional derivative are retained,
and its L² norm is bounded by the norm of the original integrand. This is
the integration map used to approximate a genuine second weak derivative.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff

abbrev N07aIntervalL2 := Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))

private theorem n07a_interval_one_norm :
    ‖(memLp_const (μ := volume.restrict (Ioo (0 : ℝ) 1)) (p := 2) (1 : ℝ)).toLp
      (fun _ : ℝ => 1)‖ = 1 := by
  have h : ‖(memLp_const (μ := volume.restrict (Ioo (0 : ℝ) 1))
      (p := 2) (1 : ℝ)).toLp (fun _ : ℝ => 1)‖ ^ 2 = 1 :=
    (norm_toLp_sq_eq_integral_sq
      (memLp_const (μ := volume.restrict (Ioo (0 : ℝ) 1)) (p := 2) (1 : ℝ))).trans
      (by norm_num [Measure.real, Real.volume_Ioo])
  nlinarith [norm_nonneg ((memLp_const
    (μ := volume.restrict (Ioo (0 : ℝ) 1)) (p := 2) (1 : ℝ)).toLp (fun _ : ℝ => 1))]

/-- On the unit interval the L¹ norm is bounded by the L² norm. -/
theorem n07a_interval_integral_norm_le {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    (∫ x in Ioo (0 : ℝ) 1, ‖f x‖) ≤ ‖hf.toLp f‖ := by
  have h := abs_integral_le_L2_one_norm hf.norm
  rw [n07a_interval_one_norm, one_mul,
    abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] at h
  have heq : ‖hf.norm.toLp (fun x => ‖f x‖)‖ = ‖hf.toLp f‖ := by
    apply le_antisymm
    · apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hf.norm.coeFn_toLp, hf.coeFn_toLp] with x hx hy
      simp only [hx, hy, norm_norm, le_refl]
    · apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hf.coeFn_toLp, hf.norm.coeFn_toLp] with x hx hy
      simp only [hx, hy, norm_norm, le_refl]
  exact h.trans_eq heq

/-- The continuous zero-extension primitive has a pointwise L² bound. -/
theorem n07a_intervalL1Primitive_bound {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖intervalL1Primitive 0 1 f x‖ ≤ ‖hf.toLp f‖ := by
  let g := (Ioo (0 : ℝ) 1).indicator f
  have hi : Integrable g :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (hf.integrable (by norm_num))
  calc
    ‖intervalL1Primitive 0 1 f x‖ ≤ ∫ y in (0 : ℝ)..x, ‖g y‖ :=
      intervalIntegral.norm_integral_le_integral_norm hx.1
    _ ≤ ∫ y, ‖g y‖ := by
      rw [intervalIntegral.integral_of_le hx.1]
      exact integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall fun _ => norm_nonneg _) hi.norm
    _ = ∫ y in Ioo (0 : ℝ) 1, ‖f y‖ := by
      rw [show (fun y => ‖g y‖) = (Ioo (0 : ℝ) 1).indicator (fun y => ‖f y‖) from
        funext fun y => by simp only [g, norm_indicator_eq_indicator_norm]]
      exact integral_indicator measurableSet_Ioo
    _ ≤ ‖hf.toLp f‖ := n07a_interval_integral_norm_le hf

/-- Membership of the actual primitive in the same interval L² space. -/
theorem n07a_intervalL1Primitive_memLp {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    MemLp (intervalL1Primitive 0 1 f) 2 (volume.restrict (Ioo (0 : ℝ) 1)) := by
  have hc := continuous_intervalL1Primitive (hf.integrable (by norm_num))
  apply MemLp.of_bound hc.aestronglyMeasurable ‖hf.toLp f‖
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact n07a_intervalL1Primitive_bound hf (Ioo_subset_Icc_self hx)

/-- The primitive is a contraction on interval L². -/
theorem n07a_intervalL1Primitive_norm_le {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ‖(n07a_intervalL1Primitive_memLp hf).toLp (intervalL1Primitive 0 1 f)‖ ≤
      ‖hf.toLp f‖ := by
  have h1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2
      (volume.restrict (Ioo (0 : ℝ) 1)) := memLp_const 1
  have h := Lp.norm_le_mul_norm_of_ae_le_mul
    (f := (n07a_intervalL1Primitive_memLp hf).toLp (intervalL1Primitive 0 1 f))
    (g := h1.toLp (fun _ => 1)) (c := ‖hf.toLp f‖) (by
      filter_upwards [(n07a_intervalL1Primitive_memLp hf).coeFn_toLp,
        h1.coeFn_toLp, ae_restrict_mem measurableSet_Ioo] with x hx hx1 hxin
      rw [hx, hx1, norm_one, mul_one]
      exact n07a_intervalL1Primitive_bound hf (Ioo_subset_Icc_self hxin))
  simpa only [n07a_interval_one_norm, mul_one] using h

/-- Almost-everywhere integrands have exactly the same actual primitive. -/
theorem n07a_intervalL1Primitive_congr {f g : ℝ → ℝ}
    (hfg : f =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] g) :
    intervalL1Primitive 0 1 f = intervalL1Primitive 0 1 g := by
  have he : (Ioo (0 : ℝ) 1).indicator f =ᵐ[volume]
      (Ioo (0 : ℝ) 1).indicator g := by
    have h := (ae_restrict_iff' measurableSet_Ioo).mp hfg
    filter_upwards [h] with x hx
    by_cases hxin : x ∈ Ioo (0 : ℝ) 1
    · simp only [indicator_of_mem hxin, hx hxin]
    · simp only [indicator_of_notMem hxin]
  funext x
  exact intervalIntegral.integral_congr_ae (he.mono fun _ h _ => h)

/-- The actual distributional identity is preserved alongside the norm bound. -/
theorem n07a_intervalL1Primitive_weakDerivative {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    HasIntervalWeakDerivative 0 1 (intervalL1Primitive 0 1 f) f := by
  intro φ hφ hc hs
  exact integral_intervalL1Primitive_mul_deriv_eq_neg zero_lt_one
    (hf.integrable (by norm_num)) hφ hc hs

/-- Integration of the prescribed L² class as a bounded linear operator. -/
def n07aIntervalPrimitive : N07aIntervalL2 →L[ℝ] N07aIntervalL2 :=
  LinearMap.mkContinuous
    { toFun := fun f => (n07a_intervalL1Primitive_memLp (Lp.memLp f)).toLp
        (intervalL1Primitive 0 1 f)
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [(n07a_intervalL1Primitive_memLp (Lp.memLp (f + g))).coeFn_toLp,
          Lp.coeFn_add
            ((n07a_intervalL1Primitive_memLp (Lp.memLp f)).toLp (intervalL1Primitive 0 1 f))
            ((n07a_intervalL1Primitive_memLp (Lp.memLp g)).toLp (intervalL1Primitive 0 1 g)),
          (n07a_intervalL1Primitive_memLp (Lp.memLp f)).coeFn_toLp,
          (n07a_intervalL1Primitive_memLp (Lp.memLp g)).coeFn_toLp] with x hx ha hf hg
        rw [hx, ha, Pi.add_apply, hf, hg]
        rw [n07a_intervalL1Primitive_congr (Lp.coeFn_add f g)]
        unfold intervalL1Primitive
        simp only [Set.indicator_add']
        exact intervalIntegral.integral_add
          ((integrable_indicator_iff measurableSet_Ioo).mpr
            ((Lp.memLp f).integrable (by norm_num))).intervalIntegrable
          ((integrable_indicator_iff measurableSet_Ioo).mpr
            ((Lp.memLp g).integrable (by norm_num))).intervalIntegrable
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [(n07a_intervalL1Primitive_memLp (Lp.memLp (c • f))).coeFn_toLp,
          Lp.coeFn_smul c
            ((n07a_intervalL1Primitive_memLp (Lp.memLp f)).toLp (intervalL1Primitive 0 1 f)),
          (n07a_intervalL1Primitive_memLp (Lp.memLp f)).coeFn_toLp] with x hx hc hf
        simp only [RingHom.id_apply, hx, hc, Pi.smul_apply, smul_eq_mul, hf]
        rw [n07a_intervalL1Primitive_congr (Lp.coeFn_smul c f)]
        unfold intervalL1Primitive
        rw [show (Ioo (0 : ℝ) 1).indicator (c • (f : ℝ → ℝ)) =
          (fun y => c * (Ioo (0 : ℝ) 1).indicator (fun y => f y) y) from by
            have heq : (c • (f : ℝ → ℝ)) = (fun y => c • f y) :=
              funext (fun y => Pi.smul_apply c (f : ℝ → ℝ) y)
            rw [heq]
            funext y
            simpa only [smul_eq_mul] using
              Set.indicator_const_smul_apply (Ioo (0 : ℝ) 1) c (f : ℝ → ℝ) y]
        exact intervalIntegral.integral_const_mul c _ }
    1 (fun f => by
      change ‖(n07a_intervalL1Primitive_memLp (Lp.memLp f)).toLp
        (intervalL1Primitive 0 1 f)‖ ≤ 1 * ‖f‖
      have h := n07a_intervalL1Primitive_norm_le (Lp.memLp f)
      simpa only [Lp.toLp_coeFn, one_mul] using h)

theorem n07aIntervalPrimitive_apply (f : N07aIntervalL2) :
    n07aIntervalPrimitive f =
      (n07a_intervalL1Primitive_memLp (Lp.memLp f)).toLp (intervalL1Primitive 0 1 f) := by
  simp only [n07aIntervalPrimitive, LinearMap.mkContinuous_apply]
  rfl

@[simp] theorem n07aIntervalPrimitive_apply_ae (f : N07aIntervalL2) :
    (n07aIntervalPrimitive f : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      intervalL1Primitive 0 1 f :=
  (n07a_intervalL1Primitive_memLp (Lp.memLp f)).coeFn_toLp

theorem n07aIntervalPrimitive_norm_le (f : N07aIntervalL2) :
    ‖n07aIntervalPrimitive f‖ ≤ ‖f‖ := by
  rw [n07aIntervalPrimitive_apply]
  simpa only [Lp.toLp_coeFn] using n07a_intervalL1Primitive_norm_le (Lp.memLp f)

end ContinuousFlexibility.Analysis
