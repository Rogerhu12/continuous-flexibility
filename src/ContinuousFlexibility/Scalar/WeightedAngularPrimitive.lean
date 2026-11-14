module

public import ContinuousFlexibility.Statements.ScalarWeighted
public import ContinuousFlexibility.Scalar.Conservation
public import ContinuousFlexibility.Scalar.RectangleParameterIntegral
public import ContinuousFlexibility.Analysis.MaterialCylinderPointwise
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The actual angular primitive for odd scalar fields

An odd periodic coefficient is represented by the angular derivative of an
even periodic height.  The primitive is the actual integral from angle zero,
so its radial support and its compatibility with the material pullback are
identities.  No boundedness assertion for this integration operator is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

/-- The primitive with its value fixed at angle zero. -/
def scalarAngularPrimitive (f : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  ∫ t in (0 : ℝ)..p.2, f (p.1, t)

theorem scalarAngularPrimitive_zero (f : PolarPoint → ℝ) (r : ℝ) :
    scalarAngularPrimitive f (r, 0) = 0 := by
  simp only [scalarAngularPrimitive, intervalIntegral.integral_same]

/-- A fixed integration interval makes joint smoothness immediate. -/
theorem scalarAngularPrimitive_eq_unitIntegral (f : PolarPoint → ℝ) (p : PolarPoint) :
    scalarAngularPrimitive f p = p.2 * ∫ t in (0 : ℝ)..1, f (p.1, p.2 * t) := by
  simpa only [scalarAngularPrimitive, smul_eq_mul, mul_zero, mul_one] using
    (intervalIntegral.smul_integral_comp_mul_left
      (fun t => f (p.1, t)) (a := 0) (b := 1) p.2).symm

theorem scalarAngularPrimitive_contDiff {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (scalarAngularPrimitive f) := by
  have hform : scalarAngularPrimitive f =
      fun p : PolarPoint => p.2 * ∫ t in (0 : ℝ)..1, f (p.1, p.2 * t) :=
    funext (scalarAngularPrimitive_eq_unitIntegral f)
  rw [hform]
  apply contDiff_snd.mul
  apply contDiff_iff_contDiffAt.mpr
  intro p
  apply contDiffAt_intervalIntegral_parameter
    (f := fun z : PolarPoint × ℝ => f (z.1.1, z.1.2 * z.2)) (O := univ) isOpen_univ
    (by norm_num : (0 : ℝ) ≤ 1) (hp := mem_univ p)
  intro q _ t _
  exact (hf.comp
    (contDiff_fst.fst.prodMk (contDiff_fst.snd.mul contDiff_snd))).contDiffAt

theorem hasDerivAt_scalarAngularPrimitive_angular {f : PolarPoint → ℝ}
    (hf : Continuous f) (r θ : ℝ) :
    HasDerivAt (fun t => scalarAngularPrimitive f (r, t)) (f (r, θ)) θ := by
  have hs : Continuous (fun t : ℝ => f (r, t)) :=
    hf.comp (continuous_const.prodMk continuous_id)
  exact intervalIntegral.integral_hasDerivAt_right (hs.intervalIntegrable 0 θ)
    hs.aestronglyMeasurable.stronglyMeasurableAtFilter hs.continuousAt

theorem angularPartial_scalarAngularPrimitive {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) : angularPartial (scalarAngularPrimitive f) = f := by
  funext p
  exact (hasDerivAt_angular_slice
    ((scalarAngularPrimitive_contDiff hf).differentiable (by simp) p)).unique
      (hasDerivAt_scalarAngularPrimitive_angular hf.continuous p.1 p.2)

/-- Oddness of the integrand gives evenness of this precise normalization. -/
theorem scalarAngularPrimitive_even {f : PolarPoint → ℝ}
    (hodd : ∀ r θ, f (r, -θ) = -f (r, θ)) (r θ : ℝ) :
    scalarAngularPrimitive f (r, -θ) = scalarAngularPrimitive f (r, θ) := by
  change (∫ t in (0 : ℝ)..-θ, f (r, t)) = ∫ t in (0 : ℝ)..θ, f (r, t)
  calc
    _ = -(∫ t in -θ..(0 : ℝ), f (r, t)) := intervalIntegral.integral_symm _ _
    _ = -(∫ t in (0 : ℝ)..θ, f (r, -t)) := by
      simpa only [neg_zero] using congrArg (fun v : ℝ => -v)
        (intervalIntegral.integral_comp_neg (fun t => f (r, t)) (a := 0) (b := θ)).symm
    _ = ∫ t in (0 : ℝ)..θ, f (r, t) := by
      simp only [hodd, intervalIntegral.integral_neg, neg_neg]

/-- An odd periodic function has zero integral over this same period. -/
theorem integral_odd_periodic_angular_eq_zero {f : PolarPoint → ℝ} {P : ℝ}
    (hodd : ∀ r θ, f (r, -θ) = -f (r, θ))
    (hp : Function.Periodic f (0, P)) (r : ℝ) :
    (∫ t in (0 : ℝ)..P, f (r, t)) = 0 := by
  have hreflect (t : ℝ) : f (r, P - t) = -f (r, t) := by
    have he := hp (r, -t)
    simp only [Prod.mk_add_mk, add_zero] at he
    rw [show P - t = -t + P by ring, he, hodd]
  have he := intervalIntegral.integral_comp_sub_left (fun t => f (r, t))
    (a := 0) (b := P) P
  simp only [sub_self, sub_zero, hreflect, intervalIntegral.integral_neg] at he
  linarith

theorem scalarAngularPrimitive_periodic {f : PolarPoint → ℝ} {P : ℝ}
    (hf : Continuous f) (hodd : ∀ r θ, f (r, -θ) = -f (r, θ))
    (hp : Function.Periodic f (0, P)) :
    Function.Periodic (scalarAngularPrimitive f) (0, P) := by
  intro p
  have hs : Function.Periodic (fun t => f (p.1, t)) P := by
    intro t
    simpa only [Prod.mk_add_mk, add_zero] using hp (p.1, t)
  have hc : Continuous (fun t : ℝ => f (p.1, t)) :=
    hf.comp (continuous_const.prodMk continuous_id)
  simp only [scalarAngularPrimitive, Prod.fst_add, Prod.snd_add, add_zero]
  rw [hs.intervalIntegral_add_eq_add 0 p.2
    (fun a b => hc.intervalIntegrable a b), zero_add,
    integral_odd_periodic_angular_eq_zero hodd hp, add_zero]

theorem scalarAngularPrimitive_eq_zero_outside {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : ∀ p, p ∉ annularOpen D → f p = 0) (p : PolarPoint)
    (hp : p ∉ annularOpen D) : scalarAngularPrimitive f p = 0 := by
  have hz : (fun t => f (p.1, t)) = fun _ => (0 : ℝ) := by
    funext t
    apply hf
    intro ht
    exact hp ⟨ht.1, mem_univ _⟩
  simp only [scalarAngularPrimitive, hz, intervalIntegral.integral_zero]

theorem scalarAngularPrimitive_add {f g : PolarPoint → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    scalarAngularPrimitive (fun p => f p + g p) =
      fun p => scalarAngularPrimitive f p + scalarAngularPrimitive g p := by
  funext p
  exact intervalIntegral.integral_add
    ((hf.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 p.2)
    ((hg.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 p.2)

theorem scalarAngularPrimitive_const_mul (c : ℝ) (f : PolarPoint → ℝ) :
    scalarAngularPrimitive (fun p => c * f p) =
      fun p => c * scalarAngularPrimitive f p := by
  funext p
  exact intervalIntegral.integral_const_mul c _

/-- The radial weight and material coordinate commute with angular integration. -/
theorem materialPullback_scalarAngularPrimitive (T : MaterialData) (γ : ℝ)
    (f : PolarPoint → ℝ) :
    materialPullback T γ (scalarAngularPrimitive f) =
      scalarAngularPrimitive (materialPullback T γ f) := by
  funext p
  simp only [materialPullback, scalarAngularPrimitive, intervalIntegral.integral_const_mul]

end ContinuousFlexibility.Statements
