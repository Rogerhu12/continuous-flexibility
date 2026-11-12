import ContinuousFlexibility.Analysis.N06WeakFiniteParseval
import ContinuousFlexibility.Analysis.N06WeakAngularModes
import ContinuousFlexibility.Radial.ReferenceCosineJacobi

/-!
# Actual cylinder weak equations give the original radial modal equations

The coefficients use the original half-period angular measure. Tensor tests
are globally smooth, periodic, and compactly supported only in the radial
variable, exactly as in the canonical test class. Fubini then gives the
weak radial equation without imposing regularity on the L2 input fields.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators ContDiff
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- The normalized cosine coefficient of the actual half-period representative. -/
def n06HalfCosineCoefficient (U : PolarPoint → ℝ) (i : ℕ) (r : ℝ) : ℝ :=
  Real.pi⁻¹ * n06AngularCoefficient U (referenceAngularBasis i) r

/-- The canonical test class on the unit radial interval. -/
def n06UnitCanonicalTest (φ : PolarPoint → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ Function.Periodic φ (0, Real.pi) ∧
    ∃ J : Set ℝ, IsCompact J ∧ J ⊆ Ioo (0 : ℝ) 1 ∧
      ∀ r, r ∉ J → ∀ θ, φ (r, θ) = 0

theorem n06_unitCanonicalTest_iff {S : PhysicalSpacesData} {K : CanonicalData S}
    {m : ℕ} (hl : K.left m = 0) (hr : K.right m = 1) (φ : PolarPoint → ℝ) :
    n06UnitCanonicalTest φ ↔ CanonicalTest S K m φ := by
  simp only [n06UnitCanonicalTest, CanonicalTest, hl, hr]

/-- The actual formal adjoint appearing in the radial-coefficient weak PDE. -/
def n06UnitReferenceTestOperator (a c V : ℝ → ℝ) (φ : PolarPoint → ℝ) :
    PolarPoint → ℝ := fun p =>
  -radialPartial (fun q => a q.1 * radialPartial φ q) p -
    c p.1 * angularPartial (angularPartial φ) p + V p.1 * φ p

/-- The genuine unit-cylinder distributional equation, tested against the
whole canonical test class. -/
def n06UnitReferenceWeakEquation (a c V : ℝ → ℝ) (U F : PolarPoint → ℝ) : Prop :=
  ∀ φ, n06UnitCanonicalTest φ →
    (∫ p, U p * n06UnitReferenceTestOperator a c V φ p ∂cylinderWindowMeasure 0) =
      ∫ p, F p * φ p ∂cylinderWindowMeasure 0

theorem n06_unitCanonicalTest_tensor {φ e : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ioo (0 : ℝ) 1)
    (he : ContDiff ℝ ∞ e) (hp : Function.Periodic e Real.pi) :
    n06UnitCanonicalTest (fun p => φ p.1 * e p.2) := by
  refine ⟨(hφ.comp contDiff_fst).mul (he.comp contDiff_snd), ?_,
    tsupport φ, hφc, hφs, ?_⟩
  · intro p
    simp only [Prod.fst_add, Prod.snd_add, add_zero, hp p.2]
  · intro r hr θ
    change φ r * e θ = 0
    rw [image_eq_zero_of_notMem_tsupport hr, zero_mul]

theorem n06_halfCosineCoefficient_memLp {U : PolarPoint → ℝ}
    (hU : MemLp U 2 (cylinderWindowMeasure 0)) (i : ℕ) :
    MemLp (n06HalfCosineCoefficient U i) 2 (volume.restrict (Ioo (0 : ℝ) 1)) := by
  have hprod : MemLp U 2 ((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioc (0 : ℝ) Real.pi))) := by
    simpa only [n06_weak_unitWindow_eq_prod] using hU
  have hraw := (r11b_memLp_modeCoefficient hprod
    (n06_weak_halfPeriod_memLp_of_continuous
      (contDiff_referenceAngularBasis i).continuous)).1
  change MemLp (fun r => Real.pi⁻¹ *
    (∫ θ, U (r, θ) * referenceAngularBasis i θ
      ∂volume.restrict (Ioc (0 : ℝ) Real.pi))) 2
        (volume.restrict (Ioo (0 : ℝ) 1))
  exact hraw.const_mul Real.pi⁻¹

/-- Pairing an arbitrary original L2 field with a continuous tensor is the
pairing of its actual angular integral with the radial factor. -/
theorem n06_unit_tensor_pairing {U : PolarPoint → ℝ}
    (hU : MemLp U 2 (cylinderWindowMeasure 0)) {φ e : ℝ → ℝ}
    (hφ : Continuous φ) (he : Continuous e) :
    (∫ p, U p * (φ p.1 * e p.2) ∂cylinderWindowMeasure 0) =
      ∫ r in (0 : ℝ)..1, n06AngularCoefficient U e r * φ r := by
  have ht : MemLp (fun p : PolarPoint => φ p.1 * e p.2) 2
      (cylinderWindowMeasure 0) := by
    rw [n06_weak_unitWindow_eq_prod]
    exact r11b_memLp_tensor (interval_memLp_of_continuous hφ)
      (n06_weak_halfPeriod_memLp_of_continuous he)
  have hi : Integrable (fun p => U p * (φ p.1 * e p.2))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioc (0 : ℝ) Real.pi))) := by
    rw [← n06_weak_unitWindow_eq_prod]
    exact hU.integrable_mul ht
  rw [n06_weak_unitWindow_eq_prod, integral_prod _ hi, n06_unit_intervalIntegral_eq]
  apply integral_congr_ae
  filter_upwards with r
  change (∫ θ, U (r, θ) * (φ r * e θ) ∂angleMeasure) =
    (∫ θ, U (r, θ) * e θ ∂angleMeasure) * φ r
  have heq : (fun θ => U (r, θ) * (φ r * e θ)) =
      fun θ => (U (r, θ) * e θ) * φ r := by
    funext θ
    ring
  rw [heq, integral_mul_const]

theorem n06_unit_radialPartial_tensor {φ e : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (he : ContDiff ℝ ∞ e) :
    radialPartial (fun p : PolarPoint => φ p.1 * e p.2) =
      fun p => deriv φ p.1 * e p.2 := by
  have ht : ContDiff ℝ ∞ (fun p : PolarPoint => φ p.1 * e p.2) :=
    (hφ.comp contDiff_fst).mul (he.comp contDiff_snd)
  funext p
  rw [← deriv_cylinder_radial_slice (ht.differentiable (by simp)) p.1 p.2]
  exact ((hφ.differentiable (by simp) p.1).hasDerivAt.mul_const (e p.2)).deriv

theorem n06_unit_angularPartial_tensor {φ e : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (he : ContDiff ℝ ∞ e) :
    angularPartial (fun p : PolarPoint => φ p.1 * e p.2) =
      fun p => φ p.1 * deriv e p.2 := by
  have ht : ContDiff ℝ ∞ (fun p : PolarPoint => φ p.1 * e p.2) :=
    (hφ.comp contDiff_fst).mul (he.comp contDiff_snd)
  funext p
  rw [← deriv_cylinder_angular_slice (ht.differentiable (by simp)) p.1 p.2]
  exact ((he.differentiable (by simp) p.2).hasDerivAt.const_mul (φ p.1)).deriv

/-- Applying the actual two-variable test operator to a cosine tensor
produces precisely the one-variable modal adjoint, including the mean mode. -/
theorem n06_unit_referenceTestOperator_tensor {a c V φ : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hφ : ContDiff ℝ ∞ φ) (i : ℕ) :
    n06UnitReferenceTestOperator a c V
        (fun p => φ p.1 * referenceAngularBasis i p.2) =
      fun p => (-deriv (fun y => a y * deriv φ y) p.1 +
        ((((2 * i : ℕ) : ℝ)) ^ 2 * c p.1 + V p.1) * φ p.1) *
          referenceAngularBasis i p.2 := by
  have he := contDiff_referenceAngularBasis i
  have hφd : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hed : ContDiff ℝ ∞ (deriv (referenceAngularBasis i)) :=
    (contDiff_infty_iff_deriv.mp he).2
  have hr := n06_unit_radialPartial_tensor hφ he
  have hflux : (fun p : PolarPoint => a p.1 *
      radialPartial (fun q : PolarPoint => φ q.1 * referenceAngularBasis i q.2) p) =
      fun p => (a p.1 * deriv φ p.1) * referenceAngularBasis i p.2 := by
    funext p
    rw [hr]
    ring
  have hrr := n06_unit_radialPartial_tensor (ha.mul hφd) he
  have htt : angularPartial (angularPartial
      (fun p : PolarPoint => φ p.1 * referenceAngularBasis i p.2)) =
      fun p => φ p.1 * deriv (deriv (referenceAngularBasis i)) p.2 := by
    rw [n06_unit_angularPartial_tensor hφ he, n06_unit_angularPartial_tensor hφ hed]
  funext p
  unfold n06UnitReferenceTestOperator
  rw [hflux, hrr, htt]
  dsimp only
  rw [deriv_deriv_referenceAngularBasis]
  ring

/-- The actual cylinder distributional equation gives the original weak
equation of every normalized half-period cosine coefficient. -/
theorem n06_unit_weakEquation_modal {a c V : ℝ → ℝ} {U F : PolarPoint → ℝ}
    (ha : ContDiff ℝ ∞ a) (hc : Continuous c) (hV : Continuous V)
    (hU : MemLp U 2 (cylinderWindowMeasure 0))
    (hF : MemLp F 2 (cylinderWindowMeasure 0))
    (hweak : n06UnitReferenceWeakEquation a c V U F) (i : ℕ) :
    ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (0 : ℝ) 1 →
        (∫ y in (0 : ℝ)..1, n06HalfCosineCoefficient U i y *
          (-deriv (fun t => a t * deriv φ t) y +
            ((((2 * i : ℕ) : ℝ)) ^ 2 * c y + V y) * φ y)) =
          ∫ y in (0 : ℝ)..1, n06HalfCosineCoefficient F i y * φ y := by
  intro φ hφ hφc hφs
  let P : ℝ → ℝ := fun y => -deriv (fun t => a t * deriv φ t) y +
    ((((2 * i : ℕ) : ℝ)) ^ 2 * c y + V y) * φ y
  have hφd : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hP : Continuous P :=
    ((ha.mul hφd).continuous_deriv (by simp)).neg.add
      (((continuous_const.mul hc).add hV).mul hφ.continuous)
  have htest := n06_unitCanonicalTest_tensor hφ hφc hφs
    (contDiff_referenceAngularBasis i) (referenceAngularBasis_periodic i)
  have h := hweak _ htest
  rw [n06_unit_referenceTestOperator_tensor ha hφ i] at h
  change (∫ p, U p * (P p.1 * referenceAngularBasis i p.2) ∂cylinderWindowMeasure 0) =
    ∫ p, F p * (φ p.1 * referenceAngularBasis i p.2) ∂cylinderWindowMeasure 0 at h
  rw [n06_unit_tensor_pairing hU hP (contDiff_referenceAngularBasis i).continuous,
    n06_unit_tensor_pairing hF hφ.continuous (contDiff_referenceAngularBasis i).continuous] at h
  change (∫ y in (0 : ℝ)..1,
    (Real.pi⁻¹ * n06AngularCoefficient U (referenceAngularBasis i) y) * P y) =
      ∫ y in (0 : ℝ)..1,
        (Real.pi⁻¹ * n06AngularCoefficient F (referenceAngularBasis i) y) * φ y
  calc
    _ = Real.pi⁻¹ * ∫ y in (0 : ℝ)..1,
        n06AngularCoefficient U (referenceAngularBasis i) y * P y := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro y _
      ring
    _ = Real.pi⁻¹ * ∫ y in (0 : ℝ)..1,
        n06AngularCoefficient F (referenceAngularBasis i) y * φ y := congrArg (Real.pi⁻¹ * ·) h
    _ = _ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro y _
      ring

end ContinuousFlexibility.Analysis
