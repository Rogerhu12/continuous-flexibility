import ContinuousFlexibility.Analysis.N07bFiniteRadialGreen
import ContinuousFlexibility.Analysis.N06AngularMeanBridge
import ContinuousFlexibility.Radial.FourierOrthogonality

/-!
# Compatibility of the reference PDE at finite regularity

A height with actual C² germs on the closed radial core has zero total
reference source. The constant test in the finite rectangle Green formula
has zero radial flux because the profile vanishes at both endpoints; the
angular seam cancels by the actual half-period symmetry.

The reference column also has zero half-period angular mean. Consequently
the genuine field `radialPDE u + μ * referenceColumn * cosineMode 2` satisfies
the physical compatibility condition. No zero-integral hypothesis or
infinite-order regularity of the height is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem n07b_reference_angularCoefficient_contDiffAt
    {D : ReferenceData} (hgeom : RadialProfileGeometry D) {p : PolarPoint}
    (hp : p.1 ∈ Icc D.a D.b) :
    ContDiffAt ℝ ∞ (radialHeightField (fun r => deriv D.w r / r)) p := by
  have hr : p.1 ≠ 0 := (hgeom.1.trans_le hp.1).ne'
  have hq : ContDiffAt ℝ ∞ (fun r => deriv D.w r / r) p.1 :=
    (contDiff_infty_iff_deriv.mp hgeom.2.2.1.1).2.contDiffAt.div contDiffAt_id hr
  exact hq.comp p contDiffAt_fst

/-- Actual C² germs along the closed core suffice. No endpoint value or
endpoint derivative condition on the height is required. -/
theorem n07b_c2_reference_physicalSourceIntegral_eq_zero
    {D : ReferenceData} (hgeom : RadialProfileGeometry D) {u : PolarPoint → ℝ}
    (hu : ∀ p ∈ Icc D.a D.b ×ˢ (univ : Set ℝ), ContDiffAt ℝ 2 u p)
    (hperiod : Function.Periodic u (0, Real.pi)) :
    physicalSourceIntegral D
      (fun p => radialPDE D.w (fun r θ => u (r, θ)) p.1 p.2) = 0 := by
  have hw : ContDiff ℝ ∞ D.w := hgeom.2.2.1.1
  have hwa : D.w D.a = 0 := hgeom.2.2.1.2 D.a (Or.inl le_rfl)
  have hwb : D.w D.b = 0 := hgeom.2.2.1.2 D.b (Or.inr le_rfl)
  have hclosed (p : PolarPoint)
      (hp : p ∈ uIcc D.a D.b ×ˢ uIcc (0 : ℝ) Real.pi) :
      p ∈ Icc D.a D.b ×ˢ (univ : Set ℝ) := by
    exact ⟨by simpa only [uIcc_of_le hgeom.2.1.le] using hp.1, mem_univ _⟩
  have hA (p : PolarPoint)
      (_hp : p ∈ uIcc D.a D.b ×ˢ uIcc (0 : ℝ) Real.pi) :
      ContDiffAt ℝ 1 (radialHeightField D.w) p :=
    (contDiff_radialHeightField hw).contDiffAt.of_le (by simp)
  have hC (p : PolarPoint)
      (hp : p ∈ uIcc D.a D.b ×ˢ uIcc (0 : ℝ) Real.pi) :
      ContDiffAt ℝ 1 (radialHeightField (fun r => deriv D.w r / r)) p :=
    (n07b_reference_angularCoefficient_contDiffAt hgeom (hclosed p hp).1).of_le (by simp)
  have hseam : ∀ r ∈ uIcc D.a D.b,
      greenAngularFlux (fun _ => 0)
        (radialHeightField (fun s => deriv D.w s / s)) (fun _ => 1) u (r, Real.pi) =
      greenAngularFlux (fun _ => 0)
        (radialHeightField (fun s => deriv D.w s / s)) (fun _ => 1) u (r, 0) := by
    intro r _
    have hθ := periodic_angularPartial hperiod (r, 0)
    simp only [Prod.mk_add_mk, add_zero, zero_add] at hθ
    simp only [greenAngularFlux, symmetricAngularFlux, radialHeightField,
      radialPartial_const, angularPartial_const, zero_mul, mul_zero,
      zero_add, one_mul, sub_zero, hθ]
  have hends : ∀ θ ∈ uIcc (0 : ℝ) Real.pi,
      greenNormalFlux (radialHeightField D.w) (fun _ => 0) (fun _ => 1) u (D.b, θ) =
      greenNormalFlux (radialHeightField D.w) (fun _ => 0) (fun _ => 1) u (D.a, θ) := by
    intro θ _
    simp only [greenNormalFlux, symmetricNormalFlux, radialHeightField,
      hwa, hwb, zero_mul, add_zero, mul_zero, sub_self]
  have hgreen := n07b_c2_integral_symmetric_green_eq_zero
    (A := radialHeightField D.w) (B := fun _ => 0)
    (C := radialHeightField (fun r => deriv D.w r / r))
    (φ := fun _ => 1) (ψ := u) (a := D.a) (b := D.b) (c := 0) (d := Real.pi)
    hA (fun _ _ => contDiffAt_const) hC (fun _ _ => contDiffAt_const)
    (fun p hp => hu p (hclosed p hp)) hseam hends
  have hconstant (p : PolarPoint) :
      symmetricDivergence (radialHeightField D.w) (fun _ => 0)
        (radialHeightField (fun r => deriv D.w r / r)) (fun _ => 1) p = 0 := by
    simp [symmetricDivergence, symmetricNormalFlux, symmetricAngularFlux]
  have hraw : (∫ r in D.a..D.b, ∫ θ in (0 : ℝ)..Real.pi,
      radialPDE D.w (fun s α => u (s, α)) r θ) = 0 := by
    calc
      _ = ∫ r in D.a..D.b, ∫ θ in (0 : ℝ)..Real.pi,
          (1 : ℝ) * symmetricDivergence (radialHeightField D.w) (fun _ => 0)
            (radialHeightField (fun s => deriv D.w s / s)) u (r, θ) -
          u (r, θ) * symmetricDivergence (radialHeightField D.w) (fun _ => 0)
            (radialHeightField (fun s => deriv D.w s / s)) (fun _ => 1) (r, θ) := by
        apply intervalIntegral.integral_congr
        intro r hr
        apply intervalIntegral.integral_congr
        intro θ hθ
        have hp := hclosed (r, θ) ⟨hr, hθ⟩
        change radialPDE D.w (fun s α => u (s, α)) r θ =
          1 * symmetricDivergence (radialHeightField D.w) (fun _ => 0)
            (radialHeightField (fun s => deriv D.w s / s)) u (r, θ) -
          u (r, θ) * symmetricDivergence (radialHeightField D.w) (fun _ => 0)
            (radialHeightField (fun s => deriv D.w s / s)) (fun _ => 1) (r, θ)
        rw [hconstant, mul_zero, sub_zero, one_mul,
          n07b_c2_reference_divergence_eq_radialPDE hw (hu (r, θ) hp)
            ((hgeom.1.trans_le hp.1.1).ne')]
      _ = 0 := hgreen
  change (∫ r in D.a..D.b, (1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi,
    radialPDE D.w (fun s α => u (s, α)) r θ) = 0
  rw [intervalIntegral.integral_const_mul, hraw, mul_zero]

/-- The common global C² specialization. -/
theorem n07b_reference_physicalSourceIntegral_eq_zero_of_contDiff
    {D : ReferenceData} (hgeom : RadialProfileGeometry D) {u : PolarPoint → ℝ}
    (hu : ContDiff ℝ 2 u) (hperiod : Function.Periodic u (0, Real.pi)) :
    physicalSourceIntegral D
      (fun p => radialPDE D.w (fun r θ => u (r, θ)) p.1 p.2) = 0 :=
  n07b_c2_reference_physicalSourceIntegral_eq_zero hgeom (fun _ _ => hu.contDiffAt) hperiod

/-- A fixed interior radial slice of the actual reference PDE is continuous
under C² regularity of the height on the open annulus. -/
theorem n07b_c2_continuous_referencePDESlice
    {D : ReferenceData} (hgeom : RadialProfileGeometry D) {u : PolarPoint → ℝ}
    (hu : ContDiffOn ℝ 2 u (annularOpen D)) {r : ℝ} (hr : r ∈ radialCore D) :
    Continuous (fun θ => radialPDE D.w (fun s α => u (s, α)) r θ) := by
  let L : SymmetricCoefficients :=
    ⟨radialHeightField D.w, fun _ => 0,
      radialHeightField (fun s => deriv D.w s / s)⟩
  have hopen : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hA : ContDiffOn ℝ 1 L.a (annularOpen D) :=
    ((contDiff_radialHeightField hgeom.2.2.1.1).of_le (by simp)).contDiffOn
  have hB : ContDiffOn ℝ 1 L.b (annularOpen D) := contDiffOn_const
  have hC : ContDiffOn ℝ 1 L.c (annularOpen D) := by
    intro p hp
    exact ((n07b_reference_angularCoefficient_contDiffAt hgeom
      ⟨hp.1.1.le, hp.1.2.le⟩).of_le (by simp)).contDiffWithinAt
  have hdiv := n07b_c2_continuousOn_divergenceOperator hopen hA hB hC hu
  have heq : (fun θ => radialPDE D.w (fun s α => u (s, α)) r θ) =
      (fun θ => divergenceOperator L u (r, θ)) := by
    funext θ
    have hp : (r, θ) ∈ annularOpen D := ⟨hr, mem_univ _⟩
    exact (n07b_c2_reference_divergence_eq_radialPDE hgeom.2.2.1.1
      ((hu (r, θ) hp).contDiffAt (hopen.mem_nhds hp))
      ((hgeom.1.trans hr.1).ne')).symm
  rw [heq]
  exact hdiv.comp_continuous (continuous_const.prodMk continuous_id)
    (fun θ => ⟨hr, mem_univ θ⟩)

/-- The actual even-frequency reference column has zero half-period mean. -/
theorem n07b_angularMean_mul_cosineMode_two (c : ℝ) :
    angularMean (fun θ => c * cosineMode 2 θ) = 0 := by
  have hp : Function.Periodic (fun θ => c * cosineMode 2 θ) Real.pi := by
    intro θ
    simpa only [Nat.mul_one] using congrArg (fun v : ℝ => c * v)
      (cosineMode_even_frequency_periodic 1 θ)
  have hc : Continuous (fun θ => c * cosineMode 2 θ) :=
    (continuous_iff_continuousAt.mpr
      (fun θ => (hasDerivAt_cosineMode 2 θ).continuousAt)).const_mul c
  rw [← n06_radialAngularMean_eq_angularMean_of_continuous hp hc]
  unfold radialAngularMean
  rw [intervalIntegral.integral_const_mul, integral_cosineMode 2 (by decide),
    mul_zero, mul_zero]

theorem n07b_referenceColumn_physicalSourceIntegral_eq_zero
    (D : ReferenceData) (μ : ℝ) :
    physicalSourceIntegral D
      (fun p => μ * referenceColumn D p.1 * cosineMode 2 p.2) = 0 := by
  simp only [physicalSourceIntegral, n07b_angularMean_mul_cosineMode_two,
    intervalIntegral.integral_zero]

/-- Compatibility holds for the actual reference forcing, with its scalar
column included and with no extra condition on that scalar. -/
theorem n07b_c2_reference_compatibility
    {D : ReferenceData} (hgeom : RadialProfileGeometry D) {u : PolarPoint → ℝ}
    (hu : ∀ p ∈ Icc D.a D.b ×ˢ (univ : Set ℝ), ContDiffAt ℝ 2 u p)
    (hperiod : Function.Periodic u (0, Real.pi)) (μ : ℝ) :
    physicalSourceIntegral D (fun p =>
      radialPDE D.w (fun r θ => u (r, θ)) p.1 p.2 +
        μ * referenceColumn D p.1 * cosineMode 2 p.2) = 0 := by
  have huOpen : ContDiffOn ℝ 2 u (annularOpen D) := by
    intro p hp
    exact (hu p ⟨⟨hp.1.1.le, hp.1.2.le⟩, mem_univ _⟩).contDiffWithinAt
  calc
    _ = physicalSourceIntegral D
        (fun p => radialPDE D.w (fun r θ => u (r, θ)) p.1 p.2) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hgeom.2.1.le
      intro r hr
      have hf := n07b_c2_continuous_referencePDESlice hgeom huOpen hr
      have hg : Continuous (fun θ => μ * referenceColumn D r * cosineMode 2 θ) :=
        (continuous_iff_continuousAt.mpr
          (fun θ => (hasDerivAt_cosineMode 2 θ).continuousAt)).const_mul _
      change angularMean (fun θ =>
        radialPDE D.w (fun s α => u (s, α)) r θ +
          μ * referenceColumn D r * cosineMode 2 θ) =
        angularMean (fun θ => radialPDE D.w (fun s α => u (s, α)) r θ)
      calc
        _ = angularMean (fun θ => radialPDE D.w (fun s α => u (s, α)) r θ) +
            angularMean (fun θ => μ * referenceColumn D r * cosineMode 2 θ) := by
          unfold angularMean
          rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _)
            (hg.intervalIntegrable _ _), mul_add]
        _ = _ := by rw [n07b_angularMean_mul_cosineMode_two, add_zero]
    _ = 0 := n07b_c2_reference_physicalSourceIntegral_eq_zero hgeom hu hperiod

/-- Only the formula inside the annulus matters for the compatibility
functional; arbitrary endpoint representatives give the same integral. -/
theorem n07b_c2_reference_compatibility_of_eqOn
    {D : ReferenceData} (hgeom : RadialProfileGeometry D) {u f : PolarPoint → ℝ}
    (hu : ∀ p ∈ Icc D.a D.b ×ˢ (univ : Set ℝ), ContDiffAt ℝ 2 u p)
    (hperiod : Function.Periodic u (0, Real.pi)) (μ : ℝ)
    (hf : EqOn f (fun p =>
      radialPDE D.w (fun r θ => u (r, θ)) p.1 p.2 +
        μ * referenceColumn D p.1 * cosineMode 2 p.2) (annularOpen D)) :
    physicalSourceIntegral D f = 0 := by
  apply Eq.trans _ (n07b_c2_reference_compatibility hgeom hu hperiod μ)
  apply intervalIntegral.integral_congr_Ioo_of_le hgeom.2.1.le
  intro r hr
  apply congrArg angularMean
  funext θ
  exact hf ⟨hr, mem_univ θ⟩

end ContinuousFlexibility.Analysis
