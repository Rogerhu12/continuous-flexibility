import ContinuousFlexibility.Radial.R11bRadialTests
import ContinuousFlexibility.Radial.R11bPhysicalPairing
import ContinuousFlexibility.Scalar.GreenIdentity

/-!
# Green symmetry of the smooth radial differential expression

The actual radial Jacobi PDE is a symmetric divergence with coefficients
`w, 0, w'/r`.  The periodic seam cancels and the radial conormal
Wronskian vanishes because the profile is zero at both endpoints.
No endpoint condition on the two smooth test fields is needed here.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

theorem reference_divergence_eq_radialPDE
    {w : ℝ → ℝ} {u : PolarPoint → ℝ} {x : PolarPoint}
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u) (hr : x.1 ≠ 0) :
    symmetricDivergence (radialHeightField w) (fun _ => 0)
      (radialHeightField (fun r => deriv w r / r)) u x =
        radialPDE w (fun r θ => u (r, θ)) x.1 x.2 := by
  have hwd := hw.differentiable (by simp) x.1
  have hq : DifferentiableAt ℝ (fun r => deriv w r / r) x.1 :=
    ((contDiff_infty_iff_deriv.mp hw).2.differentiable (by simp) x.1).div
      differentiableAt_id hr
  have hA : DifferentiableAt ℝ (radialHeightField w) x :=
    (contDiff_radialHeightField hw).differentiable (by simp) x
  have hC : DifferentiableAt ℝ
      (radialHeightField (fun r => deriv w r / r)) x :=
    hq.comp x differentiableAt_fst
  have hur : DifferentiableAt ℝ (radialPartial u) x :=
    (contDiffAt_radialPartial hu.contDiffAt (m := 1) (by simp)).differentiableAt
      one_ne_zero
  have huθ : DifferentiableAt ℝ (angularPartial u) x :=
    (contDiffAt_angularPartial hu.contDiffAt (m := 1) (by simp)).differentiableAt
      one_ne_zero
  rw [radialPDE_eq_polar_jets hwd hu]
  simp only [symmetricDivergence, symmetricNormalFlux, symmetricAngularFlux,
    zero_mul, add_zero, zero_add]
  rw [radialPartial_mul hA hur, angularPartial_mul hC huθ,
    radialPartial_radialHeightField hwd, angularPartial_radialHeightField hq]
  simp only [radialHeightField, zero_mul, zero_add]

theorem reference_periodic_two_pi {u : PolarPoint → ℝ}
    (hu : Function.Periodic u (0, Real.pi)) :
    Function.Periodic u (0, 2 * Real.pi) := by
  intro x
  have heq : x + (0, 2 * Real.pi) = (x + (0, Real.pi)) + (0, Real.pi) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, add_zero] <;> ring
  rw [heq, hu, hu]

/-- Ordinary rectangle Green identity for the actual radial PDE. -/
theorem reference_smooth_green_zero {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) {u v : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hup : Function.Periodic u (0, 2 * Real.pi))
    (hvp : Function.Periodic v (0, 2 * Real.pi)) :
    (∫ r in D.a..D.b, ∫ θ in (0 : ℝ)..2 * Real.pi,
      u (r, θ) * radialPDE D.w (fun s φ => v (s, φ)) r θ -
        v (r, θ) * radialPDE D.w (fun s φ => u (s, φ)) r θ) = 0 := by
  have hw : ContDiff ℝ ∞ D.w := hgeom.2.2.1.1
  have hwa : D.w D.a = 0 := hgeom.2.2.1.2 D.a (Or.inl le_rfl)
  have hwb : D.w D.b = 0 := hgeom.2.2.1.2 D.b (Or.inr le_rfl)
  have hr : ∀ x ∈ uIcc D.a D.b ×ˢ uIcc (0 : ℝ) (2 * Real.pi), x.1 ≠ 0 := by
    intro x hx
    rw [uIcc_of_le hgeom.2.1.le] at hx
    exact (hgeom.1.trans_le hx.1.1).ne'
  have hA : ∀ x ∈ uIcc D.a D.b ×ˢ uIcc (0 : ℝ) (2 * Real.pi),
      ContDiffAt ℝ ∞ (radialHeightField D.w) x :=
    fun _ _ => (contDiff_radialHeightField hw).contDiffAt
  have hC : ∀ x ∈ uIcc D.a D.b ×ˢ uIcc (0 : ℝ) (2 * Real.pi),
      ContDiffAt ℝ ∞ (radialHeightField (fun r => deriv D.w r / r)) x := by
    intro x hx
    have hq : ContDiffAt ℝ ∞ (fun r => deriv D.w r / r) x.1 :=
      (contDiff_infty_iff_deriv.mp hw).2.contDiffAt.div contDiffAt_id (hr x hx)
    exact hq.comp x contDiffAt_fst
  have hBp : Function.Periodic (fun _ : PolarPoint => (0 : ℝ))
      (0, 2 * Real.pi) := fun _ => rfl
  have hCp : Function.Periodic
      (radialHeightField (fun r => deriv D.w r / r)) (0, 2 * Real.pi) := by
    intro x
    simp only [radialHeightField, Prod.fst_add, add_zero]
  have hflux (r : ℝ) (hwzero : D.w r = 0) (θ : ℝ) :
      greenNormalFlux (radialHeightField D.w) (fun _ => 0) u v (r, θ) = 0 := by
    simp only [greenNormalFlux, symmetricNormalFlux, radialHeightField,
      hwzero, zero_mul, add_zero, mul_zero, sub_self]
  have hi := integral_symmetric_green_eq_zero_of_periodic
    (A := radialHeightField D.w) (B := fun _ => 0)
    (C := radialHeightField (fun r => deriv D.w r / r))
    (φ := u) (ψ := v) (a := D.a) (b := D.b) (T := 2 * Real.pi)
    hA (fun _ _ => contDiffAt_const) hC
    (fun _ _ => hu.contDiffAt) (fun _ _ => hv.contDiffAt)
    hBp hCp hup hvp (fun θ _ => hflux D.a hwa θ) (fun θ _ => hflux D.b hwb θ)
  calc
    _ = (∫ r in D.a..D.b, ∫ θ in (0 : ℝ)..2 * Real.pi,
        u (r, θ) * symmetricDivergence (radialHeightField D.w) (fun _ => 0)
          (radialHeightField (fun r => deriv D.w r / r)) v (r, θ) -
        v (r, θ) * symmetricDivergence (radialHeightField D.w) (fun _ => 0)
          (radialHeightField (fun r => deriv D.w r / r)) u (r, θ)) := by
      apply intervalIntegral.integral_congr
      intro r hrr
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [reference_divergence_eq_radialPDE hw hv (hr (r, θ) ⟨hrr, hθ⟩),
        reference_divergence_eq_radialPDE hw hu (hr (r, θ) ⟨hrr, hθ⟩)]
    _ = 0 := hi

theorem reference_smooth_green_mean_zero {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) {u v : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hup : Function.Periodic u (0, 2 * Real.pi))
    (hvp : Function.Periodic v (0, 2 * Real.pi)) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      u (r, θ) * radialPDE D.w (fun s φ => v (s, φ)) r θ -
        v (r, θ) * radialPDE D.w (fun s φ => u (s, φ)) r θ)) = 0 := by
  unfold radialAngularMean
  rw [intervalIntegral.integral_const_mul,
    reference_smooth_green_zero hgeom hu hv hup hvp, mul_zero]

/-- The normalized physical weak pairing is symmetric on smooth periodic fields. -/
theorem reference_smooth_pairing_symm {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) {u v : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hup : Function.Periodic u (0, 2 * Real.pi))
    (hvp : Function.Periodic v (0, 2 * Real.pi)) :
    radialWeakPairing D u v = radialWeakPairing D v u := by
  have huv : Integrable (fun x : PolarPoint =>
      u x * radialPDE D.w (fun r θ => v (r, θ)) x.1 x.2) (radialPhysicalMeasure D) :=
    (r11b_continuous_memLp hu.continuous).integrable_mul
      (r11b_continuous_memLp (r11b_continuous_radialPDE_test hgeom hv))
  have hvu : Integrable (fun x : PolarPoint =>
      v x * radialPDE D.w (fun r θ => u (r, θ)) x.1 x.2) (radialPhysicalMeasure D) :=
    (r11b_continuous_memLp hv.continuous).integrable_mul
      (r11b_continuous_memLp (r11b_continuous_radialPDE_test hgeom hu))
  have hzero := reference_smooth_green_mean_zero hgeom hu hv hup hvp
  rw [r11b_integral_angularMean_eq hgeom.2.1.le (huv.sub hvu),
    integral_sub huv hvu] at hzero
  unfold radialWeakPairing
  rw [r11b_integral_angularMean_eq hgeom.2.1.le huv,
    r11b_integral_angularMean_eq hgeom.2.1.le hvu]
  exact sub_eq_zero.mp (by simpa only [mul_sub] using hzero)

theorem reference_smoothAdmissible_pairing_symm {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) {U V : RadialUnknown}
    (hU : SmoothAdmissibleField D U) (hV : SmoothAdmissibleField D V) :
    radialWeakPairing D U.1 V.1 = radialWeakPairing D V.1 U.1 :=
  reference_smooth_pairing_symm hgeom hU.1 hV.1
    (reference_periodic_two_pi hU.2.1) (reference_periodic_two_pi hV.2.1)

end ContinuousFlexibility.Radial
