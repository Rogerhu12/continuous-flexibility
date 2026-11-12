import ContinuousFlexibility.Analysis.PhysicalTransmissionOperator
import ContinuousFlexibility.Radial.R11bRadialTests
import ContinuousFlexibility.Scalar.GreenIdentity

/-!
# Physical Green symmetry for N07b

A compact radial test and both of its first partials vanish at the radial
endpoints. The existing rectangle Green identity therefore gives symmetry
against every full-period radial test. All angular averages in this module
use the same full period as the frozen radial test space.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- A radial test and its first partials vanish outside the open core. -/
theorem n07b_radialTest_jets_zero_of_not_mem_core {D : ReferenceData}
    {φ : PolarPoint → ℝ} (hφ : RadialTest D φ) {r : ℝ}
    (hr : r ∉ radialCore D) (θ : ℝ) :
    φ (r, θ) = 0 ∧ radialPartial φ (r, θ) = 0 ∧
      angularPartial φ (r, θ) = 0 := by
  obtain ⟨K, hK, hKcore, hzero⟩ := hφ.2.2
  have hrK : r ∉ K := fun h => hr (hKcore h)
  exact ⟨hzero r hrK θ,
    Radial.r11b_directionalPartial_zero_outside hK.isClosed hzero (1, 0) hrK θ,
    Radial.r11b_directionalPartial_zero_outside hK.isClosed hzero (0, 1) hrK θ⟩

/-- No boundary condition on the other function is needed for a compact test. -/
theorem n07b_greenNormalFlux_zero_of_radialTest {D : ReferenceData}
    (A B u : PolarPoint → ℝ) {φ : PolarPoint → ℝ} (hφ : RadialTest D φ)
    {r : ℝ} (hr : r ∉ radialCore D) (θ : ℝ) :
    greenNormalFlux A B u φ (r, θ) = 0 := by
  obtain ⟨hv, hr', hθ⟩ := n07b_radialTest_jets_zero_of_not_mem_core hφ hr θ
  simp only [greenNormalFlux, symmetricNormalFlux, hv, hr', hθ,
    mul_zero, zero_mul, add_zero, sub_zero]

/-- Subtraction in the full-period physical pairing, with actual integrability. -/
theorem n07b_integral_radialAngularMean_sub (D : ReferenceData)
    {f g : PolarPoint → ℝ} (hf : Continuous f) (hg : Continuous g) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ) - g (r, θ))) =
      (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ))) -
        (∫ r in D.a..D.b, radialAngularMean (fun θ => g (r, θ))) := by
  have hfi : Continuous (fun r => ∫ θ in (0 : ℝ)..2 * Real.pi, f (r, θ)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun r θ => f (r, θ)) hf 0 (2 * Real.pi)
  have hgi : Continuous (fun r => ∫ θ in (0 : ℝ)..2 * Real.pi, g (r, θ)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun r θ => g (r, θ)) hg 0 (2 * Real.pi)
  have he (r : ℝ) :
      (∫ θ in (0 : ℝ)..2 * Real.pi, f (r, θ) - g (r, θ)) =
        (∫ θ in (0 : ℝ)..2 * Real.pi, f (r, θ)) -
          (∫ θ in (0 : ℝ)..2 * Real.pi, g (r, θ)) :=
    intervalIntegral.integral_sub
      ((hf.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 (2 * Real.pi))
      ((hg.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 (2 * Real.pi))
  have hfm : Continuous (fun r =>
      (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, f (r, θ)) :=
    continuous_const.mul hfi
  have hgm : Continuous (fun r =>
      (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, g (r, θ)) :=
    continuous_const.mul hgi
  simp_rw [radialAngularMean, he, mul_sub]
  exact intervalIntegral.integral_sub (hfm.intervalIntegrable D.a D.b)
    (hgm.intervalIntegrable D.a D.b)

/-- Actual Green symmetry for a smooth symmetric divergence operator and a
compact radial test, with the full-period angular average. -/
theorem n07b_physical_green {D : ReferenceData} {L : SymmetricCoefficients}
    {u φ : PolarPoint → ℝ}
    (hA : ContDiff ℝ ∞ L.a) (hB : ContDiff ℝ ∞ L.b) (hC : ContDiff ℝ ∞ L.c)
    (hu : ContDiff ℝ ∞ u)
    (hBp : Function.Periodic L.b (0, 2 * Real.pi))
    (hCp : Function.Periodic L.c (0, 2 * Real.pi))
    (hup : Function.Periodic u (0, 2 * Real.pi)) (hφ : RadialTest D φ) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      u (r, θ) * divergenceOperator L φ (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ =>
        divergenceOperator L u (r, θ) * φ (r, θ)) := by
  have hgreen := integral_symmetric_green_eq_zero_of_periodic
    (A := L.a) (B := L.b) (C := L.c) (φ := u) (ψ := φ)
    (a := D.a) (b := D.b) (T := 2 * Real.pi)
    (fun _ _ => hA.contDiffAt) (fun _ _ => hB.contDiffAt)
    (fun _ _ => hC.contDiffAt) (fun _ _ => hu.contDiffAt)
    (fun _ _ => hφ.1.contDiffAt) hBp hCp hup hφ.2.1
    (fun θ _ => n07b_greenNormalFlux_zero_of_radialTest L.a L.b u hφ (r := D.a)
      (fun h => (lt_irrefl D.a) h.1) θ)
    (fun θ _ => n07b_greenNormalFlux_zero_of_radialTest L.a L.b u hφ (r := D.b)
      (fun h => (lt_irrefl D.b) h.2) θ)
  change (∫ r in D.a..D.b, ∫ θ in (0 : ℝ)..2 * Real.pi,
    u (r, θ) * divergenceOperator L φ (r, θ) -
      φ (r, θ) * divergenceOperator L u (r, θ)) = 0 at hgreen
  have hraw : (∫ r in D.a..D.b, ∫ θ in (0 : ℝ)..2 * Real.pi,
      u (r, θ) * divergenceOperator L φ (r, θ) -
        divergenceOperator L u (r, θ) * φ (r, θ)) = 0 := by
    calc
      _ = ∫ r in D.a..D.b, ∫ θ in (0 : ℝ)..2 * Real.pi,
          u (r, θ) * divergenceOperator L φ (r, θ) -
            φ (r, θ) * divergenceOperator L u (r, θ) := by
        apply intervalIntegral.integral_congr
        intro r _
        apply intervalIntegral.integral_congr
        intro θ _
        ring
      _ = 0 := hgreen
  have hzero : (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      u (r, θ) * divergenceOperator L φ (r, θ) -
        divergenceOperator L u (r, θ) * φ (r, θ))) = 0 := by
    change (∫ r in D.a..D.b, (2 * Real.pi)⁻¹ *
      (∫ θ in (0 : ℝ)..2 * Real.pi,
        u (r, θ) * divergenceOperator L φ (r, θ) -
          divergenceOperator L u (r, θ) * φ (r, θ))) = 0
    rw [intervalIntegral.integral_const_mul, hraw, mul_zero]
  have hf : Continuous (fun p => u p * divergenceOperator L φ p) :=
    hu.continuous.mul (contDiff_divergenceOperator hA hB hC hφ.1).continuous
  have hg : Continuous (fun p => divergenceOperator L u p * φ p) :=
    (contDiff_divergenceOperator hA hB hC hu).continuous.mul hφ.1.continuous
  exact sub_eq_zero.mp ((n07b_integral_radialAngularMean_sub D hf hg).symm.trans hzero)

/-- Half-period coefficients and heights also satisfy the full-period Green identity. -/
theorem n07b_physical_green_of_pi_periodic {D : ReferenceData}
    {L : SymmetricCoefficients} {u φ : PolarPoint → ℝ}
    (hA : ContDiff ℝ ∞ L.a) (hB : ContDiff ℝ ∞ L.b) (hC : ContDiff ℝ ∞ L.c)
    (hu : ContDiff ℝ ∞ u)
    (hBp : Function.Periodic L.b (0, Real.pi))
    (hCp : Function.Periodic L.c (0, Real.pi))
    (hup : Function.Periodic u (0, Real.pi)) (hφ : RadialTest D φ) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      u (r, θ) * divergenceOperator L φ (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ =>
        divergenceOperator L u (r, θ) * φ (r, θ)) := by
  apply n07b_physical_green hA hB hC hu
  · simpa only [Prod.mk_add_mk, zero_add, two_mul] using hBp.add_period hBp
  · simpa only [Prod.mk_add_mk, zero_add, two_mul] using hCp.add_period hCp
  · simpa only [Prod.mk_add_mk, zero_add, two_mul] using hup.add_period hup
  · exact hφ

end ContinuousFlexibility.Analysis
