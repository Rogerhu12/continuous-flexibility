import ContinuousFlexibility.Analysis.N01aReferenceModes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Radial Green symmetry and actual modal tests

The flat radial coefficient kills the endpoint Wronskian.  This permits
moving the radial Jacobi operator from an interior cutoff to a smooth
admissible mode before the cutoff is removed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

theorem continuousOn_radialJacobi {w u : ℝ → ℝ} {a b : ℝ}
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u) (ha : 0 < a) (κ : ℝ) :
    ContinuousOn (Radial.radialJacobi κ w u) (Icc a b) := by
  have hud : ContDiff ℝ ∞ (deriv u) := (contDiff_infty_iff_deriv.mp hu).2
  have hflux : Continuous (deriv (fun r => w r * deriv u r)) :=
    (hw.mul hud).continuous_deriv (by simp)
  have hwd : Continuous (deriv w) := hw.continuous_deriv (by simp)
  exact hflux.continuousOn.sub
    (((continuous_const.mul hwd).continuousOn.div continuousOn_id
      (fun r hr => (ha.trans_le hr.1).ne')).mul hu.continuous.continuousOn)

private theorem hasDerivAt_radialGreenPrimitive {w u v : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (κ r : ℝ) :
    HasDerivAt
      (fun x => u x * (w x * deriv v x) - v x * (w x * deriv u x))
      (u r * Radial.radialJacobi κ w v r -
        v r * Radial.radialJacobi κ w u r) r := by
  have hud : ContDiff ℝ ∞ (deriv u) := (contDiff_infty_iff_deriv.mp hu).2
  have hvd : ContDiff ℝ ∞ (deriv v) := (contDiff_infty_iff_deriv.mp hv).2
  have h := (((hu.differentiable (by simp) r).hasDerivAt).mul
      (((hw.mul hvd).differentiable (by simp) r).hasDerivAt)).sub
    (((hv.differentiable (by simp) r).hasDerivAt).mul
      (((hw.mul hud).differentiable (by simp) r).hasDerivAt))
  apply h.congr_deriv
  simp only [Radial.radialJacobi]
  ring

/-- Both endpoint terms vanish because the physical profile is flat there. -/
theorem integral_radialJacobi_symm {w u v : ℝ → ℝ} {a b : ℝ}
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (ha : 0 < a) (hab : a ≤ b) (hwa : w a = 0) (hwb : w b = 0) (κ : ℝ) :
    (∫ r in a..b, u r * Radial.radialJacobi κ w v r) =
      ∫ r in a..b, v r * Radial.radialJacobi κ w u r := by
  have hleft : IntervalIntegrable
      (fun r => u r * Radial.radialJacobi κ w v r) volume a b :=
    (hu.continuous.continuousOn.mul
      (continuousOn_radialJacobi hw hv ha κ)).intervalIntegrable_of_Icc hab
  have hright : IntervalIntegrable
      (fun r => v r * Radial.radialJacobi κ w u r) volume a b :=
    (hv.continuous.continuousOn.mul
      (continuousOn_radialJacobi hw hu ha κ)).intervalIntegrable_of_Icc hab
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => hasDerivAt_radialGreenPrimitive hw hu hv κ r) (hleft.sub hright)
  rw [intervalIntegral.integral_sub hleft hright] at h
  simp only [hwa, hwb, zero_mul, mul_zero, sub_self] at h
  exact sub_eq_zero.mp h

/-- Modal separation is valid even before any measurability of the field is known. -/
theorem radialWeakPairing_cosine_test {D : ReferenceData} {ψ : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ D.w) (hψ : ContDiff ℝ ∞ ψ)
    (u : PolarPoint → ℝ) (j : ℕ) :
    radialWeakPairing D u (fun p => ψ p.1 * Radial.cosineMode j p.2) =
      ∫ r in D.a..D.b,
        referenceMode u j r * Radial.radialJacobi ((j : ℝ) ^ 2) D.w ψ r := by
  have hψd : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hsep (r θ : ℝ) := Radial.radialPDE_cosine_lift (w := D.w) (u := ψ) j
    (r := r) (θ := θ)
    (Eventually.of_forall (hψ.differentiable (by simp)))
    ((hw.mul hψd).differentiable (by simp) r)
  unfold radialWeakPairing
  simp_rw [hsep]
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  rw [show (fun θ => u (r, θ) *
      (Radial.radialJacobi ((j : ℝ) ^ 2) D.w ψ r * Radial.cosineMode j θ)) =
      (fun θ => Radial.radialJacobi ((j : ℝ) ^ 2) D.w ψ r *
        (u (r, θ) * Radial.cosineMode j θ)) by funext θ; ring]
  rw [radialAngularMean_const_mul]
  exact mul_comm _ _

theorem radialTest_cosine {D : ReferenceData} {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ radialCore D) (j : ℕ) :
    RadialTest D (fun p => ψ p.1 * Radial.cosineMode j p.2) := by
  refine ⟨?_, ?_, tsupport ψ, hc, hs, ?_⟩
  · unfold Radial.cosineMode
    fun_prop
  · intro p
    change ψ (p.1 + 0) * Radial.cosineMode j (p.2 + 2 * Real.pi) =
      ψ p.1 * Radial.cosineMode j p.2
    rw [add_zero]
    unfold Radial.cosineMode
    rw [mul_add, Real.cos_add_nat_mul_two_pi]
  · intro r hr θ
    dsimp only
    rw [image_eq_zero_of_notMem_tsupport hr, zero_mul]

theorem referenceColumn_cosine_test (D : ReferenceData) (ψ : ℝ → ℝ) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      referenceColumn D r * Radial.cosineMode 2 θ *
        (ψ r * Radial.cosineMode 2 θ))) =
      ∫ r in D.a..D.b, referenceColumn D r * ψ r := by
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  rw [show (fun θ => referenceColumn D r * Radial.cosineMode 2 θ *
      (ψ r * Radial.cosineMode 2 θ)) =
      (fun θ => (referenceColumn D r * ψ r) *
        (Radial.cosineMode 2 θ * Radial.cosineMode 2 θ)) by funext θ; ring]
  rw [radialAngularMean_const_mul,
    radialAngularMean_cosineMode_product 2 2 (by decide) (by decide)]
  simp only [if_true, mul_one]

end ContinuousFlexibility.Statements
