module

public import ContinuousFlexibility.Analysis.N01aReferenceGreen
public import ContinuousFlexibility.Analysis.N01aReferencePureRow
public import ContinuousFlexibility.Scalar.NormalizedConservation

/-!
# The explicit reference eigenfield satisfies the actual weak graph

The scalar Green identity applies to the radial coefficient matrix. Both
normal boundary fluxes vanish because the profile itself vanishes at the
endpoints. This tests the eigenfield against every smooth periodic test,
without imposing a separated form on that test.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

set_option backward.isDefEq.respectTransparency false in
theorem n01a_symmetricDivergence_radialPDE {w : ℝ → ℝ} {u : PolarPoint → ℝ}
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u) {x : PolarPoint} (hx : x.1 ≠ 0) :
    symmetricDivergence (fun p => w p.1) (fun _ => 0)
      (fun p => deriv w p.1 / p.1) u x =
      Radial.radialPDE w (fun r θ => u (r, θ)) x.1 x.2 := by
  have hwd := (contDiff_infty_iff_deriv.mp hw).2
  have hwx := hw.differentiable (by simp) x.1
  have hc : DifferentiableAt ℝ (fun r => deriv w r / r) x.1 :=
    (hwd.differentiable (by simp) x.1).div differentiableAt_id hx
  have hA : DifferentiableAt ℝ (fun p : PolarPoint => w p.1) x :=
    hwx.comp x differentiableAt_fst
  have hC : DifferentiableAt ℝ (fun p : PolarPoint => deriv w p.1 / p.1) x :=
    hc.comp x differentiableAt_fst
  have hAr : radialPartial (fun p : PolarPoint => w p.1) x = deriv w x.1 :=
    Radial.radialPartial_radialHeightField hwx
  have hCθ : angularPartial (fun p : PolarPoint => deriv w p.1 / p.1) x = 0 :=
    Radial.angularPartial_radialHeightField hc
  have hur : DifferentiableAt ℝ (radialPartial u) x :=
    (contDiffAt_radialPartial hu.contDiffAt (m := 1) (by simp)).differentiableAt one_ne_zero
  have huθ : DifferentiableAt ℝ (angularPartial u) x :=
    (contDiffAt_angularPartial hu.contDiffAt (m := 1) (by simp)).differentiableAt one_ne_zero
  rw [Radial.radialPDE_eq_polar_jets hwx hu]
  unfold symmetricDivergence symmetricNormalFlux symmetricAngularFlux
  simp only [zero_mul, add_zero, zero_add]
  rw [radialPartial_mul hA hur, angularPartial_mul hC huθ, hAr, hCθ]
  simp only [zero_mul, zero_add]

theorem n01a_reference_eigenfield_smooth {D : ReferenceData}
    (hD : RadialProfileGeometry D) :
    ContDiff ℝ ∞ (fun p : PolarPoint => D.phi p.1 * Radial.cosineMode 2 p.2) := by
  have hφ := hD.2.2.2.1.1
  unfold Radial.cosineMode
  exact (hφ.comp contDiff_fst).mul
    (contDiff_const.mul (contDiff_const.mul contDiff_snd).cos)

theorem n01a_reference_eigenfield_periodic (D : ReferenceData) :
    Function.Periodic (fun p : PolarPoint => D.phi p.1 * Radial.cosineMode 2 p.2)
      (0, 2 * Real.pi) := by
  intro p
  change D.phi (p.1 + 0) * Radial.cosineMode 2 (p.2 + 2 * Real.pi) = _
  rw [add_zero]
  unfold Radial.cosineMode
  rw [mul_add, Real.cos_add_nat_mul_two_pi]

theorem n01a_reference_eigenfield_pde {D : ReferenceData}
    (hD : RadialProfileGeometry D) (hN : RadialNaturalKernels D)
    {r : ℝ} (hr : r ∈ radialCore D) (θ : ℝ) :
    Radial.radialPDE D.w (fun r θ => D.phi r * Radial.cosineMode 2 θ) r θ = 0 := by
  have hw := hD.2.2.1.1
  have hφ := hD.2.2.2.1.1
  have hφd := (contDiff_infty_iff_deriv.mp hφ).2
  have h := Radial.radialPDE_cosine_lift (w := D.w) (u := D.phi) 2
    (r := r) (θ := θ) (Eventually.of_forall (hφ.differentiable (by simp)))
    ((hw.mul hφd).differentiable (by simp) r)
  simpa only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num, hN.1 r hr, zero_mul] using h

set_option backward.isDefEq.respectTransparency false in
theorem radialWeakPairing_reference_eigenfield {D : ReferenceData}
    (hD : RadialProfileGeometry D) (hN : RadialNaturalKernels D)
    {ψ : PolarPoint → ℝ} (hψ : RadialTest D ψ) :
    radialWeakPairing D (fun p => D.phi p.1 * Radial.cosineMode 2 p.2) ψ = 0 := by
  let Φ : PolarPoint → ℝ := fun p => D.phi p.1 * Radial.cosineMode 2 p.2
  let A : PolarPoint → ℝ := fun p => D.w p.1
  let C : PolarPoint → ℝ := fun p => deriv D.w p.1 / p.1
  have hw := hD.2.2.1.1
  have hwd := (contDiff_infty_iff_deriv.mp hw).2
  have hΦ : ContDiff ℝ ∞ Φ := n01a_reference_eigenfield_smooth hD
  have hr (p : PolarPoint) (hp : p ∈ uIcc D.a D.b ×ˢ uIcc 0 (2 * Real.pi)) : p.1 ≠ 0 := by
    have hpa : p.1 ∈ Icc D.a D.b := by simpa only [uIcc_of_le hD.2.1.le] using hp.1
    exact (hD.1.trans_le hpa.1).ne'
  have hA : ∀ p ∈ uIcc D.a D.b ×ˢ uIcc 0 (2 * Real.pi), ContDiffAt ℝ ∞ A p :=
    fun _ _ => (hw.comp contDiff_fst).contDiffAt
  have hC : ∀ p ∈ uIcc D.a D.b ×ˢ uIcc 0 (2 * Real.pi), ContDiffAt ℝ ∞ C p := by
    intro p hp
    exact (hwd.contDiffAt.comp p contDiffAt_fst).div contDiffAt_fst (hr p hp)
  have hflux (x : ℝ) (hx : D.w x = 0) (θ : ℝ) :
      greenNormalFlux A (fun _ => 0) Φ ψ (x, θ) = 0 := by
    simp only [greenNormalFlux, symmetricNormalFlux, A, hx, zero_mul, add_zero, mul_zero, sub_self]
  have hgreen := integral_symmetric_green_eq_zero_of_periodic hA
    (fun _ _ => contDiffAt_const) hC (fun _ _ => hΦ.contDiffAt)
    (fun _ _ => hψ.1.contDiffAt)
    (show Function.Periodic (fun _ : PolarPoint => (0 : ℝ)) (0, 2 * Real.pi) from fun _ => rfl)
    (show Function.Periodic C (0, 2 * Real.pi) from by intro p; simp only [C, Prod.fst_add, add_zero])
    (n01a_reference_eigenfield_periodic D) hψ.2.1
    (fun θ _ => hflux D.a (hD.2.2.1.2 D.a (Or.inl le_rfl)) θ)
    (fun θ _ => hflux D.b (hD.2.2.1.2 D.b (Or.inr le_rfl)) θ)
  have heq : (∫ r in D.a..D.b, ∫ θ in 0..2 * Real.pi,
      Φ (r, θ) * Radial.radialPDE D.w (fun r θ => ψ (r, θ)) r θ) =
      ∫ r in D.a..D.b, ∫ θ in 0..2 * Real.pi,
        Φ (r, θ) * symmetricDivergence A (fun _ => 0) C ψ (r, θ) -
          ψ (r, θ) * symmetricDivergence A (fun _ => 0) C Φ (r, θ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hD.2.1.le
    intro r hr
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only
    rw [n01a_symmetricDivergence_radialPDE hw hψ.1 (hD.1.trans hr.1).ne',
      n01a_symmetricDivergence_radialPDE hw hΦ (hD.1.trans hr.1).ne']
    simp only [Φ, n01a_reference_eigenfield_pde hD hN hr θ, mul_zero, sub_zero]
  unfold radialWeakPairing radialAngularMean
  rw [intervalIntegral.integral_const_mul]
  change (2 * Real.pi)⁻¹ *
    (∫ r in D.a..D.b, ∫ θ in 0..2 * Real.pi,
      Φ (r, θ) * Radial.radialPDE D.w (fun r θ => ψ (r, θ)) r θ) = 0
  rw [heq, hgreen, mul_zero]

theorem referenceGraph_reference_eigenfield {D : ReferenceData}
    (hD : RadialProfileGeometry D) (hN : RadialNaturalKernels D) (hB : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ}
    (hU : OutputRealization D γ M₁ 0
      ((fun p => D.phi p.1 * Radial.cosineMode 2 p.2), 0)) :
    ReferenceGraph D γ M₀ M₁
      ((fun p => D.phi p.1 * Radial.cosineMode 2 p.2), 0) ((0 : PolarPoint → ℝ), 1) := by
  refine ⟨⟨0, hU⟩, sourceMember_pure_row D γ M₀ 1, referenceRow_phi_cosineMode hB, ?_⟩
  intro ψ hψ
  dsimp only
  rw [radialWeakPairing_reference_eigenfield hD hN hψ]
  simp only [zero_mul, mul_zero, add_zero, Pi.zero_apply, radialAngularMean,
    intervalIntegral.integral_zero]

end ContinuousFlexibility.Statements
