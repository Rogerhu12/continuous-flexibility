import ContinuousFlexibility.Radial.InnerWeakGreen

/-!
# First-order integration by parts on the original closed model domain

This is proved on the actual Schrodinger core and then extended by
continuity. The auxiliary test is any smooth function at the closed
interval; it need not vanish at the endpoints because the domain
coordinate does.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff InnerProductSpace

theorem innerEnergyClosure_firstOrder_pairing {a b : ℝ} {V p : ℝ → ℝ}
    (hab : a < b) (hp : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ p x)
    {P Pd u d q : RadialL2}
    (hP : (P : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator p)
    (hPd : (Pd : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator (deriv p))
    (hu : (u, d, q) ∈ closure (IntervalEnergyCore V a b)) :
    ⟪d, P⟫_ℝ + ⟪u, Pd⟫_ℝ = 0 := by
  have hcore : IntervalEnergyCore V a b ⊆
      {v : RadialL2 × RadialL2 × RadialL2 |
        ⟪v.2.1, P⟫_ℝ + ⟪v.1, Pd⟫_ℝ = 0} := by
    intro v hv
    obtain ⟨φ, hφ, _hcφ, hvφ, hvd, _hvq⟩ := hv.1
    have hφout : φ =ᵐ[volume.restrict ((Ioo a b)ᶜ)] (fun _ => 0) :=
      (ae_restrict_of_ae hvφ).symm.trans hv.2
    have hzero := innerDirichlet_representative_zero_outside hab hφ.continuous hφout
    have hφa : φ a = 0 := hzero (by simp : a ∈ (Ioo a b)ᶜ)
    have hφb : φ b = 0 := hzero (by simp : b ∈ (Ioo a b)ᶜ)
    have hpc : ContinuousOn p (Icc a b) :=
      fun x hx => (hp x hx).continuousAt.continuousWithinAt
    have hpdc : ContinuousOn (deriv p) (Icc a b) :=
      innerDirichlet_deriv_continuousOn hp
    have hφc := hφ.continuous.continuousOn
    have hφdc := (hφ.continuous_deriv (by simp)).continuousOn
    have hI₁ : IntervalIntegrable (fun x => deriv p x * φ x) volume a b :=
      (hpdc.mul hφc).intervalIntegrable_of_Icc hab.le
    have hI₂ : IntervalIntegrable (fun x => p x * deriv φ x) volume a b :=
      (hpc.mul hφdc).intervalIntegrable_of_Icc hab.le
    have hparts : (∫ x in a..b, deriv p x * φ x + p x * deriv φ x) = 0 := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le
        (hpc.mul hφc)
        (fun x hx => ((hp x (Ioo_subset_Icc_self hx)).differentiableAt (by simp)).hasDerivAt.mul ((hφ.differentiable (by simp) x).hasDerivAt))
        (hI₁.add hI₂)
      simpa only [Pi.mul_apply, hφa, hφb, mul_zero, sub_self] using h
    rw [intervalIntegral.integral_add hI₁ hI₂] at hparts
    change ⟪v.2.1, P⟫_ℝ + ⟪v.1, Pd⟫_ℝ = 0
    rw [real_inner_comm v.2.1 P, real_inner_comm v.1 Pd,
      innerDirichlet_pairing_indicator hab.le hP hvd,
      innerDirichlet_pairing_indicator hab.le hPd hvφ]
    linarith
  have hclosed : IsClosed {v : RadialL2 × RadialL2 × RadialL2 |
      ⟪v.2.1, P⟫_ℝ + ⟪v.1, Pd⟫_ℝ = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  exact closure_minimal hcore hclosed hu

end ContinuousFlexibility.Radial
