import ContinuousFlexibility.Radial.InnerWeakFlux

/-!
# Actual endpoint traces on the interval energy domain

The two traces are continuous L² pairings of the field and its derivative
against fixed affine hats. On the actual energy closure they vanish; on
a smooth representative they equal its endpoint values. Thus the trace
used for finite-piece matching is determined by the field and derivative,
rather than being an independently supplied boundary label.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

theorem innerEnergyClosure_derivative_pairing {a b : ℝ} {V p : ℝ → ℝ}
    (hab : a < b) (hp : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ p x)
    {P Pd u d q : RadialL2}
    (hP : (P : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator p)
    (hPd : (Pd : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator (deriv p))
    (hu : (u, d, q) ∈ closure (IntervalEnergyCore V a b)) :
    ⟪d, P⟫_ℝ + ⟪u, Pd⟫_ℝ = 0 := by
  have hpc : ContinuousOn p (Icc a b) :=
    fun x hx => (hp x hx).continuousAt.continuousWithinAt
  have hpdc := innerDirichlet_deriv_continuousOn hp
  have hcore : IntervalEnergyCore V a b ⊆
      {v : RadialL2 × RadialL2 × RadialL2 |
        ⟪v.2.1, P⟫_ℝ + ⟪v.1, Pd⟫_ℝ = 0} := by
    intro v hv
    obtain ⟨φ, hφ, hcφ, hvφ, hvd, hvq⟩ := hv.1
    have hvφout : (v.1 : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo a b)ᶜ)] φ :=
      ae_restrict_of_ae hvφ
    have hφout : φ =ᵐ[volume.restrict ((Ioo a b)ᶜ)] (fun _ => 0) :=
      Filter.EventuallyEq.trans (Filter.EventuallyEq.symm hvφout) hv.2
    have hz := innerDirichlet_representative_zero_outside hab hφ.continuous hφout
    have hφa : φ a = 0 := hz (by simp : a ∈ (Ioo a b)ᶜ)
    have hφb : φ b = 0 := hz (by simp : b ∈ (Ioo a b)ᶜ)
    have hI₁ := (hpdc.mul hφ.continuous.continuousOn).intervalIntegrable_of_Icc hab.le
    have hI₂ := (hpc.mul (hφ.continuous_deriv (by simp)).continuousOn).intervalIntegrable_of_Icc
      hab.le
    have hFTC : (∫ x in a..b, deriv p x * φ x + p x * deriv φ x) = 0 := by
      have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le
        (hpc.mul hφ.continuous.continuousOn)
        (fun x hx => ((hp x (Ioo_subset_Icc_self hx)).differentiableAt (by simp)).hasDerivAt.mul
          (hφ.differentiable (by simp) x).hasDerivAt) (hI₁.add hI₂)
      simpa only [Pi.mul_apply, hφa, hφb, mul_zero, sub_self] using he
    rw [intervalIntegral.integral_add hI₁ hI₂] at hFTC
    change ⟪v.2.1, P⟫_ℝ + ⟪v.1, Pd⟫_ℝ = 0
    rw [real_inner_comm P v.2.1, real_inner_comm Pd v.1,
      innerDirichlet_pairing_indicator hab.le hP hvd,
      innerDirichlet_pairing_indicator hab.le hPd hvφ]
    linarith
  have hclosed : IsClosed {v : RadialL2 × RadialL2 × RadialL2 |
      ⟪v.2.1, P⟫_ℝ + ⟪v.1, Pd⟫_ℝ = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  exact closure_minimal hcore hclosed hu

/-- Boundary values of the canonical hat for one endpoint. -/
def innerEndpointValues (i : Fin 2) (k : Fin 2) : ℝ := if i = k then 1 else 0

def innerIntervalTrace (a b : ℝ) (u d : RadialL2) (i : Fin 2) : ℝ :=
  bufferSign i *
    (⟪d, innerIntervalBoundaryLiftL2 a b (innerEndpointValues i)⟫_ℝ +
      ⟪u, innerIntervalBoundaryDerivL2 a b (innerEndpointValues i)⟫_ℝ)

theorem innerIntervalTrace_zero_of_energyClosure {a b : ℝ} {V : ℝ → ℝ}
    (hab : a < b) {u d q : RadialL2}
    (hu : (u, d, q) ∈ closure (IntervalEnergyCore V a b)) :
    innerIntervalTrace a b u d = 0 := by
  funext i
  have he := innerEnergyClosure_derivative_pairing hab
    (fun _ _ => (innerIntervalAffineLift_contDiff a b (innerEndpointValues i)).contDiffAt)
    (innerIntervalBoundaryLiftL2_ae a b (innerEndpointValues i))
    (innerIntervalBoundaryDerivL2_ae a b (innerEndpointValues i)) hu
  simp only [innerIntervalTrace, he, mul_zero, Pi.zero_apply]

theorem innerWeakGreen_pairing_indicators {a b : ℝ} (hab : a ≤ b)
    {u v : RadialL2} {f g : ℝ → ℝ}
    (hu : (u : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator f)
    (hv : (v : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator g) :
    ⟪u, v⟫_ℝ = ∫ x in a..b, f x * g x := by
  rw [L2.inner_def]
  calc
    (∫ x : ℝ, ⟪u x, v x⟫_ℝ) =
        ∫ x : ℝ, (Ioo a b).indicator (fun y => f y * g y) x := by
      apply integral_congr_ae
      filter_upwards [hu, hv] with x hux hvx
      rw [hux, hvx]
      by_cases hx : x ∈ Ioo a b
      · simp only [Set.indicator_of_mem hx, RCLike.inner_apply, conj_trivial]
        ring
      · simp only [Set.indicator_of_notMem hx, inner_zero_left]
    _ = ∫ x in Ioo a b, f x * g x := integral_indicator measurableSet_Ioo
    _ = ∫ x in a..b, f x * g x := by
      rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

/-- The trace pairings are the actual endpoint product from FTC. -/
theorem innerSmooth_trace_pairing {a b : ℝ} {φ p : ℝ → ℝ}
    (hab : a < b) (hφ : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ φ x)
    (hp : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ p x)
    {u d P Pd : RadialL2}
    (hu : (u : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator φ)
    (hd : (d : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator (deriv φ))
    (hP : (P : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator p)
    (hPd : (Pd : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator (deriv p)) :
    ⟪d, P⟫_ℝ + ⟪u, Pd⟫_ℝ = p b * φ b - p a * φ a := by
  have hφc : ContinuousOn φ (Icc a b) :=
    fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  have hpc : ContinuousOn p (Icc a b) :=
    fun x hx => (hp x hx).continuousAt.continuousWithinAt
  have hI₁ := ((innerDirichlet_deriv_continuousOn hp).mul hφc).intervalIntegrable_of_Icc hab.le
  have hI₂ := (hpc.mul (innerDirichlet_deriv_continuousOn hφ)).intervalIntegrable_of_Icc hab.le
  have hFTC : (∫ x in a..b, deriv p x * φ x + p x * deriv φ x) =
      p b * φ b - p a * φ a := by
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le (hpc.mul hφc)
      (fun x hx => ((hp x (Ioo_subset_Icc_self hx)).differentiableAt (by simp)).hasDerivAt.mul
        ((hφ x (Ioo_subset_Icc_self hx)).differentiableAt (by simp)).hasDerivAt) (hI₁.add hI₂)
    simpa only [Pi.mul_apply] using he
  rw [intervalIntegral.integral_add hI₁ hI₂] at hFTC
  rw [real_inner_comm P d, real_inner_comm Pd u,
    innerWeakGreen_pairing_indicators hab.le hP hd,
    innerWeakGreen_pairing_indicators hab.le hPd hu]
  linarith

/-- On a smooth representative, the trace is its true boundary value. -/
theorem innerIntervalTrace_smooth {a b : ℝ} {φ : ℝ → ℝ}
    (hab : a < b) (hφ : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ φ x)
    {u d : RadialL2}
    (hu : (u : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator φ)
    (hd : (d : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator (deriv φ))
    (i : Fin 2) :
    innerIntervalTrace a b u d i = if i = 0 then φ a else φ b := by
  have hpair := innerSmooth_trace_pairing hab hφ
    (fun _ _ => (innerIntervalAffineLift_contDiff a b (innerEndpointValues i)).contDiffAt)
    hu hd (innerIntervalBoundaryLiftL2_ae a b (innerEndpointValues i))
    (innerIntervalBoundaryDerivL2_ae a b (innerEndpointValues i))
  have hends := innerIntervalAffineLift_endpoints hab (innerEndpointValues i)
  rw [hends.1, hends.2] at hpair
  rw [innerIntervalTrace, hpair]
  fin_cases i <;> norm_num [bufferSign, innerEndpointValues]

/-- The trace is a linear map on the field and derivative coordinates. -/
def innerIntervalTraceLinear (a b : ℝ) : (RadialL2 × RadialL2) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun U := innerIntervalTrace a b U.1 U.2
  map_add' U V := by
    funext i
    simp only [innerIntervalTrace, Prod.fst_add, Prod.snd_add, Pi.add_apply, inner_add_left]
    ring
  map_smul' r U := by
    funext i
    simp only [innerIntervalTrace, Prod.fst_smul, Prod.snd_smul, Pi.smul_apply,
      real_inner_smul_left, smul_eq_mul]
    ring

@[simp] theorem innerIntervalTraceLinear_apply (a b : ℝ) (U : RadialL2 × RadialL2) :
    innerIntervalTraceLinear a b U = innerIntervalTrace a b U.1 U.2 := rfl

end ContinuousFlexibility.Radial
