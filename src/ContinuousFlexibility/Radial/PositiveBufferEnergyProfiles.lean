module

public import ContinuousFlexibility.Radial.PositiveBufferEnergyClassical
public import ContinuousFlexibility.Radial.PositiveBufferEnergyIdentities

/-!
# Existence of the finite and exterior positive-buffer profiles

The profiles in this file are obtained from actual minimizers in the weak
energy graph. Their trace values are inherited from a compact smooth lift.
The ordinary ODE continuation supplies globally smooth representatives, and
the regional physical energy is bounded by the energy of the lift.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

theorem positiveBuffer_exists_finite_profile {V : ℝ → ℝ}
    (hreal : ActualClosedFormRealization V) (hV : ContDiff ℝ ∞ V)
    {m a b : ℝ} (hm : 0 < m) (hab : a < b)
    (hVm : ∀ x ∈ Icc a b, m ^ 2 ≤ V x)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hpos : ∀ x ∈ Icc a b ∪ Function.support φ, 0 ≤ V x) :
    ∃ p : ℝ → ℝ, ContDiff ℝ ∞ p ∧ p a = φ a ∧ p b = φ b ∧
      (∀ x ∈ Ioo a b, -deriv (deriv p) x + V x * p x = 0) ∧
      (∫ x in a..b, deriv p x ^ 2 + V x * p x ^ 2) ≤
        ∫ x : ℝ, deriv φ x ^ 2 + V x * φ x ^ 2 := by
  obtain ⟨u, U, hU, hue, _, hderiv, _, htrace, _, hstationary, hmin, _⟩ :=
    positiveBuffer_exists_variational_profile hreal hV.continuous hm (Icc a b)
      isClosed_Icc hVm φ hφ hcφ
  obtain ⟨p, hp, hpU, hpu, hpd, hODE⟩ := positiveBuffer_stationary_finite_smooth_profile
    hV (Icc a b) measurableSet_Icc u hstationary hU hue hderiv hab Ioo_subset_Icc_self
  have ha : a ∈ closure (Icc a b)ᶜ := by simp [closure_compl, interior_Icc]
  have hb : b ∈ closure (Icc a b)ᶜ := by simp [closure_compl, interior_Icc]
  refine ⟨p, hp, (hpU (left_mem_Icc.mpr hab.le)).trans (htrace ha),
    (hpU (right_mem_Icc.mpr hab.le)).trans (htrace hb), ?_, ?_⟩
  · intro x hx
    exact hODE x ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
    have hnonneg := positiveBufferEnergyDensity_nonneg_of_trace u (Icc a b) hue htrace hpos
    have hle := (positiveBuffer_classical_energy_le hV.continuous u (Ioo a b)
      hnonneg hpu hpd).trans hmin
    simpa only [positiveBufferCompactEnergyLift_self_eq_integral] using hle

/-- A single finite boundary point can be filled from a finite ODE
continuation, while keeping the actual minimizer on the whole open region.
The geometric hypotheses are satisfied by either half-line. -/
theorem positiveBuffer_exists_single_boundary_profile {V : ℝ → ℝ}
    (hreal : ActualClosedFormRealization V) (hV : ContDiff ℝ ∞ V)
    {m c a b : ℝ} (hm : 0 < m) {O : Set ℝ} (hO : IsOpen O)
    (hS : IsClosed (insert c O)) (hc : c ∈ closure (insert c O)ᶜ)
    (hab : a < b) (hsub : Ioo a b ⊆ insert c O)
    (hnear : ∀ᶠ x in 𝓝 c, x ∈ insert c O → x ∈ Icc a b)
    (hVm : ∀ x ∈ insert c O, m ^ 2 ≤ V x)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hpos : ∀ x ∈ insert c O ∪ Function.support φ, 0 ≤ V x) :
    ∃ p : ℝ → ℝ, ContDiff ℝ ∞ p ∧ p c = φ c ∧
      MemLp p 2 (volume.restrict O) ∧
      IntegrableOn (fun x => deriv p x ^ 2 + V x * p x ^ 2) O volume ∧
      (∀ x ∈ O, -deriv (deriv p) x + V x * p x = 0) ∧
      (∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ insert c O, |p x| ≤ M) ∧
      (∫ x in O, deriv p x ^ 2 + V x * p x ^ 2) ≤
        ∫ x : ℝ, deriv φ x ^ 2 + V x * φ x ^ 2 := by
  let s := insert c O
  obtain ⟨u, U, hU, hue, _, hderiv, hbound, htrace, _, hstationary, hmin, _⟩ :=
    positiveBuffer_exists_variational_profile hreal hV.continuous hm s hS hVm φ hφ hcφ
  obtain ⟨p₀, hp₀, hp₀U, _, _, _⟩ := positiveBuffer_stationary_finite_smooth_profile
    hV s hS.measurableSet u hstationary hU hue hderiv hab hsub
  obtain ⟨hUsm, hUODE⟩ := positiveBuffer_stationary_smooth_on_open
    hV s hS.measurableSet u hstationary hU hue hO (subset_insert c O)
  have hnear' : ∀ᶠ x in 𝓝 c, x ∈ insert c O → U x = p₀ x := by
    filter_upwards [hnear] with x hx hxs
    exact (hp₀U (hx hxs)).symm
  obtain ⟨p, hp, hpU, _, hpUdd⟩ := positiveBuffer_glue_boundary_smooth hO hS hUsm hp₀ hnear'
  have hpUo := hpU.mono (subset_insert c O)
  have hpu : (positiveBufferEnergyCoordinate V 0 u : ℝ → ℝ) =ᵐ[volume.restrict O] p := by
    filter_upwards [ae_restrict_of_ae hue, ae_restrict_mem hO.measurableSet] with x hx hxs
    exact hx.trans (hpUo hxs).symm
  have hpd := positiveBuffer_classical_derivative_ae u hO hderiv hpUo
  refine ⟨p, hp, (hpU (mem_insert c O)).trans (htrace hc),
    (memLp_congr_ae hpu).mp ((Lp.memLp (positiveBufferEnergyCoordinate V 0 u)).restrict O),
    positiveBuffer_classical_energy_integrableOn hV.continuous u O hpu hpd, ?_, ?_, ?_⟩
  · intro x hx
    rw [hpUdd hx, hpUo hx]
    exact hUODE x hx
  · refine ⟨‖positiveBufferEnergyCoordinate V 0 u‖ +
      ‖positiveBufferEnergyCoordinate V 1 u‖, by positivity, ?_⟩
    intro x hx
    rw [hpU hx]
    exact hbound x
  · have hnonneg := positiveBufferEnergyDensity_nonneg_of_trace u s hue htrace hpos
    have hle := (positiveBuffer_classical_energy_le hV.continuous u O hnonneg hpu hpd).trans hmin
    simpa only [positiveBufferCompactEnergyLift_self_eq_integral] using hle

/-- The concrete unit-trace lift gives a finite homogeneous profile with
zero value at the far wall and energy comparable to the mass. Both
orientations use the same theorem. -/
theorem positiveBuffer_exists_finite_unit_profile {V : ℝ → ℝ}
    (hreal : ActualClosedFormRealization V) (hV : ContDiff ℝ ∞ V)
    {m C₀ c w : ℝ} (hm : 0 < m) (hC₀ : 0 ≤ C₀)
    (hwall : 2 / m ≤ |w - c|)
    (hVm : ∀ x ∈ uIcc c w ∪ Icc (c - 2 / m) (c + 2 / m), m ^ 2 ≤ V x)
    (hupper : ∀ x, |x - c| ≤ 2 / m → V x ≤ C₀ * m ^ 2) :
    ∃ p : ℝ → ℝ, ContDiff ℝ ∞ p ∧ p c = 1 ∧ p w = 0 ∧
      (∀ x ∈ Ioo (min c w) (max c w), -deriv (deriv p) x + V x * p x = 0) ∧
      (∫ x in min c w..max c w, deriv p x ^ 2 + V x * p x ^ 2) =
        (if c < w then -deriv p c else deriv p c) ∧
      m ≤ (∫ x in min c w..max c w, deriv p x ^ 2 + V x * p x ^ 2) ∧
      (∫ x in min c w..max c w, deriv p x ^ 2 + V x * p x ^ 2) ≤
        4 * (morseCutoffDerivativeConstant ^ 2 + C₀) * m := by
  have hcw : c ≠ w := by
    intro heq
    rw [← heq, sub_self, abs_zero] at hwall
    exact (by positivity : (0 : ℝ) < 2 / m).not_ge hwall
  have hab : min c w < max c w := min_lt_max.mpr hcw
  let φ := positiveBufferTraceLift c m
  have hφ := contDiff_positiveBufferTraceLift c m
  have hcφ := positiveBufferTraceLift_hasCompactSupport c hm
  have hVmI : ∀ x ∈ Icc (min c w) (max c w), m ^ 2 ≤ V x :=
    fun x hx => hVm x (Or.inl hx)
  have hpos : ∀ x ∈ Icc (min c w) (max c w) ∪ Function.support φ, 0 ≤ V x := by
    intro x hx
    apply (sq_nonneg m).trans
    apply hVm x
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (positiveBufferTraceLift_tsupport_subset c hm (subset_tsupport φ hx))
  obtain ⟨p, hp, hpa, hpb, hODE, hE⟩ := positiveBuffer_exists_finite_profile
    hreal hV hm hab hVmI φ hφ hcφ hpos
  have hpc : p c = 1 := by
    rcases le_total c w with h | h
    · simpa only [min_eq_left h, φ, positiveBufferTraceLift_at_cut] using hpa
    · simpa only [max_eq_left h, φ, positiveBufferTraceLift_at_cut] using hpb
  have hpw : p w = 0 := by
    have hφw := positiveBufferTraceLift_eq_zero (c := c) hm hwall
    rcases le_total c w with h | h
    · simpa only [max_eq_right h, φ, hφw] using hpb
    · simpa only [min_eq_right h, φ, hφw] using hpa
  have hpd := (contDiff_infty_iff_deriv.mp hp).2
  have hp' (x : ℝ) : HasDerivAt p (deriv p x) x :=
    (hp.differentiable (by simp) x).hasDerivAt
  have hp'' (x : ℝ) (hx : x ∈ Ioo (min c w) (max c w)) :
      HasDerivAt (deriv p) (V x * p x) x := by
    convert (hpd.differentiable (by simp) x).hasDerivAt using 1
    linarith [hODE x hx]
  refine ⟨p, hp, hpc, hpw, hODE, ?_, ?_, ?_⟩
  · rw [positiveBuffer_energy_eq_flux hab.le hp.continuous.continuousOn
      hpd.continuous.continuousOn hV.continuous.continuousOn (fun x _ => hp' x) hp'']
    by_cases h : c < w
    · simp only [min_eq_left h.le, max_eq_right h.le, hpc, hpw, zero_mul, one_mul,
        zero_sub, if_pos h]
    · have hwc : w ≤ c := le_of_not_gt h
      simp only [min_eq_right hwc, max_eq_left hwc, hpc, hpw, zero_mul, one_mul,
        sub_zero, if_neg h]
  · apply positiveBuffer_unit_trace_energy hab.le hm.le hp.continuous.continuousOn
      hpd.continuous.continuousOn hV.continuous.continuousOn (fun x _ => hp' x) hVmI
    rcases le_total c w with h | h
    · exact Or.inl ⟨by simpa only [min_eq_left h] using hpc,
        by simpa only [max_eq_right h] using hpw⟩
    · exact Or.inr ⟨by simpa only [min_eq_right h] using hpw,
        by simpa only [max_eq_left h] using hpc⟩
  · exact hE.trans (positiveBufferTraceLift_energy_bound hV.continuous c hm hC₀ hupper)

end ContinuousFlexibility.Radial
