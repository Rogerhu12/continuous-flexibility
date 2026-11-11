import ContinuousFlexibility.Radial.PositiveBufferEnergyIntegral
import ContinuousFlexibility.Radial.PositiveBufferWeakRegularity
import ContinuousFlexibility.Radial.PositiveBufferSmoothExtension

/-!
# Classical representatives of stationary buffer profiles

Stationarity in the genuine energy graph implies the distributional
Schrödinger equation.  Local regularity and ordinary scalar ODE uniqueness
then supply smooth profiles through finite endpoints, and smoothness on
every open part of a stationary region.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

theorem positiveBuffer_stationary_localWeakEquation {V : ℝ → ℝ} (hV : Continuous V)
    (s : Set ℝ) (hs : MeasurableSet s) (u : PositiveBufferEnergy V)
    (hu : ∀ v : PositiveBufferEnergy V, v ∈ positiveBufferSupportedEnergyGraph V s hs →
      positiveBufferEnergyForm V hV u v = 0)
    {a b : ℝ} (hab : Ioo a b ⊆ s) :
    PositiveBufferLocalWeakEquation V (positiveBufferEnergyCoordinate V 0 u) (fun _ => 0) a b := by
  intro φ hφ hcφ hsφ
  have hφ' := (contDiff_infty_iff_deriv.mp hφ).2
  have hφ'' := (contDiff_infty_iff_deriv.mp hφ').2
  have huLI := (Lp.memLp (positiveBufferEnergyCoordinate V 0 u)).locallyIntegrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  have htest : Integrable (fun x => positiveBufferEnergyCoordinate V 0 u x *
      deriv (deriv φ) x) volume := by
    simpa only [smul_eq_mul] using
      huLI.integrable_smul_right_of_hasCompactSupport hφ''.continuous hcφ.deriv.deriv
  have hpot : Integrable (fun x => V x * positiveBufferEnergyCoordinate V 0 u x * φ x) volume := by
    apply (positiveBufferPotential_pairing_integrable V hV u
      (positiveBufferCompactEnergyLift V hV φ hφ hcφ)).congr
    filter_upwards [positiveBufferCompactEnergyLift_base_ae V hV φ hφ hcφ] with x hx
    rw [hx]
  have hweak := positiveBuffer_stationary_weak_equation V hV s hs u hu φ hφ hcφ
    ((subset_tsupport φ).trans (hsφ.trans hab))
  have hsplit : (∫ x : ℝ, positiveBufferEnergyCoordinate V 0 u x *
      (-deriv (deriv φ) x + V x * φ x)) =
      -(∫ x : ℝ, positiveBufferEnergyCoordinate V 0 u x * deriv (deriv φ) x) +
        ∫ x : ℝ, V x * positiveBufferEnergyCoordinate V 0 u x * φ x := by
    calc
      _ = ∫ x : ℝ, -(positiveBufferEnergyCoordinate V 0 u x * deriv (deriv φ) x) +
          V x * positiveBufferEnergyCoordinate V 0 u x * φ x := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = _ := by rw [integral_add htest.neg hpot, integral_neg]
  rw [hsplit, hweak]
  simp

/-- A stationary energy profile has a globally smooth continuation agreeing
with its continuous representative on an entire finite closed interval.
The actual weak derivative agrees almost everywhere with the continuation's
ordinary derivative. -/
theorem positiveBuffer_stationary_finite_smooth_profile {V U : ℝ → ℝ}
    (hV : ContDiff ℝ ∞ V) (s : Set ℝ) (hs : MeasurableSet s)
    (u : PositiveBufferEnergy V)
    (hu : ∀ v : PositiveBufferEnergy V, v ∈ positiveBufferSupportedEnergyGraph V s hs →
      positiveBufferEnergyForm V hV.continuous u v = 0)
    (hU : Continuous U)
    (hue : (positiveBufferEnergyCoordinate V 0 u : ℝ → ℝ) =ᵐ[volume] U)
    (hderiv : ∀ᵐ x : ℝ, HasDerivAt U (positiveBufferEnergyCoordinate V 1 u x) x)
    {a b : ℝ} (hab : a < b) (hsub : Ioo a b ⊆ s) :
    ∃ p : ℝ → ℝ, ContDiff ℝ ∞ p ∧ EqOn p U (Icc a b) ∧
      (positiveBufferEnergyCoordinate V 0 u : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] p ∧
      (positiveBufferEnergyCoordinate V 1 u : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] deriv p ∧
      ∀ x ∈ Ioo (a - 1) (b + 1), -deriv (deriv p) x + V x * p x = 0 := by
  obtain ⟨U₀, D₀, hU₀, hD₀, hu₀, _, hU₀d, hD₀d⟩ :=
    positiveBuffer_local_classical_representative hab hV.continuous continuous_const
      (positiveBufferEnergy_derivative_weak V u)
      (positiveBuffer_stationary_localWeakEquation hV.continuous s hs u hu hsub)
  have heq : EqOn U₀ U (Ioo a b) := MeasureTheory.Measure.eqOn_open_of_ae_eq
    (hu₀.symm.trans (ae_restrict_of_ae hue)) isOpen_Ioo hU₀.continuousOn hU.continuousOn
  have heqcc : EqOn U₀ U (Icc a b) := by
    simpa only [closure_Ioo hab.ne] using heq.closure hU₀ hU
  have hD₀d' : ∀ x ∈ Ioo a b, HasDerivAt D₀ (V x * U₀ x) x := by
    simpa only [sub_zero] using hD₀d
  obtain ⟨p, hp, hpU₀, _, hpODE⟩ := positiveBuffer_finite_smooth_extension hab hV
    hU₀.continuousOn hD₀.continuousOn hU₀d hD₀d'
  have hpU : EqOn p U (Icc a b) := hpU₀.trans heqcc
  have hpUo := hpU.mono Ioo_subset_Icc_self
  refine ⟨p, hp, hpU, ?_, positiveBuffer_classical_derivative_ae u isOpen_Ioo hderiv hpUo, hpODE⟩
  filter_upwards [ae_restrict_of_ae hue, ae_restrict_mem measurableSet_Ioo] with x hx hxs
  exact hx.trans (hpUo hxs).symm

/-- The canonical continuous energy representative is smooth at every
interior point of a stationary region and satisfies the classical equation
there. -/
theorem positiveBuffer_stationary_smooth_on_open {V U : ℝ → ℝ}
    (hV : ContDiff ℝ ∞ V) (s : Set ℝ) (hs : MeasurableSet s)
    (u : PositiveBufferEnergy V)
    (hu : ∀ v : PositiveBufferEnergy V, v ∈ positiveBufferSupportedEnergyGraph V s hs →
      positiveBufferEnergyForm V hV.continuous u v = 0)
    (hU : Continuous U)
    (hue : (positiveBufferEnergyCoordinate V 0 u : ℝ → ℝ) =ᵐ[volume] U)
    {O : Set ℝ} (hO : IsOpen O) (hOs : O ⊆ s) :
    ContDiffOn ℝ ∞ U O ∧ ∀ x ∈ O, -deriv (deriv U) x + V x * U x = 0 := by
  have hpoint (x : ℝ) (hx : x ∈ O) :
      ContDiffAt ℝ ∞ U x ∧ -deriv (deriv U) x + V x * U x = 0 := by
    obtain ⟨a, b, hxab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hO.mem_nhds hx)
    obtain ⟨p, hp, hup, hpsm, hpODE⟩ :=
      positiveBuffer_local_smooth_representative (hxab.1.trans hxab.2) hV contDiff_const
        (positiveBufferEnergy_derivative_weak V u)
        (positiveBuffer_stationary_localWeakEquation hV.continuous s hs u hu (hsub.trans hOs))
    have heq : EqOn U p (Ioo a b) := MeasureTheory.Measure.eqOn_open_of_ae_eq
      ((ae_restrict_of_ae hue).symm.trans hup) isOpen_Ioo hU.continuousOn hp.continuousOn
    have hev : U =ᶠ[𝓝 x] p := by
      filter_upwards [Ioo_mem_nhds hxab.1 hxab.2] with y hy
      exact heq hy
    refine ⟨(hpsm.contDiffAt (Ioo_mem_nhds hxab.1 hxab.2)).congr_of_eventuallyEq hev, ?_⟩
    rw [hev.deriv.deriv_eq, heq hxab]
    exact hpODE x hxab
  exact ⟨fun x hx => (hpoint x hx).1.contDiffWithinAt, fun x hx => (hpoint x hx).2⟩

/-- Glue a smooth continuation across the unique finite boundary point of
an open region. This is the same construction for either exterior half-line. -/
theorem positiveBuffer_glue_boundary_smooth {U p₀ : ℝ → ℝ} {O : Set ℝ} {c : ℝ}
    (hO : IsOpen O) (hS : IsClosed (insert c O)) (hU : ContDiffOn ℝ ∞ U O)
    (hp₀ : ContDiff ℝ ∞ p₀)
    (hnear : ∀ᶠ x in 𝓝 c, x ∈ insert c O → U x = p₀ x) :
    ∃ p : ℝ → ℝ, ContDiff ℝ ∞ p ∧
      EqOn p U (insert c O) ∧ EqOn (deriv p) (deriv U) O ∧
      EqOn (deriv (deriv p)) (deriv (deriv U)) O := by
  classical
  let p := (insert c O).piecewise U p₀
  have hpU : EqOn p U (insert c O) := by
    intro x hx
    exact piecewise_eq_of_mem (insert c O) U p₀ hx
  have hpUO : EqOn p U O := hpU.mono (subset_insert c O)
  have hpc : p =ᶠ[𝓝 c] p₀ := by
    filter_upwards [hnear] with x hx
    by_cases hxs : x ∈ insert c O
    · exact (hpU hxs).trans (hx hxs)
    · exact piecewise_eq_of_notMem (insert c O) U p₀ hxs
  have hcsm := hp₀.contDiffAt.congr_of_eventuallyEq hpc
  have hsm : ContDiff ℝ ∞ p := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hxs : x ∈ insert c O
    · rcases hxs with rfl | hx
      · exact hcsm
      · have heq : p =ᶠ[𝓝 x] U := by
          filter_upwards [hO.mem_nhds hx] with y hy
          exact hpUO hy
        exact (hU.contDiffAt (hO.mem_nhds hx)).congr_of_eventuallyEq heq
    · have heq : p =ᶠ[𝓝 x] p₀ := by
        filter_upwards [hS.isOpen_compl.mem_nhds hxs] with y hy
        exact piecewise_eq_of_notMem (insert c O) U p₀ hy
      exact hp₀.contDiffAt.congr_of_eventuallyEq heq
  exact ⟨p, hsm, hpU, hpUO.deriv hO, (hpUO.deriv hO).deriv hO⟩

end ContinuousFlexibility.Radial
