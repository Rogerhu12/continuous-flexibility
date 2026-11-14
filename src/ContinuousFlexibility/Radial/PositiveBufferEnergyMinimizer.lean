module

public import ContinuousFlexibility.Radial.PositiveBufferEnergyLift
public import ContinuousFlexibility.Radial.BufferTraceBound

/-!
# Actual variational buffer profiles and their boundary values

The minimizer is an element of the genuine weighted weak energy graph. Its
continuous representative has the same boundary values as a chosen smooth
lift, because their difference vanishes on the exterior. No boundary value
is assigned to an arbitrary representative of an `L²` class.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

theorem positiveBuffer_supported_trace_eq {V : ℝ → ℝ}
    (s : Set ℝ) (hs : IsClosed s) {u v : PositiveBufferEnergy V}
    (huv : u - v ∈ positiveBufferSupportedEnergyGraph V s hs.measurableSet)
    {U W : ℝ → ℝ} (hU : Continuous U) (hW : Continuous W)
    (hu : (positiveBufferEnergyCoordinate V 0 u : ℝ → ℝ) =ᵐ[volume] U)
    (hv : (positiveBufferEnergyCoordinate V 0 v : ℝ → ℝ) =ᵐ[volume] W) :
    EqOn U W (closure sᶜ) := by
  have hw : (positiveBufferEnergyCoordinate V 0 (u - v) : ℝ → ℝ) =ᵐ[volume]
      (fun x => U x - W x) := by
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (positiveBufferEnergyCoordinate V 0 u)
      (positiveBufferEnergyCoordinate V 0 v), hu, hv] with x hsub hx hy
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hx, hy]
  have hzero := buffer_continuousRepresentative_zero_on_closure (hU.sub hW) hw
    hs.isOpen_compl ((mem_positiveBufferSupportedEnergyGraph_iff V s hs.measurableSet _).mp huv)
  intro x hx
  exact sub_eq_zero.mp (hzero hx)

/-- The stationary supported variation has the smallest physical energy
among all competitors agreeing with its lift on the exterior. -/
theorem positiveBuffer_supported_stationary_minimum {V : ℝ → ℝ}
    (hV : Continuous V) {m : ℝ} (hm : 0 < m)
    (s : Set ℝ) (hs : MeasurableSet s) (hVm : ∀ x ∈ s, m ^ 2 ≤ V x)
    {u v : PositiveBufferEnergy V}
    (hu : ∀ w : PositiveBufferEnergy V, w ∈ positiveBufferSupportedEnergyGraph V s hs →
      positiveBufferEnergyForm V hV u w = 0)
    (hv : v - u ∈ positiveBufferSupportedEnergyGraph V s hs) :
    positiveBufferEnergyForm V hV u u ≤ positiveBufferEnergyForm V hV v v := by
  have he := positiveBuffer_stationary_energy_identity (positiveBufferEnergyForm V hV)
    (positiveBufferEnergyForm_symm V hV) (positiveBufferSupportedEnergyGraph V s hs) hu hv
  have hc := positiveBufferEnergyForm_supported_coercive_bound hV hm s hs hVm (v - u) hv
  have hn : 0 ≤ (m ^ 2 / (m ^ 2 + 2)) * ‖v - u‖ ^ 2 := by positivity
  linarith

/-- The concrete variational construction produces a bounded continuous
profile with true trace values, an actual weak derivative and the local weak
equation. This single theorem applies to a closed finite interval and to a
closed half-line. -/
theorem positiveBuffer_exists_variational_profile {V : ℝ → ℝ}
    (hreal : ActualClosedFormRealization V) (hV : Continuous V) {m : ℝ} (hm : 0 < m)
    (s : Set ℝ) (hs : IsClosed s) (hVm : ∀ x ∈ s, m ^ 2 ≤ V x)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    ∃ u : PositiveBufferEnergy V, ∃ U : ℝ → ℝ,
      Continuous U ∧ (positiveBufferEnergyCoordinate V 0 u : ℝ → ℝ) =ᵐ[volume] U ∧
      (∀ a b : ℝ, U b - U a = ∫ x in a..b, positiveBufferEnergyCoordinate V 1 u x) ∧
      (∀ᵐ x : ℝ, HasDerivAt U (positiveBufferEnergyCoordinate V 1 u x) x) ∧
      (∀ x : ℝ, |U x| ≤ ‖positiveBufferEnergyCoordinate V 0 u‖ +
        ‖positiveBufferEnergyCoordinate V 1 u‖) ∧
      EqOn U φ (closure sᶜ) ∧
      u - positiveBufferCompactEnergyLift V hV φ hφ hcφ ∈
        positiveBufferSupportedEnergyGraph V s hs.measurableSet ∧
      (∀ v : PositiveBufferEnergy V, v ∈ positiveBufferSupportedEnergyGraph V s hs.measurableSet →
        positiveBufferEnergyForm V hV u v = 0) ∧
      positiveBufferEnergyForm V hV u u ≤
        positiveBufferEnergyForm V hV (positiveBufferCompactEnergyLift V hV φ hφ hcφ)
          (positiveBufferCompactEnergyLift V hV φ hφ hcφ) ∧
      (∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → Function.support ψ ⊆ s →
        (∫ x : ℝ, positiveBufferEnergyCoordinate V 0 u x * deriv (deriv ψ) x) =
          ∫ x : ℝ, V x * positiveBufferEnergyCoordinate V 0 u x * ψ x) := by
  let lift := positiveBufferCompactEnergyLift V hV φ hφ hcφ
  obtain ⟨u, hu, _⟩ := positiveBuffer_exists_unique_supported_stationary hreal hV hm s
    hs.measurableSet hVm lift
  obtain ⟨U, hU, hue, hprim, hderiv⟩ :=
    buffer_weakDerivative_continuousRepresentative (positiveBufferEnergy_derivative_weak V u)
  have htrace : EqOn U φ (closure sᶜ) :=
    positiveBuffer_supported_trace_eq s hs hu.1 hU hφ.continuous hue
      (positiveBufferCompactEnergyLift_base_ae V hV φ hφ hcφ)
  have hneg : lift - u ∈ positiveBufferSupportedEnergyGraph V s hs.measurableSet := by
    simpa only [neg_sub] using (positiveBufferSupportedEnergyGraph V s hs.measurableSet).neg_mem hu.1
  refine ⟨u, U, hU, hue, hprim, hderiv, ?_, htrace, hu.1, hu.2, ?_, ?_⟩
  · intro x
    exact bufferRepresentative_abs_le hU _ _ hue hprim x
  · exact positiveBuffer_supported_stationary_minimum hV hm s hs.measurableSet hVm hu.2 hneg
  · intro ψ hψ hcψ hsψ
    exact positiveBuffer_stationary_weak_equation V hV s hs.measurableSet u hu.2 ψ hψ hcψ hsψ

end ContinuousFlexibility.Radial
