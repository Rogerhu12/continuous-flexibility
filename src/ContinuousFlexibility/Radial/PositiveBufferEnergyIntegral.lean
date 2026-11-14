module

public import ContinuousFlexibility.Radial.PositiveBufferEnergyMinimizer

/-!
# The physical energy of actual variational profiles

The graph norm controls an integrable physical energy density.  A stationary
profile agrees with its compact lift off the varied region, so positivity of
the potential on that region and on the support of the lift makes its total
physical energy nonnegative.  Consequently its energy on each subregion is
bounded by the energy of the lift.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

def positiveBufferEnergyDensity (V : ℝ → ℝ) (u : PositiveBufferEnergy V) (x : ℝ) : ℝ :=
  positiveBufferEnergyCoordinate V 1 u x ^ 2 +
    V x * positiveBufferEnergyCoordinate V 0 u x ^ 2

theorem positiveBufferEnergyDensity_integrable (V : ℝ → ℝ) (hV : Continuous V)
    (u : PositiveBufferEnergy V) : Integrable (positiveBufferEnergyDensity V u) volume := by
  have hpot : Integrable
      (fun x => V x * positiveBufferEnergyCoordinate V 0 u x ^ 2) volume := by
    simpa only [pow_two, mul_assoc] using positiveBufferPotential_pairing_integrable V hV u u
  exact (Lp.memLp (positiveBufferEnergyCoordinate V 1 u)).integrable_sq.add hpot

theorem positiveBufferEnergyForm_self_eq_integral (V : ℝ → ℝ) (hV : Continuous V)
    (u : PositiveBufferEnergy V) :
    positiveBufferEnergyForm V hV u u = ∫ x : ℝ, positiveBufferEnergyDensity V u x := by
  rw [positiveBufferEnergyForm_eq_integral, positiveBufferL2_inner_integral]
  have hpot := positiveBufferPotential_pairing_integrable V hV u u
  have hd : Integrable (fun x : ℝ =>
      positiveBufferEnergyCoordinate V 1 u x * positiveBufferEnergyCoordinate V 1 u x)
      volume := by
    apply ((Lp.memLp (positiveBufferEnergyCoordinate V 1 u)).integrable_mul
      (Lp.memLp (positiveBufferEnergyCoordinate V 1 u))).congr
    filter_upwards [] with x
    rfl
  rw [← integral_add hd hpot]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [positiveBufferEnergyDensity, pow_two, mul_assoc]

theorem positiveBufferCompactEnergyLift_self_eq_integral (V : ℝ → ℝ) (hV : Continuous V)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    positiveBufferEnergyForm V hV (positiveBufferCompactEnergyLift V hV φ hφ hcφ)
      (positiveBufferCompactEnergyLift V hV φ hφ hcφ) =
      ∫ x : ℝ, deriv φ x ^ 2 + V x * φ x ^ 2 := by
  rw [positiveBufferEnergyForm_self_eq_integral]
  apply integral_congr_ae
  filter_upwards [positiveBufferCompactEnergyLift_base_ae V hV φ hφ hcφ,
    positiveBufferCompactEnergyLift_derivative_ae V hV φ hφ hcφ] with x hu hd
  simp only [positiveBufferEnergyDensity, hu, hd]

theorem positiveBufferEnergyDensity_nonneg_of_trace {V U φ : ℝ → ℝ}
    (u : PositiveBufferEnergy V) (s : Set ℝ)
    (hu : (positiveBufferEnergyCoordinate V 0 u : ℝ → ℝ) =ᵐ[volume] U)
    (htrace : EqOn U φ (closure sᶜ))
    (hV : ∀ x ∈ s ∪ Function.support φ, 0 ≤ V x) :
    0 ≤ᵐ[volume] positiveBufferEnergyDensity V u := by
  filter_upwards [hu] with x hx
  dsimp only [positiveBufferEnergyDensity]
  rw [hx]
  by_cases hxs : x ∈ s ∪ Function.support φ
  · exact add_nonneg (sq_nonneg _) (mul_nonneg (hV x hxs) (sq_nonneg _))
  · have hs : x ∈ sᶜ := fun h => hxs (Or.inl h)
    have hφ : φ x = 0 := Function.notMem_support.mp (fun h => hxs (Or.inr h))
    rw [htrace (subset_closure hs), hφ]
    simpa using sq_nonneg (positiveBufferEnergyCoordinate V 1 u x)

/-- Any region has energy at most the total physical energy when the latter
density is nonnegative. -/
theorem positiveBufferEnergyDensity_setIntegral_le {V : ℝ → ℝ} (hV : Continuous V)
    (u : PositiveBufferEnergy V) (s : Set ℝ)
    (hpos : 0 ≤ᵐ[volume] positiveBufferEnergyDensity V u) :
    (∫ x in s, positiveBufferEnergyDensity V u x) ≤ positiveBufferEnergyForm V hV u u := by
  rw [positiveBufferEnergyForm_self_eq_integral]
  exact setIntegral_le_integral (positiveBufferEnergyDensity_integrable V hV u) hpos

/-- An ordinary derivative on an open region agrees with the true weak
derivative there. The conclusion concerns actual `L²` representatives only
almost everywhere, as required. -/
theorem positiveBuffer_classical_derivative_ae {V U p : ℝ → ℝ}
    (u : PositiveBufferEnergy V) {O : Set ℝ} (hO : IsOpen O)
    (hderiv : ∀ᵐ x : ℝ, HasDerivAt U (positiveBufferEnergyCoordinate V 1 u x) x)
    (hpU : EqOn p U O) :
    (positiveBufferEnergyCoordinate V 1 u : ℝ → ℝ) =ᵐ[volume.restrict O] deriv p := by
  filter_upwards [ae_restrict_of_ae hderiv, ae_restrict_mem hO.measurableSet] with x hd hx
  have heq : p =ᶠ[𝓝 x] U := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact hpU hy
  exact (hd.congr_of_eventuallyEq heq).deriv.symm

theorem positiveBuffer_classical_energy_ae {V p : ℝ → ℝ}
    (u : PositiveBufferEnergy V) (s : Set ℝ)
    (hp : (positiveBufferEnergyCoordinate V 0 u : ℝ → ℝ) =ᵐ[volume.restrict s] p)
    (hd : (positiveBufferEnergyCoordinate V 1 u : ℝ → ℝ) =ᵐ[volume.restrict s] deriv p) :
    positiveBufferEnergyDensity V u =ᵐ[volume.restrict s]
      (fun x => deriv p x ^ 2 + V x * p x ^ 2) := by
  filter_upwards [hp, hd] with x hx hd
  simp only [positiveBufferEnergyDensity, hx, hd]

theorem positiveBuffer_classical_energy_integrableOn {V p : ℝ → ℝ}
    (hV : Continuous V) (u : PositiveBufferEnergy V) (s : Set ℝ)
    (hp : (positiveBufferEnergyCoordinate V 0 u : ℝ → ℝ) =ᵐ[volume.restrict s] p)
    (hd : (positiveBufferEnergyCoordinate V 1 u : ℝ → ℝ) =ᵐ[volume.restrict s] deriv p) :
    IntegrableOn (fun x => deriv p x ^ 2 + V x * p x ^ 2) s volume :=
  (positiveBufferEnergyDensity_integrable V hV u).integrableOn.congr
    (positiveBuffer_classical_energy_ae u s hp hd)

theorem positiveBuffer_classical_energy_le {V p : ℝ → ℝ}
    (hV : Continuous V) (u : PositiveBufferEnergy V) (s : Set ℝ)
    (hpos : 0 ≤ᵐ[volume] positiveBufferEnergyDensity V u)
    (hp : (positiveBufferEnergyCoordinate V 0 u : ℝ → ℝ) =ᵐ[volume.restrict s] p)
    (hd : (positiveBufferEnergyCoordinate V 1 u : ℝ → ℝ) =ᵐ[volume.restrict s] deriv p) :
    (∫ x in s, deriv p x ^ 2 + V x * p x ^ 2) ≤ positiveBufferEnergyForm V hV u u := by
  rw [← integral_congr_ae (positiveBuffer_classical_energy_ae u s hp hd)]
  exact positiveBufferEnergyDensity_setIntegral_le hV u s hpos

end ContinuousFlexibility.Radial
