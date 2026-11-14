module

public import ContinuousFlexibility.Radial.PositiveBufferWeakRegularity
public import ContinuousFlexibility.Radial.PositiveBufferTraceMap

/-!
# Smooth representatives of full-model corrections

The full inverse applied to a smooth commutator source has a canonical
continuous energy representative. Local weak regularity identifies that
same representative with smooth classical solutions on every finite
interval, giving a globally smooth correction with the actual equation.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem positiveBuffer_localWeakEquation_of_full {V f : ℝ → ℝ}
    {u F : RadialL2} (hu : WeakSchrodingerGraph V u F)
    (hF : (F : ℝ → ℝ) =ᵐ[volume] f) (a b : ℝ) :
    PositiveBufferLocalWeakEquation V u f a b := by
  intro φ hφ hcφ _
  calc
    (∫ x : ℝ, f x * φ x) = ∫ x : ℝ, F x * φ x := by
      apply integral_congr_ae
      filter_upwards [hF] with x hx
      rw [hx]
    _ = _ := hu φ hφ hcφ

/-- Local weak regularity belongs to the unique continuous energy
representative, independent of the primitive used to prove regularity. -/
theorem positiveBufferEnergyRepresentative_local_smooth {V f : ℝ → ℝ}
    {a b : ℝ} (hab : a < b) (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f)
    (u : PositiveBufferEnergy V)
    (hu : PositiveBufferLocalWeakEquation V (positiveBufferEnergyCoordinate V 0 u) f a b) :
    ContDiffOn ℝ ∞ (positiveBufferEnergyRepresentative V u) (Ioo a b) ∧
      ∀ x ∈ Ioo a b, -deriv (deriv (positiveBufferEnergyRepresentative V u)) x +
        V x * positiveBufferEnergyRepresentative V u x = f x := by
  obtain ⟨U, hU, hue, hUs, hUeq⟩ := positiveBuffer_local_smooth_representative hab hV hf
    (positiveBufferEnergy_derivative_weak V u) hu
  have hcan := positiveBufferEnergyRepresentative_spec V u
  have hcae : (positiveBufferEnergyCoordinate V 0 u : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)]
      positiveBufferEnergyRepresentative V u := ae_restrict_of_ae hcan.2.1
  have heq : EqOn (positiveBufferEnergyRepresentative V u) U (Ioo a b) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq (μ := volume) (hcae.symm.trans hue)
      isOpen_Ioo hcan.1.continuousOn hU.continuousOn
  refine ⟨hUs.congr heq, ?_⟩
  intro x hx
  have he : positiveBufferEnergyRepresentative V u =ᶠ[𝓝 x] U := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact heq hy
  rw [he.deriv.deriv_eq, he.eq_of_nhds]
  exact hUeq x hx

/-- Every smooth full source has the actual globally smooth classical
energy representative. No pointwise properties are assigned to the `L²`
class itself. -/
theorem positiveBufferEnergyRepresentative_global_smooth {V f : ℝ → ℝ}
    (hV : ContDiff ℝ ∞ V) (hf : ContDiff ℝ ∞ f) (u : PositiveBufferEnergy V)
    {F : RadialL2} (hu : WeakSchrodingerGraph V (positiveBufferEnergyCoordinate V 0 u) F)
    (hF : (F : ℝ → ℝ) =ᵐ[volume] f) :
    ContDiff ℝ ∞ (positiveBufferEnergyRepresentative V u) ∧
      ∀ x : ℝ, -deriv (deriv (positiveBufferEnergyRepresentative V u)) x +
        V x * positiveBufferEnergyRepresentative V u x = f x := by
  have hloc (x : ℝ) := positiveBufferEnergyRepresentative_local_smooth
    (show x - 1 < x + 1 by linarith) hV hf u
    (positiveBuffer_localWeakEquation_of_full hu hF (x - 1) (x + 1))
  have hx (x : ℝ) : x ∈ Ioo (x - 1) (x + 1) := ⟨by linarith, by linarith⟩
  refine ⟨contDiff_iff_contDiffAt.mpr (fun x => ?_), fun x => (hloc x).2 x (hx x)⟩
  exact (hloc x).1.contDiffAt (isOpen_Ioo.mem_nhds (hx x))

end ContinuousFlexibility.Radial
