import ContinuousFlexibility.Radial.PositiveBufferEnergySpace
import ContinuousFlexibility.Radial.BufferTraceBound

/-!
# Actual continuous trace maps on the weighted energy domain

Point evaluation is defined using the unique continuous representative of
the actual weak energy field. The representative respects linear
operations, and its values are bounded linear functionals on the energy
space. This is the trace used in Green-column subtraction.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

def positiveBufferEnergyRepresentative (V : ℝ → ℝ) (u : PositiveBufferEnergy V) : ℝ → ℝ :=
  Classical.choose (buffer_weakDerivative_continuousRepresentative
    (positiveBufferEnergy_derivative_weak V u))

theorem positiveBufferEnergyRepresentative_spec (V : ℝ → ℝ) (u : PositiveBufferEnergy V) :
    Continuous (positiveBufferEnergyRepresentative V u) ∧
      (positiveBufferEnergyCoordinate V 0 u : ℝ → ℝ) =ᵐ[volume]
        positiveBufferEnergyRepresentative V u ∧
      (∀ a b : ℝ, positiveBufferEnergyRepresentative V u b -
        positiveBufferEnergyRepresentative V u a =
          ∫ x in a..b, positiveBufferEnergyCoordinate V 1 u x) ∧
      (∀ᵐ x : ℝ, HasDerivAt (positiveBufferEnergyRepresentative V u)
        (positiveBufferEnergyCoordinate V 1 u x) x) :=
  Classical.choose_spec (buffer_weakDerivative_continuousRepresentative
    (positiveBufferEnergy_derivative_weak V u))

theorem positiveBufferEnergyRepresentative_eq (V : ℝ → ℝ) (u : PositiveBufferEnergy V)
    {U : ℝ → ℝ} (hU : Continuous U)
    (hu : (positiveBufferEnergyCoordinate V 0 u : ℝ → ℝ) =ᵐ[volume] U) :
    positiveBufferEnergyRepresentative V u = U := by
  have h := positiveBufferEnergyRepresentative_spec V u
  exact buffer_continuousRepresentative_unique h.1 hU h.2.1 hu

theorem positiveBufferEnergyRepresentative_add (V : ℝ → ℝ) (u v : PositiveBufferEnergy V) :
    positiveBufferEnergyRepresentative V (u + v) =
      fun x => positiveBufferEnergyRepresentative V u x + positiveBufferEnergyRepresentative V v x := by
  have hu := positiveBufferEnergyRepresentative_spec V u
  have hv := positiveBufferEnergyRepresentative_spec V v
  apply positiveBufferEnergyRepresentative_eq V (u + v) (hu.1.add hv.1)
  rw [map_add]
  filter_upwards [Lp.coeFn_add (positiveBufferEnergyCoordinate V 0 u)
    (positiveBufferEnergyCoordinate V 0 v), hu.2.1, hv.2.1] with x hx hux hvx
  rw [hx]
  simp only [Pi.add_apply, hux, hvx]

theorem positiveBufferEnergyRepresentative_smul (V : ℝ → ℝ) (c : ℝ)
    (u : PositiveBufferEnergy V) :
    positiveBufferEnergyRepresentative V (c • u) =
      fun x => c * positiveBufferEnergyRepresentative V u x := by
  have hu := positiveBufferEnergyRepresentative_spec V u
  apply positiveBufferEnergyRepresentative_eq V (c • u) (hu.1.const_mul c)
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul c (positiveBufferEnergyCoordinate V 0 u), hu.2.1]
    with x hx hux
  rw [hx]
  simp only [Pi.smul_apply, smul_eq_mul, hux]

theorem positiveBufferEnergyRepresentative_bound (V : ℝ → ℝ)
    (u : PositiveBufferEnergy V) (c : ℝ) :
    |positiveBufferEnergyRepresentative V u c| ≤ 2 * ‖u‖ := by
  have h := positiveBufferEnergyRepresentative_spec V u
  have he := bufferRepresentative_abs_le h.1 _ _ h.2.1 h.2.2.1 c
  have h0 := positiveBufferEnergyCoordinate_norm_le V 0 u
  have h1 := positiveBufferEnergyCoordinate_norm_le V 1 u
  linarith

/-- Evaluation at a real cut, defined on the actual closed energy domain. -/
def positiveBufferTraceAt (V : ℝ → ℝ) (c : ℝ) : PositiveBufferEnergy V →L[ℝ] ℝ := by
  let L : PositiveBufferEnergy V →ₗ[ℝ] ℝ :=
    { toFun := fun u => positiveBufferEnergyRepresentative V u c
      map_add' := by
        intro u v
        exact congrFun (positiveBufferEnergyRepresentative_add V u v) c
      map_smul' := by
        intro a u
        simpa only [smul_eq_mul, RingHom.id_apply] using
          congrFun (positiveBufferEnergyRepresentative_smul V a u) c }
  exact L.mkContinuous 2 (fun u => by
    change ‖positiveBufferEnergyRepresentative V u c‖ ≤ 2 * ‖u‖
    simpa only [Real.norm_eq_abs] using positiveBufferEnergyRepresentative_bound V u c)

@[simp] theorem positiveBufferTraceAt_apply (V : ℝ → ℝ) (c : ℝ)
    (u : PositiveBufferEnergy V) :
    positiveBufferTraceAt V c u = positiveBufferEnergyRepresentative V u c := rfl

/-- Any classical continuous representative gives the same actual trace. -/
theorem positiveBufferTraceAt_eq (V : ℝ → ℝ) (c : ℝ) (u : PositiveBufferEnergy V)
    {U : ℝ → ℝ} (hU : Continuous U)
    (hu : (positiveBufferEnergyCoordinate V 0 u : ℝ → ℝ) =ᵐ[volume] U) :
    positiveBufferTraceAt V c u = U c := by
  rw [positiveBufferTraceAt_apply, positiveBufferEnergyRepresentative_eq V u hU hu]

end ContinuousFlexibility.Radial
