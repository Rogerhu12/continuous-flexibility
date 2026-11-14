module

public import ContinuousFlexibility.Analysis.N01cComponentCosineSpeed
public import ContinuousFlexibility.Scalar.GreenIdentity

/-! Angular periodicity of the actual state fields and compact speed. -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S}

theorem stateU_periodic (hS : IsPhysicalSpaces D T S) (x : AnnularState S) :
    Function.Periodic (stateU S x) (0, Real.pi) := by
  have hp := ((hS.1 (3 / 4 : ℝ)).2.2.2.1 x.1.1).2.2.1
  intro p
  simp only [stateU, heightPairField, Prod.fst_add, add_zero, hp p]

theorem stateHeight_periodic (hS : IsPhysicalSpaces D T S)
    (z : AnnularState S × ℝ) :
    Function.Periodic (stateHeight D S C z) (0, Real.pi) := by
  intro p
  simp only [stateHeight, Prod.fst_add, add_zero, stateU_periodic hS z.1 p]

theorem originalCoefficients_periodic (hS : IsPhysicalSpaces D T S)
    (z : AnnularState S × ℝ) :
    Function.Periodic (originalCoefficients D S C z).a (0, Real.pi) ∧
      Function.Periodic (originalCoefficients D S C z).b (0, Real.pi) ∧
      Function.Periodic (originalCoefficients D S C z).c (0, Real.pi) :=
  periodic_heightCorrectedCoefficients (stateProfile D S C z.1)
    (stateHeight_periodic (C := C) hS z)

theorem minusCharacteristicSpeed_periodic (hS : IsPhysicalSpaces D T S)
    (z : AnnularState S × ℝ) :
    Function.Periodic (minusCharacteristicSpeed (originalCoefficients D S C z))
      (0, Real.pi) := by
  have hc := originalCoefficients_periodic (C := C) hS z
  intro p
  simp only [minusCharacteristicSpeed, hc.1 p, hc.2.1 p, hc.2.2 p]

theorem normalizedSpeedFactor_periodic (hS : IsPhysicalSpaces D T S)
    (z : AnnularState S × ℝ) (i : Fin 2) :
    Function.Periodic (normalizedSpeedFactor D S C i z) (0, Real.pi) := by
  have hz := stateHeight_periodic (C := C) hS z
  have hE : Function.Periodic (profileEnergy (stateProfile D S C z.1)) (0, Real.pi) := by
    intro p
    simp only [profileEnergy, Prod.fst_add, add_zero]
  have hk : Function.Periodic (heightRadial (stateHeight D S C z)) (0, Real.pi) :=
    periodic_radialPartial hz
  have hp : Function.Periodic (heightAngular (stateHeight D S C z)) (0, Real.pi) := by
    intro p
    simp only [heightAngular, periodic_angularPartial hz p, Prod.fst_add, add_zero]
  have hpr := periodic_radialPartial hp
  have hpt := periodic_angularPartial hp
  intro p
  simp only [normalizedSpeedFactor, polarDiscriminant, Prod.fst_add, add_zero,
    hE p, hk p, hp p, hpr p, hpt p]

/-- The supplied cosine speed is periodic for every real time and every
actual state; no neighbourhood or positivity assumption is required. -/
theorem componentCosineSpeed_periodic (hS : IsPhysicalSpaces D T S)
    (z : AnnularState S × ℝ) (m : ℕ) :
    ∀ t, Function.Periodic
      (fun θ => componentCosineSpeed D S C m (z, (t, θ))) Real.pi := by
  intro t θ
  have ha :
      normalizedSpeedFactor D S C 0 z
        (rootCosinePath (C.left m) (C.right m) t, θ + Real.pi) =
      normalizedSpeedFactor D S C 0 z
        (rootCosinePath (C.left m) (C.right m) t, θ) := by
    simpa only [Prod.mk_add_mk, add_zero] using
      normalizedSpeedFactor_periodic (C := C) hS z 0
        (rootCosinePath (C.left m) (C.right m) t, θ)
  have hb :
      normalizedSpeedFactor D S C 1 z
        (rootCosinePath (C.left m) (C.right m) t, θ + Real.pi) =
      normalizedSpeedFactor D S C 1 z
        (rootCosinePath (C.left m) (C.right m) t, θ) := by
    simpa only [Prod.mk_add_mk, add_zero] using
      normalizedSpeedFactor_periodic (C := C) hS z 1
        (rootCosinePath (C.left m) (C.right m) t, θ)
  simp only [componentCosineSpeed, cosineRegularizedSpeed, ha, hb]

end ContinuousFlexibility.Statements
