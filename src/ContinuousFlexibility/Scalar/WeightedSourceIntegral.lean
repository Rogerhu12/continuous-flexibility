import ContinuousFlexibility.Scalar.WeightedStateFlatness
import ContinuousFlexibility.Scalar.NormalizedConservation

/-!
# Compatibility of the actual weighted scalar residual

The conservation theorem for the genuine connection is used with angular
period `π`, exactly the period and normalization of `physicalSourceIntegral`.
It applies to the removable value at `q = 0` as well as nonzero parameters.
The compatibility of any decoded residual then follows from the defining
physical integral of `S.Q`.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

/-- The actual residual has zero physical source integral at every geometric
state, including the removable parameter value zero. -/
theorem ScalarStateGeometry.physicalSourceIntegral_eq_zero
    (hD : IsAccumulatingProfile D) (hS : IsPhysicalSpaces D T S)
    {x : ScalarWeightedState S} (hg : ScalarStateGeometry D S x) :
    physicalSourceIntegral D (scalarStateResidual D S x) = 0 := by
  have hadm := ScalarStateGeometry.admissibleScalarData hD hS hg
  rcases hadm with ⟨ha, hab, hw, hh, hu, hhw, _, hwa, hwb, hjets, hpos⟩
  have hr : ∀ r ∈ uIcc D.a D.b, r ≠ 0 := by
    intro r hrr
    rw [uIcc_of_le hab.le] at hrr
    exact (lt_of_lt_of_le ha hrr.1).ne'
  exact integral_mean_normalizedHeightResidual_radialHeight_eq_zero
    (T := Real.pi) hh hhw (fun _ _ => hw.contDiffAt) hu hr
    (fun p hp => hpos p.1 (by simpa only [uIcc_of_le hab.le] using hp.1) p.2)
    (scalarStateIncrement_periodic hS x) hwa hwb
    (fun θ _ => (hjets θ).1) (fun θ _ => (hjets θ).2.1)
    (fun θ _ => (hjets θ).2.2.1) (fun θ _ => (hjets θ).2.2.2)

/-- A decoded realization of the actual residual belongs to the physical
compatible-source kernel; compatibility is not an assumption on that output. -/
theorem ScalarStateGeometry.compatible_of_decode_residual
    (hD : IsAccumulatingProfile D) (hS : IsPhysicalSpaces D T S)
    {x : ScalarWeightedState S} (hg : ScalarStateGeometry D S x)
    (f : ScalarHeightSpace S)
    (hf : (S.height scalarBeta).decode f = scalarStateResidual D S x) : S.Q f = 0 := by
  have hQ : S.Q f = physicalSourceIntegral D ((S.height scalarBeta).decode f) := by
    rcases hS with ⟨_, _, _, _, _, _, _, hQ, _⟩
    exact hQ f
  rw [hQ, hf]
  exact ScalarStateGeometry.physicalSourceIntegral_eq_zero hD hS hg

end ContinuousFlexibility.Statements
