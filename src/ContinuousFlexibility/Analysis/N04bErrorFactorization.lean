import ContinuousFlexibility.Statements.Nonlinear

/-!
# The exact vanishing forced by the return-error factorization

The correction error is linear in its residual input. At zero residual,
N03 therefore identifies the actual physical operators on every height
test. More generally, continuity of a parameter-dependent linear error
preserves a residual that is smaller than the parameter to first order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open ContinuousFlexibility.Statements
open scoped Topology

/-- N03's error factorization forbids an additional operator correction
on a state with zero return residual. -/
theorem n04b_returnCorrection_operator_eq_of_residual_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base : ℕ} {ε : ℝ}
    (hN : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (hres : R.residual z = 0)
    (η : HeightPair S) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    divergenceOperator (L.coefficients z) (heightPairField S η) p =
      divergenceOperator (originalCoefficients D S C z) (heightPairField S η) p := by
  have he :
      divergenceOperator (originalCoefficients D S C z) (heightPairField S η) p -
        divergenceOperator (L.coefficients z) (heightPairField S η) p = 0 := by
    simpa [hres] using hN.2.2.2.2.2.1 z hz hs η p hp
  exact (sub_eq_zero.mp he).symm

/-- A genuine first-order small residual remains first-order small under
a jointly continuous linear error. The codomain can itself be a space of
jets on a compact set, so the statement also applies to uniform control. -/
theorem n04b_factorized_error_div_tendsto_zero
    {Z E F : Type*} [TopologicalSpace Z]
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    (A : Z → E →ₗ[ℝ] F) {z₀ : Z} {z : ℝ → Z} {e : ℝ → E}
    (hA : ContinuousAt (fun p : Z × E => A p.1 p.2) (z₀, 0))
    (hz : Tendsto z (𝓝[≠] (0 : ℝ)) (𝓝 z₀))
    (he : Tendsto (fun q : ℝ => q⁻¹ • e q) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : E))) :
    Tendsto (fun q : ℝ => q⁻¹ • A (z q) (e q))
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : F)) := by
  have h := hA.tendsto.comp (hz.prodMk_nhds he)
  simpa only [Function.comp_def, map_smul, map_zero] using h

end ContinuousFlexibility.Analysis
