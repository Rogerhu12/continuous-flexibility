module

public import ContinuousFlexibility.Statements.Scalar

/-!
# Connection, residual and local development of the height equation

The pointwise calculus is assembled from the actual derivative identities in
`HeightDerivatives`, `HeightCoframe` and `Linearization`.  The development is
constructed on the given convex open coordinate domain, and its metric identity
is polarized to obtain the full bilinear statement.  No primitive on an annulus
or global injectivity is asserted.

Source: `paper/flexible-surface-readable/03-height-equation.tex`, lines 23–189.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open scoped ContDiff

/-- All clauses of the scalar core hold for the actual smooth height. -/
theorem scalarCoreAt_of_smooth
    {w : ℝ → ℝ} {z : PolarPoint → ℝ}
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z)
    {x : PolarPoint} (hr : 0 < x.1) (hD : 0 < polarDiscriminant w z x) :
    ScalarCoreAt w z x := by
  have hz₂ : ContDiffAt ℝ 2 z x := hz.contDiffAt.of_le (by simp)
  have hz₃ : ContDiffAt ℝ 3 z x := hz.contDiffAt.of_le (by simp)
  have hw₁ : DifferentiableAt ℝ w x.1 := hw.contDiffAt.differentiableAt (by simp)
  obtain ⟨hcartan₁, hcartan₂⟩ := heightCoframe_cartan hw₁ hz₂ hr.ne' hD
  refine ⟨height_compatibility hz₂ hr.ne', hcartan₁, hcartan₂, ?_, ?_,
    heightConnection_exterior_eq_residual hw₁ hz₃ hr.ne' hD, ?_⟩
  · simp only [heightConnectionForm, connectionRadialField, connectionRadialValue,
      connectionB1, polarDiscriminant, div_eq_mul_inv]
    ring
  · simp only [heightConnectionForm, connectionAngularField, connectionAngularValue,
      connectionInverseRoot, connectionB1, polarDiscriminant, div_eq_mul_inv, mul_inv_rev]
    ring
  · intro η hη
    exact hasDerivAt_radialScaledResidual_divergence hw hz hη hr.ne' hD

/-- The frozen S03 calculus statement, including local smooth invertibility. -/
theorem s03CalculusStatement : S03CalculusStatement := by
  constructor
  · intro w z hw hz x hr hD
    exact scalarCoreAt_of_smooth hw hz hr hD
  · intro U w z hUo hU hw hz h
    obtain ⟨P, hPs, hmetric, hinv⟩ := exists_locally_invertible_remainder_development
      hU hUo (fun _ _ => hw.contDiffAt) (fun _ _ => hz.contDiffAt)
      (fun x hx => (h x hx).1) (fun x hx => (h x hx).2.1)
      (fun x hx => (h x hx).2.2)
    refine ⟨P, hPs, ?_, hinv⟩
    intro x hx u v
    exact development_pullback_bilinear (hmetric x hx) u v

end ContinuousFlexibility.Statements
