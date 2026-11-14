module

public import ContinuousFlexibility.Radial.ReferenceSourceCosine

/-!
# Actual reference outputs from square-summable cosine modes

The angular representative is pointwise even and periodic. Its actual
product-measure L² norm equals the sum of the radial mode norms, so adding
the prescribed left constant gives the frozen output realization and its
exact norm without an additional synthesis assumption.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory Filter
open scoped ENNReal

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

/-- The physical field, with the left constant and scalar coordinate restored. -/
def referenceOutputCosine (D : ReferenceData) (γ M aL ν : ℝ)
    (a : lp (fun _ : ℕ => Lp ℝ 2 (referenceRadialWeightedMeasure D γ (-M))) 2) :
    RadialUnknown :=
  (fun x => aL * D.chiLeft x.1 + referenceCosineRepresentative a x, ν)

@[simp]
theorem referenceOutputCosine_remainder (D : ReferenceData) (γ M aL ν : ℝ)
    (a : lp (fun _ : ℕ => Lp ℝ 2 (referenceRadialWeightedMeasure D γ (-M))) 2) :
    outputRemainder D aL (referenceOutputCosine D γ M aL ν a) =
      referenceCosineRepresentative a := by
  funext x
  dsimp [outputRemainder, referenceOutputCosine]
  ring

theorem referenceOutputCosine_periodic (D : ReferenceData) (γ M aL ν : ℝ)
    (a : lp (fun _ : ℕ => Lp ℝ 2 (referenceRadialWeightedMeasure D γ (-M))) 2) :
    Function.Periodic (referenceOutputCosine D γ M aL ν a).1 (0, Real.pi) := by
  rintro ⟨r, θ⟩
  change aL * D.chiLeft (r + 0) + referenceCosineRepresentative a (r + 0, θ + Real.pi) =
    aL * D.chiLeft r + referenceCosineRepresentative a (r, θ)
  rw [add_zero]
  exact congrArg (fun t : ℝ => aL * D.chiLeft r + t)
    (referenceCosineRepresentative_periodic a r θ)

theorem referenceOutputCosine_even (D : ReferenceData) (γ M aL ν : ℝ)
    (a : lp (fun _ : ℕ => Lp ℝ 2 (referenceRadialWeightedMeasure D γ (-M))) 2)
    (r θ : ℝ) :
    (referenceOutputCosine D γ M aL ν a).1 (r, -θ) =
      (referenceOutputCosine D γ M aL ν a).1 (r, θ) := by
  change aL * D.chiLeft r + referenceCosineRepresentative a (r, -θ) =
    aL * D.chiLeft r + referenceCosineRepresentative a (r, θ)
  rw [referenceCosineRepresentative_even]

theorem referenceOutputCosine_realization {D : ReferenceData}
    (hab : D.a ≤ D.b) (hD : RadialPartition D) (γ M aL ν : ℝ)
    (a : lp (fun _ : ℕ => Lp ℝ 2 (referenceRadialWeightedMeasure D γ (-M))) 2) :
    OutputRealization D γ M aL (referenceOutputCosine D γ M aL ν a) := by
  apply (outputRealization_iff_memLp_weighted hab hD).mpr
  refine ⟨?_, referenceOutputCosine_periodic D γ M aL ν a,
    referenceOutputCosine_even D γ M aL ν a⟩
  rw [referenceOutputCosine_remainder, referenceWeightedMeasure_eq_prod hD γ (-M)]
  exact referenceCosineRepresentative_memLp a

theorem referenceOutputCosine_member {D : ReferenceData}
    (hab : D.a ≤ D.b) (hD : RadialPartition D) (γ M aL ν : ℝ)
    (a : lp (fun _ : ℕ => Lp ℝ 2 (referenceRadialWeightedMeasure D γ (-M))) 2) :
    OutputMember D γ M (referenceOutputCosine D γ M aL ν a) :=
  ⟨aL, referenceOutputCosine_realization hab hD γ M aL ν a⟩

/-- Exact equality with the frozen output norm, including both scalar coordinates. -/
theorem referenceOutputCosine_norm_sq {D : ReferenceData}
    (hab : D.a ≤ D.b) (hD : RadialPartition D) (γ M aL ν : ℝ)
    (a : lp (fun _ : ℕ => Lp ℝ 2 (referenceRadialWeightedMeasure D γ (-M))) 2) :
    outputNormSquare D γ M aL (referenceOutputCosine D γ M aL ν a) =
      aL ^ 2 + ν ^ 2 + ∑' n : ℕ, ‖a n‖ ^ 2 := by
  have hU := referenceOutputCosine_realization hab hD γ M aL ν a
  have hl : RadialCellIntegrable D (referenceCosineRepresentative a) := by
    simpa only [referenceOutputCosine_remainder] using hU.1
  have hs : Summable (sourceCellSquare D γ (-M) (referenceCosineRepresentative a)) := by
    simpa only [referenceOutputCosine_remainder, sourceCellSquare_neg_fun] using hU.2.1
  unfold outputNormSquare
  rw [referenceOutputCosine_remainder]
  change aL ^ 2 + ν ^ 2 +
      (∑' m, outputCellSquare D γ M (referenceCosineRepresentative a) m) =
    aL ^ 2 + ν ^ 2 + ∑' n : ℕ, ‖a n‖ ^ 2
  apply congrArg (fun t : ℝ => aL ^ 2 + ν ^ 2 + t)
  calc
    (∑' m, outputCellSquare D γ M (referenceCosineRepresentative a) m) =
        ∑' m, sourceCellSquare D γ (-M) (referenceCosineRepresentative a) m := by
      simp only [sourceCellSquare_neg]
    _ = ∫ x, referenceCosineRepresentative a x ^ 2
        ∂referenceWeightedMeasure D γ (-M) :=
      (integral_sq_referenceWeightedMeasure_eq hab hD hl hs).symm
    _ = ∫ x, referenceCosineRepresentative a x ^ 2
        ∂(referenceRadialWeightedMeasure D γ (-M)).prod referenceAngularMeasure := by
      rw [referenceWeightedMeasure_eq_prod hD γ (-M)]
    _ = ‖(referenceCosineRepresentative_memLp a).toLp
        (referenceCosineRepresentative a)‖ ^ 2 :=
      (referenceL2_toLp_norm_sq (referenceCosineRepresentative_memLp a)).symm
    _ = ∑' n : ℕ, ‖a n‖ ^ 2 := referenceCosineRepresentative_norm_sq a

end ContinuousFlexibility.Statements
