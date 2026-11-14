module

public import ContinuousFlexibility.Scalar.WeightedGreen

/-!
# Physical source compatibility of the corrected linear operator

The constant test in the actual Green identity shows that the corrected
operator has zero physical mean.  The common height is unrestricted at its
left endpoint; it is the decoded normal coefficient row that annihilates
the boundary term.  Compatibility of a decoded linear output follows from
the defining physical source functional.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem physicalSourceIntegral_eq_scaled_annularIntegral (D : ReferenceData)
    (f : PolarPoint → ℝ) :
    physicalSourceIntegral D f = (1 / Real.pi) * scalarAnnularIntegral D f := by
  unfold physicalSourceIntegral angularMean scalarAnnularIntegral
  rw [intervalIntegral.integral_const_mul]

theorem scalarStateOperator_physicalSourceIntegral_eq_zero_of_decode
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S)
    (c : Fin 3 → ScalarFieldSpace S)
    (hc : ∀ i p, scalarFieldDecode S (c i) p = scalarCoefficientComponent D S x i p)
    (u : ScalarCommonHeight S) : physicalSourceIntegral D (scalarStateOperator D S x u) = 0 := by
  obtain ⟨hA, hB⟩ := scalarStateAB_contDiff_and_flatJets_of_decode hD hT hS x c hc
  have hC := (scalarStateCorrectedC_contDiff_and_flatJets_of_decode hD hT hS x c hc).1
  have hu := scalarCommonHeightDecode_contDiff hT hS u
  have hboundary (r : ℝ) (hr : r ≤ D.a ∨ D.b ≤ r) (θ : ℝ) :
      greenNormalFlux (scalarStateA D S x) (scalarStateB D S x)
        (fun _ => 1) (scalarCommonHeightDecode S u) (r, θ) = 0 := by
    have hz := scalarStateNormalFlux_eq_zero_outside_of_decode hD hT hS x c hc u hr θ
    change 1 * scalarStateNormalFlux D S x u (r, θ) -
      scalarCommonHeightDecode S u (r, θ) *
        (scalarStateA D S x (r, θ) * radialPartial (fun _ => 1) (r, θ) +
          scalarStateB D S x (r, θ) * angularPartial (fun _ => 1) (r, θ)) = 0
    simp only [hz, radialPartial_const, angularPartial_const, mul_zero, add_zero, sub_zero]
  have hi := integral_heightCorrected_green_eq_zero
    (w := scalarStateProfile D S x) (z := scalarStateHeight D S x)
    (φ := fun _ => 1) (ψ := scalarCommonHeightDecode S u)
    (a := D.a) (b := D.b) (T := Real.pi)
    (fun _ _ => hA.1.contDiffAt) (fun _ _ => hB.1.contDiffAt) (fun _ _ => hC.contDiffAt)
    (fun _ _ => contDiffAt_const) (fun _ _ => hu.contDiffAt)
    (scalarStateHeight_periodic hS x) (fun _ => rfl) (scalarCommonHeightDecode_periodic hS u)
    (fun θ _ => hboundary D.a (Or.inl le_rfl) θ)
    (fun θ _ => hboundary D.b (Or.inr le_rfl) θ)
  have hzero : scalarAnnularIntegral D (scalarStateOperator D S x u) = 0 := by
    simpa only [scalarAnnularIntegral, scalarStateOperator,
      heightCorrectedDivergence_const, one_mul, mul_zero, sub_zero] using hi
  rw [physicalSourceIntegral_eq_scaled_annularIntegral, hzero, mul_zero]

theorem scalarStateOperator_compatible_of_decode
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S)
    (c : Fin 3 → ScalarFieldSpace S)
    (hc : ∀ i p, scalarFieldDecode S (c i) p = scalarCoefficientComponent D S x i p)
    (u : ScalarCommonHeight S) (f : ScalarHeightSpace S)
    (hf : ∀ p, (S.height scalarBeta).decode f p = scalarStateOperator D S x u p) :
    S.Q f = 0 := by
  have hQ : S.Q f = physicalSourceIntegral D ((S.height scalarBeta).decode f) := by
    rcases hS with ⟨_, _, _, _, _, _, _, hQ, _⟩
    exact hQ f
  rw [hQ, funext hf]
  exact scalarStateOperator_physicalSourceIntegral_eq_zero_of_decode hD hT hS x c hc u

theorem weightedScalar_linear_conservation_clause
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (W : WeightedScalarData S)
    {U : Set (ScalarWeightedState S)}
    (hc : ∀ x ∈ U, ∀ i p,
      scalarFieldDecode S (W.coefficients x i) p = scalarCoefficientComponent D S x i p)
    (hlinear : ∀ x ∈ U, ∀ u p,
      (S.height scalarBeta).decode (W.linear x u) p = scalarStateOperator D S x u p) :
    ∀ x ∈ U, ∀ u, S.Q (W.linear x u) = 0 := by
  intro x hx u
  exact scalarStateOperator_compatible_of_decode hD hT hS x (W.coefficients x) (hc x hx)
    u (W.linear x u) (hlinear x hx u)

end ContinuousFlexibility.Statements
