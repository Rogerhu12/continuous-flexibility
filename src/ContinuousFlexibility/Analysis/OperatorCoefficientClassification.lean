import ContinuousFlexibility.Analysis.OperatorMixedCoefficientRegularity

/-!
# Pointwise coefficient alternatives forced by the actual operator

After the mixed coefficient has been proved differentiable, a possible
failure of differentiability of the angular coefficient can be analyzed
without applying a product rule to that coefficient. A nonvanishing
smooth multiplier cannot remove that failure. The polynomial tests then
force a precise degenerate alternative for the smooth comparison field.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- If the angular stored coefficient is not differentiable, its flux
for these tests is not differentiable either: the test's angular gradient
is nonzero at the center. Only the actual radial flux is differentiated. -/
theorem divergenceOperator_operatorJetProbe_of_not_differentiable_angular
    {L : SymmetricCoefficients} {p : PolarPoint}
    (ha : DifferentiableAt ℝ L.a p) (hb : DifferentiableAt ℝ L.b p)
    (hc : ¬ DifferentiableAt ℝ L.c p) (a b c : ℝ) :
    divergenceOperator L (operatorJetProbe p a b c) p =
      radialPartial L.b p + L.a p * a + L.b p * b := by
  have hr : radialPartial (operatorJetProbe p a b c) = operatorJetProbeRadial p a b :=
    funext fun q => (operatorJetProbe_partials p q a b c).1
  have ht : angularPartial (operatorJetProbe p a b c) = operatorJetProbeAngular p b c :=
    funext fun q => (operatorJetProbe_partials p q a b c).2
  have hrd := (hasFDerivAt_operatorJetProbeRadial p p a b).differentiableAt
  have htd := (hasFDerivAt_operatorJetProbeAngular p p b c).differentiableAt
  have ht0 : operatorJetProbeAngular p b c p ≠ 0 := by
    norm_num [operatorJetProbeAngular]
  have hflux : ¬ DifferentiableAt ℝ
      (fun q => L.b q * operatorJetProbeRadial p a b q +
        L.c q * operatorJetProbeAngular p b c q) p := by
    intro hd
    have hprod := hd.sub (hb.mul hrd)
    have he :
        (fun q =>
          (L.b q * operatorJetProbeRadial p a b q +
            L.c q * operatorJetProbeAngular p b c q) -
              L.b q * operatorJetProbeRadial p a b q) =
        (fun q => L.c q * operatorJetProbeAngular p b c q) := by
      funext q
      ring
    rw [he] at hprod
    have hback := hprod.mul (htd.inv ht0)
    have hgerm :
        (fun q => (L.c q * operatorJetProbeAngular p b c q) *
          (operatorJetProbeAngular p b c q)⁻¹) =ᶠ[𝓝 p] L.c := by
      filter_upwards [htd.continuousAt.eventually_ne ht0] with q hq
      simp only [mul_assoc, mul_inv_cancel₀ hq, mul_one]
    exact hc (hgerm.differentiableAt_iff.mp hback)
  have hzero : angularPartial
      (fun q => L.b q * operatorJetProbeRadial p a b q +
        L.c q * operatorJetProbeAngular p b c q) p = 0 := by
    simp only [angularPartial, fderiv_zero_of_not_differentiableAt hflux,
      ContinuousLinearMap.zero_apply]
  rw [divergenceOperator, hr, ht, hzero, add_zero,
    radialPartial_add (ha.mul hrd) (hb.mul htd),
    radialPartial_mul ha hrd, radialPartial_mul hb htd,
    (operatorJetProbeRadial_partials p p a b).1,
    (operatorJetProbeAngular_partials p p b c).1]
  simp only [operatorJetProbeRadial, operatorJetProbeAngular,
    sub_self, mul_zero, zero_add, add_zero, mul_one]
  ring

/-- Once both stored fields are differentiable, equality of the actual
operator action recovers all three coefficient values. -/
theorem coefficients_eq_of_differentiable_operator_action
    {L B : SymmetricCoefficients} {p : PolarPoint}
    (hLa : DifferentiableAt ℝ L.a p) (hLb : DifferentiableAt ℝ L.b p)
    (hLc : DifferentiableAt ℝ L.c p)
    (hBa : DifferentiableAt ℝ B.a p) (hBb : DifferentiableAt ℝ B.b p)
    (hBc : DifferentiableAt ℝ B.c p)
    (hop : ∀ u : PolarPoint → ℝ, ContDiff ℝ ∞ u →
      divergenceOperator L u p = divergenceOperator B u p) :
    L.a p = B.a p ∧ L.b p = B.b p ∧ L.c p = B.c p := by
  have he (a b c : ℝ) := hop (operatorJetProbe p a b c) (contDiff_operatorJetProbe p a b c)
  have h0 := he 0 0 0
  have ha := he 1 0 0
  have hb := he 0 1 0
  have hc := he 0 0 1
  rw [divergenceOperator_operatorJetProbe hLa hLb hLc,
    divergenceOperator_operatorJetProbe hBa hBb hBc] at h0 ha hb hc
  simp only [mul_zero, mul_one, add_zero] at h0 ha hb hc
  refine ⟨?_, ?_, ?_⟩ <;> linarith only [h0, ha, hb, hc]

/-- The only remaining pointwise alternative has zero angular comparison
coefficient and twice the comparison mixed coefficient. -/
theorem coefficients_degenerate_of_not_differentiable_angular
    {L B : SymmetricCoefficients} {p : PolarPoint}
    (hLa : DifferentiableAt ℝ L.a p) (hLb : DifferentiableAt ℝ L.b p)
    (hLc : ¬ DifferentiableAt ℝ L.c p)
    (hBa : DifferentiableAt ℝ B.a p) (hBb : DifferentiableAt ℝ B.b p)
    (hBc : DifferentiableAt ℝ B.c p)
    (hop : ∀ u : PolarPoint → ℝ, ContDiff ℝ ∞ u →
      divergenceOperator L u p = divergenceOperator B u p) :
    L.a p = B.a p ∧ L.b p = 2 * B.b p ∧ B.c p = 0 := by
  have he (a b c : ℝ) := hop (operatorJetProbe p a b c) (contDiff_operatorJetProbe p a b c)
  have h0 := he 0 0 0
  have ha := he 1 0 0
  have hb := he 0 1 0
  have hc := he 0 0 1
  rw [divergenceOperator_operatorJetProbe_of_not_differentiable_angular hLa hLb hLc,
    divergenceOperator_operatorJetProbe hBa hBb hBc] at h0 ha hb hc
  simp only [mul_zero, mul_one, add_zero] at h0 ha hb hc
  refine ⟨?_, ?_, ?_⟩ <;> linarith only [h0, ha, hb, hc]

/-- This pointwise alternative is derived from the genuine action on
globally smooth tests. No stored mixed/angular regularity is assumed. -/
theorem operatorCoefficients_value_alternative
    {L B : SymmetricCoefficients} {p : PolarPoint}
    (hLa : DifferentiableAt ℝ L.a p)
    (hBa : DifferentiableAt ℝ B.a p) (hBb : DifferentiableAt ℝ B.b p)
    (hBc : DifferentiableAt ℝ B.c p) (hBa0 : B.a p ≠ 0)
    (hop : ∀ u : PolarPoint → ℝ, ContDiff ℝ ∞ u →
      divergenceOperator L u p = divergenceOperator B u p) :
    (L.a p = B.a p ∧ L.b p = B.b p ∧ L.c p = B.c p) ∨
      (L.a p = B.a p ∧ L.b p = 2 * B.b p ∧ B.c p = 0) := by
  have hLb := differentiableAt_mixedCoefficient_of_operator_action
    hLa hBa hBb hBc hBa0 hop
  by_cases hLc : DifferentiableAt ℝ L.c p
  · exact Or.inl (coefficients_eq_of_differentiable_operator_action
      hLa hLb hLc hBa hBb hBc hop)
  · exact Or.inr (coefficients_degenerate_of_not_differentiable_angular
      hLa hLb hLc hBa hBb hBc hop)

end ContinuousFlexibility.Analysis
