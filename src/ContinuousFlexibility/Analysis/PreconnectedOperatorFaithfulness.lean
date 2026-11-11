import ContinuousFlexibility.Analysis.OperatorCoefficientClassification
import Mathlib.Topology.Connected.Basic

/-!
# Faithfulness of an actual hyperbolic divergence operator

On a preconnected domain the pointwise regular/degenerate alternatives
are closed and disjoint, because the comparison discriminant is strictly
positive. A single point where the stored mixed coefficient vanishes
excludes the degenerate alternative on the whole domain. In particular,
an actual canonical piece can supply that point by reflection symmetry.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem continuous_restrict_of_differentiableAt
    {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hf : ∀ p ∈ U, DifferentiableAt ℝ f p) :
    Continuous (fun p : U => f p) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact ContinuousAt.comp (f := (Subtype.val : U → PolarPoint)) (x := p)
    (hf p p.property).continuousAt continuous_subtype_val.continuousAt

/-- The stored coefficient values are uniquely recovered on a connected
actual piece. Smoothness of the mixed/angular stored fields is not an
input; actual equality of the operators on global smooth tests forces it
locally, with the apparent degenerate alternative excluded by topology. -/
theorem coefficients_eq_on_of_preconnected_operator_action
    {U : Set PolarPoint} {L B : SymmetricCoefficients}
    (hU : IsPreconnected U)
    (hLa : ∀ p ∈ U, DifferentiableAt ℝ L.a p)
    (hBa : ∀ p ∈ U, DifferentiableAt ℝ B.a p)
    (hBb : ∀ p ∈ U, DifferentiableAt ℝ B.b p)
    (hBc : ∀ p ∈ U, DifferentiableAt ℝ B.c p)
    (hBa0 : ∀ p ∈ U, B.a p ≠ 0)
    (hdisc : ∀ p ∈ U, 0 < B.b p ^ 2 - B.a p * B.c p)
    (haxis : ∃ p ∈ U, L.b p = 0)
    (hop : ∀ p ∈ U, ∀ u : PolarPoint → ℝ, ContDiff ℝ ∞ u →
      divergenceOperator L u p = divergenceOperator B u p) :
    ∀ p ∈ U, L.a p = B.a p ∧ L.b p = B.b p ∧ L.c p = B.c p := by
  classical
  have hLb (p : PolarPoint) (hp : p ∈ U) : DifferentiableAt ℝ L.b p :=
    differentiableAt_mixedCoefficient_of_operator_action
      (hLa p hp) (hBa p hp) (hBb p hp) (hBc p hp) (hBa0 p hp) (hop p hp)
  have halt (p : PolarPoint) (hp : p ∈ U) :=
    operatorCoefficients_value_alternative
      (hLa p hp) (hBa p hp) (hBb p hp) (hBc p hp) (hBa0 p hp) (hop p hp)
  let Good : Set U := {p | L.b p = B.b p}
  let Bad : Set U := {p | L.b p = 2 * B.b p ∧ B.c p = 0}
  have hLbcont : Continuous (fun p : U => L.b p) :=
    continuous_restrict_of_differentiableAt hLb
  have hBbcont : Continuous (fun p : U => B.b p) :=
    continuous_restrict_of_differentiableAt hBb
  have hBccont : Continuous (fun p : U => B.c p) :=
    continuous_restrict_of_differentiableAt hBc
  have hGood : IsClosed Good := isClosed_eq hLbcont hBbcont
  have hBad : IsClosed Bad :=
    (isClosed_eq hLbcont (continuous_const.mul hBbcont)).inter
      (isClosed_eq hBccont continuous_const)
  have hcover : (univ : Set U) ⊆ Good ∪ Bad := by
    intro p _
    rcases halt p p.property with hgood | hbad
    · exact Or.inl hgood.2.1
    · exact Or.inr hbad.2
  obtain ⟨p₀, hp₀, hzero⟩ := haxis
  have hbase : (⟨p₀, hp₀⟩ : U) ∈ Good := by
    rcases halt p₀ hp₀ with hgood | hbad
    · exact hgood.2.1
    · have hb0 : B.b p₀ = 0 := by linarith only [hzero, hbad.2.1]
      have hd := hdisc p₀ hp₀
      rw [hb0, hbad.2.2] at hd
      norm_num at hd
  letI : PreconnectedSpace U := Subtype.preconnectedSpace hU
  have hnotBad (p : U) : p ∉ Bad := by
    intro hp
    obtain ⟨q, _, hqGood, hqBad⟩ :=
      (isPreconnected_closed_iff.mp (isPreconnected_univ : IsPreconnected (univ : Set U)))
        Good Bad hGood hBad hcover
        ⟨⟨p₀, hp₀⟩, mem_univ _, hbase⟩ ⟨p, mem_univ _, hp⟩
    have hqg : L.b q = B.b q := hqGood
    have hqb : L.b q = 2 * B.b q ∧ B.c q = 0 := hqBad
    have hb0 : B.b q = 0 := by linarith only [hqg, hqb.1]
    have hd := hdisc q q.property
    rw [hb0, hqb.2] at hd
    norm_num at hd
  intro p hp
  rcases halt p hp with hgood | hbad
  · exact hgood
  · exact (hnotBad ⟨p, hp⟩ hbad.2).elim

end ContinuousFlexibility.Analysis
