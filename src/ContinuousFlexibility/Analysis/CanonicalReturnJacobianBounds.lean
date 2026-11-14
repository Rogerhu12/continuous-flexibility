module

public import ContinuousFlexibility.Analysis.CircleInverseDerivativeBounds
public import ContinuousFlexibility.Analysis.OrdinaryFlowJacobianBounds

/-!
# Jacobians of the actual return coordinates

The ordinary-flow bound controls the inverse return without assuming its
regularity. The right coordinate is the odd part of the left coordinate
composed with that inverse, so its derivative is an average of two positive
products. This supplies a uniform lower bound before differentiating the
right inverse. All bounds hold on the same common state neighborhood.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

/-- Reflection turns the derivative of an odd projection into an average. -/
theorem hasDerivAt_oddPart_of_two_derivatives
    {f : ℝ → ℝ} {a b θ : ℝ}
    (hp : HasDerivAt f a θ) (hn : HasDerivAt f b (-θ)) :
    HasDerivAt (oddPart f) ((a + b) / 2) θ := by
  change HasDerivAt (fun t : ℝ => (f t - f (-t)) / 2) ((a + b) / 2) θ
  simpa only [Pi.sub_apply, Function.comp_apply, mul_neg_one, sub_neg_eq_add] using
    (hp.sub (hn.comp θ (hasDerivAt_id θ).neg)).div_const 2

private theorem mul_bounds_of_half_two {a b : ℝ}
    (ha : (1 / 2 : ℝ) ≤ a ∧ a ≤ 2) (hb : (1 / 2 : ℝ) ≤ b ∧ b ≤ 2) :
    (1 / 4 : ℝ) ≤ a * b ∧ a * b ≤ 4 := by
  have ha0 : 0 ≤ a := le_trans (by norm_num) ha.1
  have hb0 : 0 ≤ b := le_trans (by norm_num) hb.1
  have hlo := mul_le_mul ha.1 hb.1 (by norm_num : (0 : ℝ) ≤ 1 / 2) ha0
  have hhi := mul_le_mul ha.2 hb.2 hb0 (by norm_num : (0 : ℝ) ≤ 2)
  constructor <;> nlinarith

/-- The scalar return construction needs only the actual forward derivative
bounds and the two actual right-inverse identities. -/
theorem circleReturn_inverse_jacobian_bounds
    {f g l k : ℝ → ℝ} {T : ℝ}
    (hf : ∀ θ, (1 / 2 : ℝ) ≤ deriv f θ ∧ deriv f θ ≤ 2)
    (hl : ∀ θ, (1 / 2 : ℝ) ≤ deriv l θ ∧ deriv l θ ≤ 2)
    (hfg : ∀ θ, f (g θ) = θ)
    (hrk : ∀ θ, oddPart (fun t => l (g t) - T) (k θ) = θ) :
    ∀ θ,
      ((1 / 2 : ℝ) ≤ deriv g θ ∧ deriv g θ ≤ 2) ∧
      ((1 / 4 : ℝ) ≤ deriv (oddPart (fun t => l (g t) - T)) θ ∧
        deriv (oddPart (fun t => l (g t) - T)) θ ≤ 4) ∧
      ((1 / 4 : ℝ) ≤ deriv k θ ∧ deriv k θ ≤ 4) := by
  have hg (θ : ℝ) : (1 / 2 : ℝ) ≤ deriv g θ ∧ deriv g θ ≤ 2 := by
    have h := inverse_deriv_bounds (by norm_num : (0 : ℝ) < 1 / 2) hf hfg θ
    norm_num at h
    exact h
  have hld (θ : ℝ) : DifferentiableAt ℝ l θ :=
    differentiableAt_of_deriv_ne_zero
      ((by norm_num : (0 : ℝ) < 1 / 2).trans_le (hl θ).1).ne'
  have hgd (θ : ℝ) : DifferentiableAt ℝ g θ :=
    differentiableAt_of_deriv_ne_zero
      ((by norm_num : (0 : ℝ) < 1 / 2).trans_le (hg θ).1).ne'
  have hcomp (θ : ℝ) :
      HasDerivAt (fun t => l (g t) - T) (deriv l (g θ) * deriv g θ) θ :=
    ((hld (g θ)).hasDerivAt.comp θ (hgd θ).hasDerivAt).sub_const T
  have hr (θ : ℝ) :
      (1 / 4 : ℝ) ≤ deriv (oddPart (fun t => l (g t) - T)) θ ∧
        deriv (oddPart (fun t => l (g t) - T)) θ ≤ 4 := by
    rw [(hasDerivAt_oddPart_of_two_derivatives (hcomp θ) (hcomp (-θ))).deriv]
    have hp := mul_bounds_of_half_two (hl (g θ)) (hg θ)
    have hn := mul_bounds_of_half_two (hl (g (-θ))) (hg (-θ))
    constructor <;> linarith
  intro θ
  refine ⟨hg θ, hr θ, ?_⟩
  have h := inverse_deriv_bounds (by norm_num : (0 : ℝ) < 1 / 4) hr hrk θ
  norm_num at h
  exact h

/-- Actual inverse returns and right coordinates, with the original data. -/
def CanonicalReturnJacobianBounds (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base : ℕ) (ε : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ m θ,
    ((1 / 2 : ℝ) ≤ deriv (C.minusReturnInverse z m) θ ∧
      deriv (C.minusReturnInverse z m) θ ≤ 2) ∧
    ((1 / 4 : ℝ) ≤ deriv (rightChartCandidate S C z m) θ ∧
      deriv (rightChartCandidate S C z m) θ ≤ 4) ∧
    ((1 / 4 : ℝ) ≤ deriv (C.rightChartInverse z m) θ ∧
      deriv (C.rightChartInverse z m) θ ≤ 4)

/-- The qualitative inverse identities in N01 acquire quantitative Jacobians
from the ordinary flow bound. No regularity of either inverse is assumed. -/
theorem canonicalReturnJacobianBounds_of_n01
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε) :
    CanonicalReturnJacobianBounds S C base ε := by
  intro z hz hs m θ
  have hlength : C.left m < C.right m := (hN.2.2.2.1.1 m).2.1
  have hl (t : ℝ) := hN.2.2.2.2.2.2.2.1 z hz hs m t
  have hi (t : ℝ) := hN.2.2.2.2.2.2.2.2.1 z hz hs m t
  exact circleReturn_inverse_jacobian_bounds
    (fun t => hflow z hz m (C.right m) ⟨hlength.le, le_rfl⟩ t)
    (fun t => ⟨(hl t).1, (hl t).2.1⟩)
    (fun t => (hi t).1) (fun t => (hi t).2.2.1) θ

/-- The actual return bounds are available while retaining the entire preceding
stage and both canonical parts on one smaller neighborhood. -/
theorem exists_restricted_canonicalStage_with_returnJacobianBounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε) :
    ∃ base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      NonlinearPropertiesThrough03 D T S C R L base' loss ε' ∧
      N04PartA D S C K base' ε' ∧ N04PartB S C L K base' ε' ∧
      OrdinaryFlowJacobianBounds S C base' ε' ∧
      CanonicalReturnJacobianBounds S C base' ε' := by
  obtain ⟨base', ε', hb, hε', hsmall, hN', hA', hB', hflow⟩ :=
    exists_restricted_canonicalStage_with_ordinaryFlowJacobianBounds hT hN hA hB
  exact ⟨base', ε', hb, hε', hsmall, hN', hA', hB', hflow,
    canonicalReturnJacobianBounds_of_n01 hN'.1.1 hflow⟩

end ContinuousFlexibility.Analysis
