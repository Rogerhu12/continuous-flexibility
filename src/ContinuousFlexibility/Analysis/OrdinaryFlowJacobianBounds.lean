module

public import ContinuousFlexibility.Analysis.CanonicalVariationBounds
public import ContinuousFlexibility.Analysis.CanonicalMaterialAbsorption
public import ContinuousFlexibility.Analysis.CanonicalNeighborhoodRestriction
public import ContinuousFlexibility.Analysis.ReferenceCircleFlow
public import ContinuousFlexibility.Analysis.CircleFlowEndpointBounds

/-!
# Uniform angular Jacobians of the ordinary flows

The actual first state variation gives a small angular derivative difference
from the reference flow. Material absorption makes this smallness uniform in
the component index. The reference derivative is exactly one, and passing
increment bounds to the radial endpoints gives the same closed-interval
Jacobian bounds on one smaller state neighborhood.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

def OrdinaryFlowJacobianBounds (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base : ℕ) (ε : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, ∀ m r,
    r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      (1 / 2 : ℝ) ≤ deriv (C.minusFlow z m r) θ ∧ deriv (C.minusFlow z m r) θ ≤ 2

theorem ordinaryFlowFamily_angular_eq_deriv_sub_one
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {base : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε))
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (m : ℕ) {p : PolarPoint} (hp : p.1 ∈ Icc (C.left m) (C.right m)) :
    ordinaryFlowFamily S C m 0 1 p z = deriv (C.minusFlow z m p.1) p.2 - 1 := by
  have hcurrent : DifferentiableAt ℝ (C.minusFlow z m p.1) p.2 :=
    differentiableAt_of_deriv_ne_zero ((hflow z hz m p.2).2.2.2 p.1 hp).1.ne'
  have href := hasDerivAt_ordinaryFlow_zeroParameter hflow
    (reference_mem_stateNeighborhood S C base hε) m hp p.2
  simp only [ordinaryFlowFamily, mixedDerivative, iteratedDeriv_zero, iteratedDeriv_one]
  exact (hcurrent.hasDerivAt.sub href).deriv

/-- N01 implies the actual uniform angular Jacobian bounds on a single
smaller neighborhood, including the two radial endpoints of every component. -/
theorem exists_ordinaryFlowJacobianBounds_of_n01
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hN : N01Properties D T S C base loss ε) :
    ∃ base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      OrdinaryFlowJacobianBounds S C base' ε' := by
  have hε : 0 < ε := hN.2.1
  have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
    hN.2.2.2.2.2.2.1
  have hlength (m : ℕ) : C.left m < C.right m := (hN.2.2.2.1.1 m).2.1
  obtain ⟨parameterLoss, horders⟩ := ordinaryFlowFamily_le_linear_high_of_n01 hT hN
  obtain ⟨B, hB, hbound⟩ := horders 1
  let V : ℕ → Set PolarPoint := fun m => Ioo (C.left m) (C.right m) ×ˢ univ
  let F : AnnularState S × ℝ → ℕ → PolarPoint → ℝ :=
    fun z m p => ordinaryFlowFamily S C m 0 1 p z
  have hK : 0 < (2 + 2 * ε : ℝ) := by linarith
  have hquant : ∀ z ∈ stateNeighborhood S C base ε, True →
      ∀ m p, p ∈ V m → |F z m p| ≤
        B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B * (2 + 2 * ε) *
            (stateGrading S (max base (1 + (loss + parameterLoss))) (z.1 - C.referenceState) + |z.2|) := by
    intro z hz _ m p hp
    simpa only [F, pairGrading_apply, realGrading, coe_normSeminorm,
      Real.norm_eq_abs, Prod.fst_sub, Prod.snd_sub, sub_zero] using
      hbound m 1 p le_rfl hp.1 z hz
  obtain ⟨base', ε', hb, _, hε', hsmall, hnear⟩ :=
    exists_stateNeighborhood_uniform_smallness hN.1.1 hT hε (fun _ => True)
      C.cell V F hB (by norm_num : (0 : ℝ) < 3 / 4) hK hquant
      (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨base', ε', hb, hε', hsmall, ?_⟩
  intro z hz m r hr θ
  have hzold := stateNeighborhood_mono S C hb hsmall hz
  have hdiff (t : ℝ) (ht : t ∈ Icc (C.left m) (C.right m)) :
      Differentiable ℝ (C.minusFlow z m t) := fun φ =>
    differentiableAt_of_deriv_ne_zero ((hflow z hzold m φ).2.2.2 t ht).1.ne'
  have hinterior (t : ℝ) (ht : t ∈ Ioo (C.left m) (C.right m)) (φ : ℝ) :
      (1 / 2 : ℝ) ≤ deriv (C.minusFlow z m t) φ ∧ deriv (C.minusFlow z m t) φ ≤ 2 := by
    have h := hnear z hz trivial m (t, φ) ⟨ht, mem_univ _⟩
    dsimp only [F] at h
    rw [ordinaryFlowFamily_angular_eq_deriv_sub_one hε hflow hzold m
      (Ioo_subset_Icc_self ht)] at h
    have habs := abs_lt.mp h
    constructor <;> linarith
  exact circleFlow_deriv_bounds_on_Icc (hlength m)
    (fun φ => (hflow z hzold m φ).2.1) hdiff hinterior hr θ

/-- The Jacobian smallness choice preserves the complete preceding stage
and both qualitative canonical parts on the same new neighborhood. -/
theorem exists_restricted_canonicalStage_with_ordinaryFlowJacobianBounds
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
      OrdinaryFlowJacobianBounds S C base' ε' := by
  obtain ⟨base', ε', hb, hε', hsmall, hflow⟩ :=
    exists_ordinaryFlowJacobianBounds_of_n01 hT hN.1.1
  exact ⟨base', ε', hb, hε', hsmall,
    nonlinearPropertiesThrough03_restrict hT hN hb le_rfl hε' hsmall,
    n04PartA_restrict hA hb hsmall, n04PartB_restrict hB hb hsmall, hflow⟩

end ContinuousFlexibility.Analysis
