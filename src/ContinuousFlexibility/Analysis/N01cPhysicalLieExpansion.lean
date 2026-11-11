import ContinuousFlexibility.Analysis.N01cPhysicalLieWords

/-!
# Finite word expansion of every physical Lie derivative

The next Lie derivative records either a radial hit on an old factor,
or an angular hit followed by a new undifferentiated speed factor.
Repeated terms remain separate finite indices. Every term is nonempty,
has at most n+1 factors, and has exactly n spatial differentiations.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators Topology

/-- Universal finite data for the n-th physical Lie expression. -/
structure PhysicalLieExpansion (n : ℕ) where
  Index : Type
  [fintype : Fintype Index]
  arity : Index → ℕ
  words : ∀ t, Fin (arity t) → PhysicalLieWord
  arity_pos : ∀ t, 0 < arity t
  arity_le : ∀ t, arity t ≤ n + 1
  total_order : ∀ t, (∑ i, (words t i).order) = n
  formula : ∀ {Ω : Set PolarPoint} {f : PolarPoint → ℝ},
    IsOpen Ω → ContDiffOn ℝ ∞ f Ω → ∀ p ∈ Ω,
      physicalFlowLieJet f n p = ∑ t : Index, ∏ i, (words t i).eval f p

attribute [instance] PhysicalLieExpansion.fintype

private def physicalLieExpansion_zero : PhysicalLieExpansion 0 where
  Index := Unit
  fintype := inferInstance
  arity := fun _ => 1
  words := fun _ _ => PhysicalLieWord.empty
  arity_pos := by intro _; decide
  arity_le := by intro _; decide
  total_order := by
    intro _
    simp only [PhysicalLieWord.empty, Finset.sum_const_zero]
  formula := by
    intro Ω f hΩ hf p hp
    simp only [physicalFlowLieJet, Fintype.sum_unique, Fintype.prod_unique,
      PhysicalLieWord.eval_empty]

/-- The physical Lie operator produces two families of actual terms. -/
def PhysicalLieExpansion.step {n : ℕ} (e : PhysicalLieExpansion n) :
    PhysicalLieExpansion (n + 1) where
  Index := (Σ t : e.Index, Fin (e.arity t)) ⊕ (Σ t : e.Index, Fin (e.arity t))
  fintype := inferInstance
  arity := fun t => match t with
    | Sum.inl ti => e.arity ti.1
    | Sum.inr ti => e.arity ti.1 + 1
  words := fun t => match t with
    | Sum.inl ti => physicalLieHit (e.words ti.1) 0 ti.2
    | Sum.inr ti => Fin.cons PhysicalLieWord.empty (physicalLieHit (e.words ti.1) 1 ti.2)
  arity_pos := by
    rintro (ti | ti)
    · exact e.arity_pos ti.1
    · exact Nat.succ_pos _
  arity_le := by
    rintro (ti | ti)
    · exact (e.arity_le ti.1).trans (by omega)
    · exact Nat.add_le_add_right (e.arity_le ti.1) 1
  total_order := by
    rintro (ti | ti)
    · exact (physicalLieHit_total_order (e.words ti.1) 0 ti.2).trans
        (congrArg (fun l : ℕ => l + 1) (e.total_order ti.1))
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
        PhysicalLieWord.empty, Nat.zero_add]
      exact (physicalLieHit_total_order (e.words ti.1) 1 ti.2).trans
        (congrArg (fun l : ℕ => l + 1) (e.total_order ti.1))
  formula := by
    classical
    intro Ω f hΩ hf p hp
    let F : PolarPoint → ℝ := fun q => ∑ t : e.Index, ∏ i, (e.words t i).eval f q
    have he : physicalFlowLieJet f n =ᶠ[𝓝 p] F := by
      filter_upwards [hΩ.mem_nhds hp] with q hq
      exact e.formula hΩ hf q hq
    have hd := he.fderiv_eq (𝕜 := ℝ)
    calc
      physicalFlowLieJet f (n + 1) p =
          fderiv ℝ F p (cylinderBasisVector 0) +
            f p * fderiv ℝ F p (cylinderBasisVector 1) := by
        change fderiv ℝ (physicalFlowLieJet f n) p (1, 0) +
          f p * fderiv ℝ (physicalFlowLieJet f n) p (0, 1) = _
        rw [hd]
        simp only [cylinderBasisVector, if_pos rfl,
          if_neg (by decide : (1 : Fin 2) ≠ 0)]
      _ = (∑ ti : (Σ t : e.Index, Fin (e.arity t)),
            ∏ i, (physicalLieHit (e.words ti.1) 0 ti.2 i).eval f p) +
          f p * (∑ ti : (Σ t : e.Index, Fin (e.arity t)),
            ∏ i, (physicalLieHit (e.words ti.1) 1 ti.2 i).eval f p) := by
        rw [fderiv_physicalLieSum e.arity e.words hΩ hf 0 hp,
          fderiv_physicalLieSum e.arity e.words hΩ hf 1 hp]
      _ = _ := by
        rw [Fintype.sum_sum_type]
        apply congrArg₂ (fun a b : ℝ => a + b)
        · rfl
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ti _
          simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
            PhysicalLieWord.eval_empty]

/-- Finite data are selected before the speed or evaluation point. -/
def physicalLieExpansion : (n : ℕ) → PhysicalLieExpansion n
  | 0 => physicalLieExpansion_zero
  | n + 1 => (physicalLieExpansion n).step

theorem physicalLieExpansion_spatial_order (n : ℕ) (t : (physicalLieExpansion n).Index) :
    (∑ i, ((physicalLieExpansion n).words t i).radialOrder +
      ((physicalLieExpansion n).words t i).angularOrder) = n := by
  simp only [PhysicalLieWord.radialOrder_add_angularOrder]
  exact (physicalLieExpansion n).total_order t

theorem physicalLieExpansion_radial_order_le (n : ℕ)
    (t : (physicalLieExpansion n).Index) :
    (∑ i, ((physicalLieExpansion n).words t i).radialOrder) ≤ n := by
  calc
    _ ≤ ∑ i, ((physicalLieExpansion n).words t i).order :=
      Finset.sum_le_sum (fun i _ => PhysicalLieWord.radialOrder_le _)
    _ = n := (physicalLieExpansion n).total_order t

/-- The finite expansion is a formula for the actual mixed spatial jets. -/
theorem physicalFlowLieJet_eq_sum_mixedDerivative
    {Ω : Set PolarPoint} {f : PolarPoint → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) (n : ℕ)
    {p : PolarPoint} (hp : p ∈ Ω) :
    physicalFlowLieJet f n p =
      ∑ t : (physicalLieExpansion n).Index, ∏ i,
        mixedDerivative ((physicalLieExpansion n).words t i).radialOrder
          ((physicalLieExpansion n).words t i).angularOrder f p := by
  rw [(physicalLieExpansion n).formula hΩ hf p hp]
  apply Finset.sum_congr rfl
  intro t _
  exact Finset.prod_congr rfl (fun i _ =>
    PhysicalLieWord.eval_eq_mixedDerivative hΩ hf _ hp)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators

/-- The original ordinary-flow family has the finite physical Lie
representation on its original component. -/
theorem ordinaryFlowFamily_eq_finitePhysicalLieDifference
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {U : Set (AnnularState S × ℝ)}
    (hFlow : ordinaryFlowConditions D S C U)
    (hlam : ∀ z ∈ U, ∀ m, ContDiffOn ℝ ∞
      (minusCharacteristicSpeed (originalCoefficients D S C z))
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)))
    (hΘ : ∀ z ∈ U, ∀ m, ContDiffOn ℝ ∞
      (fun q : PolarPoint => C.minusFlow z m q.1 q.2)
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)))
    (href : (C.referenceState, (0 : ℝ)) ∈ U)
    {z : AnnularState S × ℝ} (hz : z ∈ U) (m n b : ℕ)
    {p : PolarPoint} (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    ordinaryFlowFamily S C m (n + 1) b p z =
      iteratedDeriv b (fun θ =>
        ∑ t : (physicalLieExpansion n).Index, ∏ i,
          mixedDerivative ((physicalLieExpansion n).words t i).radialOrder
            ((physicalLieExpansion n).words t i).angularOrder
            (minusCharacteristicSpeed (originalCoefficients D S C z))
            (p.1, C.minusFlow z m p.1 θ)) p.2 -
      iteratedDeriv b (fun θ =>
        ∑ t : (physicalLieExpansion n).Index, ∏ i,
          mixedDerivative ((physicalLieExpansion n).words t i).radialOrder
            ((physicalLieExpansion n).words t i).angularOrder
            (minusCharacteristicSpeed (originalCoefficients D S C (C.referenceState, 0)))
            (p.1, C.minusFlow (C.referenceState, 0) m p.1 θ)) p.2 := by
  rw [ordinaryFlowFamily_eq_physicalLieDifference hFlow hlam hΘ href hz m n b hp]
  apply congrArg₂ (fun u v : ℝ => u - v)
  · apply congrArg (fun F : ℝ → ℝ => iteratedDeriv b F p.2)
    funext θ
    exact physicalFlowLieJet_eq_sum_mixedDerivative (isOpen_Ioo.prod isOpen_univ)
      (hlam z hz m) n ⟨hp, mem_univ _⟩
  · apply congrArg (fun F : ℝ → ℝ => iteratedDeriv b F p.2)
    funext θ
    exact physicalFlowLieJet_eq_sum_mixedDerivative (isOpen_Ioo.prod isOpen_univ)
      (hlam (C.referenceState, 0) href m) n ⟨hp, mem_univ _⟩

end ContinuousFlexibility.Statements
