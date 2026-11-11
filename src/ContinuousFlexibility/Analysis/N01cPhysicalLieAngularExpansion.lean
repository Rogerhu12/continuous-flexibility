import ContinuousFlexibility.Analysis.N01cPhysicalLieExpansion

/-!
# Angular jets of the finite physical Lie expansion

Angular differentiation only hits existing factors. It preserves their
number and their total radial order. The total spatial order is exactly
n+b, which is the budget used before the physical flow graph is inserted.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators Topology

private theorem physicalLieHit_angular_radialOrder
    {n : ℕ} (w : Fin n → PhysicalLieWord) (i l : Fin n) :
    (physicalLieHit w 1 i l).radialOrder = (w l).radialOrder := by
  by_cases h : l = i
  · simp only [physicalLieHit, if_pos h, PhysicalLieWord.radialOrder_prepend,
      if_neg (by decide : (1 : Fin 2) ≠ 0), Nat.zero_add]
  · simp only [physicalLieHit, if_neg h]

private theorem physicalLie_contDiffOn_iteratedAngularPartial
    {Ω : Set PolarPoint} {f : PolarPoint → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) (n : ℕ) :
    ContDiffOn ℝ ∞ ((angularPartial^[n]) f) Ω := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (ih.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const

private theorem physicalLie_mixedDerivative_iteratedAngularPartial
    {Ω : Set PolarPoint} {f : PolarPoint → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (n a b : ℕ) {p : PolarPoint} (hp : p ∈ Ω) :
    mixedDerivative a b ((angularPartial^[n]) f) p =
      mixedDerivative a (b + n) f p := by
  induction n generalizing b with
  | zero => simp only [Function.iterate_zero_apply, Nat.add_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply',
      mixedDerivative_angularPartial hΩ
        (physicalLie_contDiffOn_iteratedAngularPartial hΩ hf n) a b hp]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (b + 1)

/-- Universal data for angular jets of the n-th physical Lie expression. -/
structure PhysicalLieAngularExpansion (n b : ℕ) where
  Index : Type
  [fintype : Fintype Index]
  arity : Index → ℕ
  words : ∀ t, Fin (arity t) → PhysicalLieWord
  arity_pos : ∀ t, 0 < arity t
  arity_le : ∀ t, arity t ≤ n + 1
  total_order : ∀ t, (∑ i, (words t i).order) = n + b
  radial_order_le : ∀ t, (∑ i, (words t i).radialOrder) ≤ n
  formula : ∀ {Ω : Set PolarPoint} {f : PolarPoint → ℝ},
    IsOpen Ω → ContDiffOn ℝ ∞ f Ω → ∀ p ∈ Ω,
      ((angularPartial^[b]) (physicalFlowLieJet f n)) p =
        ∑ t : Index, ∏ i, (words t i).eval f p

attribute [instance] PhysicalLieAngularExpansion.fintype

private def physicalLieAngularExpansion_zero (n : ℕ) :
    PhysicalLieAngularExpansion n 0 where
  Index := (physicalLieExpansion n).Index
  fintype := inferInstance
  arity := (physicalLieExpansion n).arity
  words := (physicalLieExpansion n).words
  arity_pos := (physicalLieExpansion n).arity_pos
  arity_le := (physicalLieExpansion n).arity_le
  total_order := by
    intro t
    simpa only [Nat.add_zero] using (physicalLieExpansion n).total_order t
  radial_order_le := physicalLieExpansion_radial_order_le n
  formula := by
    intro Ω f hΩ hf p hp
    simpa only [Function.iterate_zero_apply] using (physicalLieExpansion n).formula hΩ hf p hp

/-- Angular differentiation never introduces a new speed factor. -/
def PhysicalLieAngularExpansion.step {n b : ℕ}
    (e : PhysicalLieAngularExpansion n b) : PhysicalLieAngularExpansion n (b + 1) where
  Index := Σ t : e.Index, Fin (e.arity t)
  fintype := inferInstance
  arity := fun ti => e.arity ti.1
  words := fun ti => physicalLieHit (e.words ti.1) 1 ti.2
  arity_pos := fun ti => e.arity_pos ti.1
  arity_le := fun ti => e.arity_le ti.1
  total_order := by
    intro ti
    rw [physicalLieHit_total_order, e.total_order]
    omega
  radial_order_le := by
    intro ti
    simpa only [physicalLieHit_angular_radialOrder] using e.radial_order_le ti.1
  formula := by
    intro Ω f hΩ hf p hp
    let F : PolarPoint → ℝ := fun q => ∑ t : e.Index, ∏ i, (e.words t i).eval f q
    have he : ((angularPartial^[b]) (physicalFlowLieJet f n)) =ᶠ[𝓝 p] F := by
      filter_upwards [hΩ.mem_nhds hp] with q hq
      exact e.formula hΩ hf q hq
    rw [Function.iterate_succ_apply']
    change fderiv ℝ ((angularPartial^[b]) (physicalFlowLieJet f n)) p (0, 1) = _
    rw [he.fderiv_eq (𝕜 := ℝ)]
    simpa only [cylinderBasisVector, if_neg (by decide : (1 : Fin 2) ≠ 0)] using
      fderiv_physicalLieSum e.arity e.words hΩ hf 1 hp

def physicalLieAngularExpansion (n : ℕ) : (b : ℕ) → PhysicalLieAngularExpansion n b
  | 0 => physicalLieAngularExpansion_zero n
  | b + 1 => (physicalLieAngularExpansion n b).step

theorem physicalLieAngularExpansion_spatial_order
    (n b : ℕ) (t : (physicalLieAngularExpansion n b).Index) :
    (∑ i, ((physicalLieAngularExpansion n b).words t i).radialOrder +
      ((physicalLieAngularExpansion n b).words t i).angularOrder) = n + b := by
  simp only [PhysicalLieWord.radialOrder_add_angularOrder]
  exact (physicalLieAngularExpansion n b).total_order t

/-- Every actual outer angular jet has the finite order-preserving formula. -/
theorem angularPhysicalFlowLieJet_eq_sum_mixedDerivative
    {Ω : Set PolarPoint} {f : PolarPoint → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) (n b : ℕ)
    {p : PolarPoint} (hp : p ∈ Ω) :
    mixedDerivative 0 b (physicalFlowLieJet f n) p =
      ∑ t : (physicalLieAngularExpansion n b).Index, ∏ i,
        mixedDerivative ((physicalLieAngularExpansion n b).words t i).radialOrder
          ((physicalLieAngularExpansion n b).words t i).angularOrder f p := by
  have hderiv : ((angularPartial^[b]) (physicalFlowLieJet f n)) p =
      mixedDerivative 0 b (physicalFlowLieJet f n) p := by
    simpa only [mixedDerivative, iteratedDeriv_zero, Nat.zero_add] using
      physicalLie_mixedDerivative_iteratedAngularPartial hΩ
        (contDiffOn_physicalFlowLieJet hΩ hf n) b 0 0 hp
  rw [← hderiv, (physicalLieAngularExpansion n b).formula hΩ hf p hp]
  apply Finset.sum_congr rfl
  intro t _
  exact Finset.prod_congr rfl (fun i _ =>
    PhysicalLieWord.eval_eq_mixedDerivative hΩ hf _ hp)

/-- The radial endpoint exponent left after weighting every speed factor
is nonnegative, independently of the angular order. -/
theorem physicalLieAngularExpansion_radial_budget
    (n b : ℕ) (t : (physicalLieAngularExpansion n b).Index) :
    (∑ i, ((physicalLieAngularExpansion n b).words t i).radialOrder) ≤ n + 1 :=
  ((physicalLieAngularExpansion n b).radial_order_le t).trans (by omega)

end ContinuousFlexibility.Analysis
