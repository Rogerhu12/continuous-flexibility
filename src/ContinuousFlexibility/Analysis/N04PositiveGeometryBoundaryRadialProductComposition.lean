module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryRadialComposition

/-! # Finite word bounds for a radial product with an actual composition -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem n04PositiveGeometry_radialProductComposition_bound (n N : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {U : Set E}, IsOpen U → ∀ c : ℝ,
      ∀ (f h : E × ℝ → PolarPoint → ℝ) (g : E × ℝ → PolarPoint → PolarPoint),
      (∀ y ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (f y) (c, y.2)) →
      (∀ y ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (h y) (g y (c, y.2))) →
      (∀ y ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (g y) (c, y.2)) →
      ∀ JF : ∀ j, j ≤ n → SmoothDirections (U ×ˢ univ)
        (fun y => radialBoundaryJet (f y) c j y.2),
      ∀ JH : ∀ j, j ≤ n → SmoothDirections (U ×ˢ univ)
        (fun y => iteratedFDeriv ℝ j (h y) (g y (c, y.2))),
      ∀ JG : ∀ j, 1 ≤ j → j ≤ n → ∀ v : Fin j → PolarPoint,
        SmoothDirections (U ×ˢ univ)
          (fun y => iteratedFDeriv ℝ j (g y) (c, y.2) v),
      ∀ Q : SmoothDirections (U ×ˢ univ)
        (fun y => radialBoundaryJet (fun p => f y p * h y (g y p)) c n y.2),
      ∀ K s d, K + s + d ≤ N → ∀ x ∈ U, ∀ θ P,
      ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ M → H ≤ L → 1 ≤ t → ∀ shift,
      (∀ j hj, N04BoundaryWordBounds (JF j hj) K s d x θ P M H t shift) →
      (∀ j hj, N04BoundaryWordBounds (JH j hj) K s d x θ P M H t shift) →
      (∀ j hj hjn v, (∀ a, ‖v a‖ ≤ 1) →
        N04BoundaryWordBounds (JG j hj hjn v) K s d x θ P M H t shift) →
      N04BoundaryWordBounds Q K s d x θ P
        (C * M ^ ((n + 1 + 2 * N) * (N + 2))) H t shift := by
  classical
  let compositionData (j : Fin (n + 1)) :=
    n04PositiveGeometry_boundaryRadialComposition_bound (E := E) j.val N
  let B : Fin (n + 1) → ℝ := fun j => (compositionData j).choose
  have hB (j : Fin (n + 1)) : 1 ≤ B j := (compositionData j).choose_spec.1
  let B₀ : ℝ := 1 + ∑ j, B j
  have hB₀ : 1 ≤ B₀ := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun j _ => zero_le_one.trans (hB j)))
  have hBB (j : Fin (n + 1)) : B j ≤ B₀ :=
    (Finset.single_le_sum (fun j _ => zero_le_one.trans (hB j)) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_left zero_le_one)
  obtain ⟨A, hA, hproduct⟩ := n04PositiveGeometry_radialProduct_bound (E := E) n N L hL
  refine ⟨A * B₀ ^ (N + 2), one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hB₀), ?_⟩
  intro U hU c f h g hf hh hg JF JH JG Q K s d hN x hx θ P M H t hM hH hHM hHL ht shift hF hHj hG
  let D := n + 1 + 2 * N
  let M₁ := B₀ * M ^ D
  have hM₁ : 1 ≤ M₁ := one_le_mul_of_one_le_of_one_le hB₀ (one_le_pow₀ hM)
  have hMM : M ≤ M₁ := calc
    M ≤ M ^ D := by
      simpa only [pow_one] using pow_le_pow_right₀ hM (show 1 ≤ D by dsimp only [D]; omega)
    _ ≤ B₀ * M ^ D := le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans hM) _) hB₀
  let JC (j : ℕ) (hj : j ≤ n) :=
    n04PositiveGeometry_boundaryRadialComposition_directions hU c j h g hh hg
      (fun l hl => JH l (hl.trans hj)) (fun l hl hlj => JG l hl (hlj.trans hj))
  have hCj (j : ℕ) (hj : j ≤ n) :
      N04BoundaryWordBounds (JC j hj) K s d x θ P M₁ H t shift := by
    let q : Fin (n + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    have hbound := (compositionData q).choose_spec.2 hU c h g hh hg
      (fun l hl => JH l (hl.trans hj)) (fun l hl hlj => JG l hl (hlj.trans hj)) (JC j hj)
      K s d hN x hx θ P M H t hM hH hHM ht shift
      (fun l hl => hHj l (hl.trans hj)) (fun l hl hlj v hv => hG l hl (hlj.trans hj) v hv)
    apply hbound.enlarge hH (zero_le_one.trans ht)
    exact mul_le_mul (hBB q) (pow_le_pow_right₀ hM (by dsimp only [q, D]; omega))
      (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hB₀)
  have hbound := hproduct hU c f (fun y => h y ∘ g y) hf
    (fun y hy => (hh y hy).comp _ (hg y hy)) JF JC Q
    K s d hN x hx θ P M₁ H t hM₁ hH hHL ht shift
    (fun j hj => (hF j hj).enlarge hH (zero_le_one.trans ht) hMM) hCj
  have hcost : A * M₁ ^ (N + 2) = (A * B₀ ^ (N + 2)) * M ^ (D * (N + 2)) := by
    dsimp only [M₁]
    rw [mul_pow, ← pow_mul]
    ring
  exact hbound.enlarge hH (zero_le_one.trans ht) hcost.le

end ContinuousFlexibility.Analysis
