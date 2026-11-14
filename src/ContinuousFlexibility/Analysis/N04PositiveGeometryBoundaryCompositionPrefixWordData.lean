import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryComposition
import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryTraceOperations
import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsPlaneJets

/-!
# Uniform finite plane composition bounds

The constants for the four positive spatial orders are selected before
specializing to any atlas. The finite basis argument is likewise carried
out for abstract plane maps, so actual source estimates use one bound
field without rewriting a dependent composition certificate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

structure N04PlaneCompositionPrefixWordData
    (X : Type*) [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    (N : ℕ) where
  C : ℝ
  one_le_C : 1 ≤ C
  bound :
    ∀ {U : Set X}, IsOpen U →
    ∀ (f g : X × ℝ → PolarPoint → PolarPoint) (q : X × ℝ → PolarPoint),
    (∀ y ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (f y) (g y (q y))) →
    (∀ y ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (g y) (q y)) →
    ∀ n : ℕ, 1 ≤ n → n ≤ 4 →
    ∀ JF : ∀ j, 1 ≤ j → j ≤ n →
      SmoothDirections (U ×ˢ univ)
        (fun y => iteratedFDeriv ℝ j (f y) (g y (q y))),
    ∀ JG : ∀ j, 1 ≤ j → j ≤ n → ∀ v : Fin j → PolarPoint,
      SmoothDirections (U ×ˢ univ)
        (fun y => iteratedFDeriv ℝ j (g y) (q y) v),
    ∀ Q : SmoothDirections (U ×ˢ univ)
      (fun y => iteratedFDeriv ℝ n (f y ∘ g y) (q y)),
    ∀ K s d : ℕ, K + s + d ≤ N → ∀ x ∈ U, ∀ θ P,
    ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ M → 1 ≤ t → ∀ shift,
    (∀ j hj hjn, N04BoundaryWordBounds (JF j hj hjn) K s d x θ P M H t shift) →
    (∀ j hj hjn v, (∀ a, ‖v a‖ ≤ 1) →
      N04BoundaryWordBounds (JG j hj hjn v) K s d x θ P M H t shift) →
    N04BoundaryWordBounds Q K s d x θ P (16 * C * M ^ (5 + 2 * N)) H t shift

def n04PositiveGeometry_planeCompositionPrefixWordData
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    (N : ℕ) : N04PlaneCompositionPrefixWordData X N :=
  Classical.choice (by
    choose c hc hcompositionData using fun j : Fin 4 =>
      n04PositiveGeometry_boundaryComposition_bound (X := X)
        (E := PolarPoint) (F := PolarPoint) (G := PolarPoint)
        N (j.val + 1) (Nat.zero_lt_succ j.val)
    let C : ℝ := 1 + ∑ j : Fin 4, c j
    have hC : 1 ≤ C := le_add_of_nonneg_right
      (Finset.sum_nonneg fun j _ => zero_le_one.trans (hc j))
    have hcC (j : Fin 4) : c j ≤ C :=
      (Finset.single_le_sum (fun j _ => zero_le_one.trans (hc j))
        (Finset.mem_univ j)).trans (le_add_of_nonneg_left zero_le_one)
    refine ⟨⟨C, hC, ?_⟩⟩
    intro U hU f g q hf hg n hn hn4 JF JG Q K s d hN x hx θ P
      M H t hM hH hHM ht shift hJF hJG
    let j₄ : Fin 4 := ⟨n - 1, by omega⟩
    have hj₄ : j₄.val + 1 = n := Nat.sub_add_cancel hn
    have hcomposition := hcompositionData j₄ (U := U)
    rw [hj₄] at hcomposition
    let JE (w : Fin n → Fin 2) :=
      n04PositiveGeometry_boundaryFixedEvaluation_directions Q
        (fun a => cylinderBasisVector (w a))
    have hunit (a : Fin 2) : ‖cylinderBasisVector a‖ ≤ 1 := by
      fin_cases a <;> norm_num [cylinderBasisVector, Prod.norm_def]
    have hJE (w : Fin n → Fin 2) :
        N04BoundaryWordBounds (JE w) K s d x θ P (C * M ^ (5 + 2 * N)) H t shift := by
      have hb := hcomposition hU f g q hf hg JF JG K s d hN x hx θ P
        M H t hM hH hHM ht shift hJF hJG
        (fun a => cylinderBasisVector (w a)) (fun a => hunit (w a)) (JE w)
      have hcost : c j₄ * M ^ (n + 1 + 2 * N) ≤ C * M ^ (5 + 2 * N) :=
        mul_le_mul (hcC j₄) (pow_le_pow_right₀ hM (by omega))
          (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hC)
      exact hb.enlarge hH (zero_le_one.trans ht) hcost
    have hout := N04BoundaryWordBounds.of_planeBasis Q JE hx
      (mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans hM) _))
      hH (zero_le_one.trans ht) hJE
    apply hout.enlarge hH (zero_le_one.trans ht)
    have htwo : (2 : ℝ) ^ n ≤ 16 :=
      (pow_le_pow_right₀ (by norm_num) hn4).trans_eq (by norm_num)
    calc
      (2 : ℝ) ^ n * (C * M ^ (5 + 2 * N)) ≤ 16 * (C * M ^ (5 + 2 * N)) :=
        mul_le_mul_of_nonneg_right htwo
          (mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans hM) _))
      _ = 16 * C * M ^ (5 + 2 * N) := by rw [mul_assoc])

end ContinuousFlexibility.Analysis
