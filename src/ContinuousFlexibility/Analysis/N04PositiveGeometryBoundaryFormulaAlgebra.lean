import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryFormulaWordBounds
import ContinuousFlexibility.Analysis.N06RootBoundaryFiniteFormulas

/-!
# The actual finite boundary differential expressions

The syntax below evaluates to the eight existing formulas. Its genuine
joint tower is built by scalar addition, multiplication and actual
angular differentiation. A finite reserve of three angular derivatives
then proves a polynomial material cost for every original joint word.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

inductive N04BoundaryExpression where
  | input (i : Fin 9)
  | add (f g : N04BoundaryExpression)
  | scale (a : ℝ) (f : N04BoundaryExpression)
  | mul (f g : N04BoundaryExpression)
  | angle (f : N04BoundaryExpression)

namespace N04BoundaryExpression

def depth : N04BoundaryExpression → ℕ
  | .input _ => 0
  | .add f g => max f.depth g.depth
  | .scale _ f => f.depth
  | .mul f g => max f.depth g.depth
  | .angle f => f.depth + 1

def eval (v : N06RootBoundaryInputs) : N04BoundaryExpression → ℝ → ℝ
  | .input i => v i
  | .add f g => fun θ => f.eval v θ + g.eval v θ
  | .scale a f => fun θ => a * f.eval v θ
  | .mul f g => fun θ => f.eval v θ * g.eval v θ
  | .angle f => deriv (f.eval v)

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {v : Fin 9 → E × ℝ → ℝ}

def directions (J : ∀ i, SmoothDirections (U ×ˢ (univ : Set ℝ)) (v i)) :
    (e : N04BoundaryExpression) → SmoothDirections (U ×ˢ univ)
      (fun z => e.eval (fun i θ => v i (z.1, θ)) z.2)
  | .input i => J i
  | .add f g => smoothDirectionsAdd (f.directions J) (g.directions J)
  | .scale a f => smoothDirections_postcompCLM (f.directions J)
      (a • ContinuousLinearMap.id ℝ ℝ)
  | .mul f g => (f.directions J).mul (g.directions J)
  | .angle f => (smoothDirections_angularIterate (f.directions J) 1).congr
      (fun _ _ => by simp only [iteratedDeriv_one]; rfl)

private theorem polynomial_combine {Cf Cg M : ℝ} {df dg : ℕ}
    (hf : 1 ≤ Cf) (hg : 1 ≤ Cg) (hM : 1 ≤ M) :
    1 ≤ (Cf + Cg) * M ^ (df + dg) ∧
    Cf * M ^ df ≤ (Cf + Cg) * M ^ (df + dg) ∧
    Cg * M ^ dg ≤ (Cf + Cg) * M ^ (df + dg) := by
  have hC : 1 ≤ Cf + Cg := by linarith
  exact ⟨one_le_mul hC (one_le_pow₀ hM),
    mul_le_mul (le_add_of_nonneg_right (zero_le_one.trans hg))
      (pow_le_pow_right₀ hM (Nat.le_add_right _ _))
      (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hC),
    mul_le_mul (le_add_of_nonneg_left (zero_le_one.trans hf))
      (pow_le_pow_right₀ hM (Nat.le_add_left _ _))
      (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hC)⟩

/-- The original parameter arity and the remaining spatial exponent
survive every operation in a fixed finite boundary expression. -/
theorem polynomial_bound (e : N04BoundaryExpression) (K s d : ℕ)
    (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ degree : ℕ,
      ∀ {U : Set E}, Convex ℝ U →
      ∀ {v : Fin 9 → E × ℝ → ℝ},
      ∀ J : ∀ i, SmoothDirections (U ×ˢ univ) (v i),
      ∀ x ∈ U, ∀ θ (P : E → Prop), P 0 →
      ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ L → 1 ≤ t → ∀ shift,
      (∀ i, N04BoundaryWordBounds (J i) K s (d + e.depth) x θ P M H t shift) →
      N04BoundaryWordBounds (e.directions J) K s d x θ P
        (C * M ^ degree) H t shift := by
  induction e generalizing d with
  | input i =>
      refine ⟨1, le_rfl, 1, ?_⟩
      intro U hU v J x hx θ P hP M H t hM hH hHL ht shift hv
      simpa only [depth, Nat.add_zero, directions, pow_one, one_mul] using hv i
  | scale a f ih =>
      obtain ⟨C, hC, degree, hb⟩ := ih d
      refine ⟨1 + |a| * C, le_add_of_nonneg_right
        (mul_nonneg (abs_nonneg _) (zero_le_one.trans hC)), degree, ?_⟩
      intro U hU v J x hx θ P hP M H t hM hH hHL ht shift hv
      have hf := hb hU J x hx θ P hP M H t hM hH hHL ht shift hv
      have hs := hf.scale a
      apply hs.enlarge hH (zero_le_one.trans ht)
      have hp : 0 ≤ M ^ degree := pow_nonneg (zero_le_one.trans hM) _
      nlinarith only [hp]
  | add f g ihf ihg =>
      obtain ⟨Cf, hCf, df, hfb⟩ := ihf d
      obtain ⟨Cg, hCg, dg, hgb⟩ := ihg d
      have hC : 1 ≤ 2 * (Cf + Cg) := by linarith
      refine ⟨2 * (Cf + Cg), hC, df + dg, ?_⟩
      intro U hU v J x hx θ P hP M H t hM hH hHL ht shift hv
      have hfi := hfb hU J x hx θ P hP M H t hM hH hHL ht shift
        (fun i => (hv i).reserve (zero_le_one.trans hM) hH ht (by
          dsimp only [depth]
          exact Nat.add_le_add_left (le_max_left _ _) d))
      have hgi := hgb hU J x hx θ P hP M H t hM hH hHL ht shift
        (fun i => (hv i).reserve (zero_le_one.trans hM) hH ht (by
          dsimp only [depth]
          exact Nat.add_le_add_left (le_max_right _ _) d))
      have hc := polynomial_combine (df := df) (dg := dg) hCf hCg hM
      have hf := hfi.enlarge hH (zero_le_one.trans ht) hc.2.1
      have hg := hgi.enlarge hH (zero_le_one.trans ht) hc.2.2
      have ha := hf.add hg
      convert ha using 1 <;> ring
  | mul f g ihf ihg =>
      obtain ⟨Cf, hCf, df, hfb⟩ := ihf d
      obtain ⟨Cg, hCg, dg, hgb⟩ := ihg d
      obtain ⟨Cp, hCp, hpb⟩ := n04PositiveGeometry_boundaryWord_mul (E := E)
        (K + s + d) L hL
      have hCg' : 1 ≤ Cf + Cg := by linarith
      refine ⟨Cp * (Cf + Cg) ^ (K + s + d + 2),
        one_le_mul hCp (one_le_pow₀ hCg'), (df + dg) * (K + s + d + 2), ?_⟩
      intro U hU v J x hx θ P hP M H t hM hH hHL ht shift hv
      have hfi := hfb hU J x hx θ P hP M H t hM hH hHL ht shift
        (fun i => (hv i).reserve (zero_le_one.trans hM) hH ht (by
          dsimp only [depth]
          exact Nat.add_le_add_left (le_max_left _ _) d))
      have hgi := hgb hU J x hx θ P hP M H t hM hH hHL ht shift
        (fun i => (hv i).reserve (zero_le_one.trans hM) hH ht (by
          dsimp only [depth]
          exact Nat.add_le_add_left (le_max_right _ _) d))
      have hc := polynomial_combine (df := df) (dg := dg) hCf hCg hM
      have hf := hfi.enlarge hH (zero_le_one.trans ht) hc.2.1
      have hg := hgi.enlarge hH (zero_le_one.trans ht) hc.2.2
      have hp := hpb (f.directions J) (g.directions J) K s d le_rfl x hx θ P
        ((Cf + Cg) * M ^ (df + dg)) H t hc.1 hH hHL ht shift hf hg
      simpa only [directions, mul_pow, ← pow_mul, mul_assoc] using hp
  | angle f ih =>
      obtain ⟨C, hC, degree, hb⟩ := ih (d + 1)
      refine ⟨C, hC, degree, ?_⟩
      intro U hU v J x hx θ P hP M H t hM hH hHL ht shift hv
      have hf := hb hU J x hx θ P hP M H t hM hH hHL ht shift
        (fun i => by
          simpa only [depth, show d + (f.depth + 1) = (d + 1) + f.depth by omega]
            using hv i)
      exact hf.angular hx hU hP

end N04BoundaryExpression

open N04BoundaryExpression in
def n04PositiveGeometry_boundaryExpressions : Fin 8 → N04BoundaryExpression :=
  let e1 := scale (-1) (mul (input 0) (input 8))
  let o0 := mul (scale (2 / 3) (input 4)) (input 8)
  let e2 := scale (-1) (add (mul (input 0) (angle e1)) (mul (input 1) (input 8)))
  let o1 := scale (2 / 5) (add (add (mul (input 4) (angle e1))
    (mul (input 5) (input 8))) (scale (-1) (mul (input 0) (angle o0))))
  let e3 := add (scale (-1) (add (add (mul (input 0) (angle e2))
    (mul (scale 2 (input 1)) (angle e1))) (mul (input 2) (input 8))))
    (mul (scale 2 (input 4)) (angle o0))
  let o2 := scale (2 / 7) (add (add (add (mul (input 4) (angle e2))
    (mul (scale 2 (input 5)) (angle e1))) (mul (input 6) (input 8)))
    (scale (-2) (add (mul (input 0) (angle o1)) (mul (input 1) (angle o0)))))
  let e4 := add (scale (-1) (add (add (add (mul (input 0) (angle e3))
    (mul (scale 3 (input 1)) (angle e2))) (mul (scale 3 (input 2)) (angle e1)))
    (mul (input 3) (input 8))))
    (scale 6 (add (mul (input 4) (angle o1)) (mul (input 5) (angle o0))))
  let o3 := scale (2 / 9) (add (add (add (add (mul (input 4) (angle e3))
    (mul (scale 3 (input 5)) (angle e2))) (mul (scale 3 (input 6)) (angle e1)))
    (mul (input 7) (input 8)))
    (scale (-3) (add (add (mul (input 0) (angle o2))
      (mul (scale 2 (input 1)) (angle o1))) (mul (input 2) (angle o0)))))
  ![e1, e2, e3, e4, o0, o1, o2, o3]

def n04PositiveGeometry_boundaryFormula (i : Fin 8) (v : N06RootBoundaryInputs) : ℝ → ℝ :=
  ![n06RootEvenFormula1 v, n06RootEvenFormula2 v, n06RootEvenFormula3 v,
    n06RootEvenFormula4 v, n06RootOddFormula0 v, n06RootOddFormula1 v,
    n06RootOddFormula2 v, n06RootOddFormula3 v] i

theorem n04PositiveGeometry_boundaryExpression_depth (i : Fin 8) :
    (n04PositiveGeometry_boundaryExpressions i).depth ≤ 3 := by
  fin_cases i <;> norm_num [n04PositiveGeometry_boundaryExpressions,
    N04BoundaryExpression.depth]

theorem n04PositiveGeometry_boundaryExpression_eval
    (i : Fin 8) (v : N06RootBoundaryInputs) :
    (n04PositiveGeometry_boundaryExpressions i).eval v =
      n04PositiveGeometry_boundaryFormula i v := by
  fin_cases i <;>
    simp [n04PositiveGeometry_boundaryExpressions, n04PositiveGeometry_boundaryFormula,
      N04BoundaryExpression.eval,
      n06RootEvenFormula1, n06RootEvenFormula2, n06RootEvenFormula3, n06RootEvenFormula4,
      n06RootOddFormula0, n06RootOddFormula1, n06RootOddFormula2, n06RootOddFormula3,
      neg_one_mul, sub_eq_add_neg, neg_mul, one_mul]

end ContinuousFlexibility.Analysis
