import ContinuousFlexibility.Scalar.WeightedStateTopology
import ContinuousFlexibility.Scalar.WeightedTowerCalculus

/-!
# Fixed-order bookkeeping for the final scalar operator estimates

These monotonicity facts permit one final enlargement of the common base
and loss. The value bound is read directly from order zero of the actual
uniform derivative tower.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

section Value

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
  {U : Set E} {base loss : ℕ} {f : E → F}

theorem UniformScalarTowerEstimate.value_bound
    {J : SmoothDirections U f} (hJ : UniformScalarTowerEstimate p q U base loss f J)
    (s : ℕ) (hs : base ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, q s (f x) ≤ C * (1 + p (s + loss) x) := by
  obtain ⟨C, hC, hCx⟩ := hJ 0 s hs
  refine ⟨C, hC, fun x hx => ?_⟩
  have h := hCx x hx Fin.elim0
  rw [J.zero x hx] at h
  simpa only [Fin.prod_univ_zero, Fin.sum_univ_zero, mul_one, add_zero] using h

theorem FixedNeighborhoodSmoothTame.value_bound
    (hf : FixedNeighborhoodSmoothTame p q U base loss f)
    (s : ℕ) (hs : base ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, q s (f x) ≤ C * (1 + p (s + loss) x) := by
  obtain ⟨J, hJ⟩ := hf.2
  exact hJ.value_bound s hs

end Value

section Costs

variable {E F G : Type*}
  [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G]
  {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}

theorem weightedLinearFamilyCost_mono
    (hp : Monotone p) (hq : Monotone q)
    {base base' loss loss' s : ℕ} (hb : base ≤ base') (hl : loss ≤ loss')
    (x : E) (u : F) :
    q (s + loss) u + (1 + p (s + loss) x) * q base u ≤
      q (s + loss') u + (1 + p (s + loss') x) * q base' u := by
  exact add_le_add (hq (Nat.add_le_add_left hl s) u)
    (mul_le_mul (add_le_add (le_refl 1) (hp (Nat.add_le_add_left hl s) x))
      (hq hb u) (apply_nonneg _ _) (by positivity))

theorem weightedErrorFamilyCost_mono
    (hp : Monotone p) (hq : Monotone q) (hr : Monotone r)
    {base base' loss loss' s : ℕ} (hb : base ≤ base') (hl : loss ≤ loss')
    (x : E) (R : F) (u : G) :
    q (s + loss) R * r base u + q base R * r (s + loss) u +
        (1 + p (s + loss) x) * q base R * r base u ≤
      q (s + loss') R * r base' u + q base' R * r (s + loss') u +
        (1 + p (s + loss') x) * q base' R * r base' u := by
  apply add_le_add
  · exact add_le_add
      (mul_le_mul (hq (Nat.add_le_add_left hl s) R) (hr hb u)
        (apply_nonneg _ _) (apply_nonneg _ _))
      (mul_le_mul (hq hb R) (hr (Nat.add_le_add_left hl s) u)
        (apply_nonneg _ _) (apply_nonneg _ _))
  · exact mul_le_mul
      (mul_le_mul (add_le_add (le_refl 1) (hp (Nat.add_le_add_left hl s) x))
        (hq hb R) (apply_nonneg _ _) (by positivity))
      (hr hb u) (apply_nonneg _ _) (by positivity)

end Costs

end ContinuousFlexibility.Statements
