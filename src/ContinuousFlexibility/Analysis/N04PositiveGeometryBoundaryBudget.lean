module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryMoving

/-! # Changing a boundary word budget with a common normalized power -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Set E} {f : E × ℝ → F} {J : SmoothDirections (U ×ˢ univ) f}
  {K K' s s' d : ℕ} {x : E} {θ : ℝ} {P P' : E → Prop}
  {M M' H t t' : ℝ} {c c' : ℕ}

private theorem boundary_budget_scalar
    (hM : 0 ≤ M') (hH : 0 ≤ H) (ht : 1 ≤ t') (hMM : M ≤ M')
    (htt : t = t') (hcc : c ≤ c') (k b : ℕ) :
    M * parameterHeightWeight H k * t ^ (b + c * k) ≤
      M' * parameterHeightWeight H k * t' ^ (b + c' * k) := by
  rw [htt]
  exact mul_le_mul (mul_le_mul_of_nonneg_right hMM (parameterHeightWeight_nonneg hH k))
    (pow_le_pow_right₀ ht (Nat.add_le_add_left (Nat.mul_le_mul_right k hcc) b))
    (pow_nonneg (zero_le_one.trans ht) _) (mul_nonneg hM (parameterHeightWeight_nonneg hH k))

theorem N04BoundaryWordBounds.mono_budget
    (h : N04BoundaryWordBounds J K s d x θ P M H t c)
    (hK : K' ≤ K) (hs : s' ≤ s) (hP : ∀ v, P' v → P v)
    (hM : 0 ≤ M') (hH : 0 ≤ H) (ht : 1 ≤ t') (hMM : M ≤ M')
    (htt : t = t') (hcc : c ≤ c') :
    N04BoundaryWordBounds J K' s' d x θ P' M' H t' c' := by
  intro n w hk ha v hv hp
  exact (h n w (hk.trans hK) (ha.trans (Nat.add_le_add_right hs d)) v hv
    (fun i => hP _ (hp i))).trans
      (boundary_budget_scalar hM hH ht hMM htt hcc w.stateArity (w.angleArity - d))

theorem N04BoundaryPositiveWordBounds.mono_budget
    (h : N04BoundaryPositiveWordBounds J K s d x θ P M H t c)
    (hK : K' ≤ K) (hs : s' ≤ s) (hP : ∀ v, P' v → P v)
    (hM : 0 ≤ M') (hH : 0 ≤ H) (ht : 1 ≤ t') (hMM : M ≤ M')
    (htt : t = t') (hcc : c ≤ c') :
    N04BoundaryPositiveWordBounds J K' s' d x θ P' M' H t' c' := by
  intro n hn w hk ha v hv hp
  exact (h n hn w (hk.trans hK) (ha.trans (Nat.add_le_add_right hs d)) v hv
    (fun i => hP _ (hp i))).trans
      (boundary_budget_scalar hM hH ht hMM htt hcc w.stateArity (w.angleArity - d))

end ContinuousFlexibility.Analysis
