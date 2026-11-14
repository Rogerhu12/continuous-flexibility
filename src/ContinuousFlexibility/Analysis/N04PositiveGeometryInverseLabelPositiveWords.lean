module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryMoving
public import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryFormulaPrefix
public import ContinuousFlexibility.Analysis.N01cMixedPowerNormalization

/-!
# Positive words of an unwrapped inverse label

Words with an angular slot are derivatives of the actual slope. Pure
state words of positive order are derivatives of the displacement.
Thus no bound for the value of the unwrapped angle is introduced.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem n04PositiveGeometry_inverseLabel_positive_words
    {U : Set E} {α : E × ℝ → ℝ}
    (Jα : SmoothDirections (U ×ˢ univ) α)
    (Jb : SmoothDirections (U ×ˢ univ)
      (fun y => deriv (fun η => α (y.1, η)) y.2))
    (K s : ℕ) (x : E) (hx : x ∈ U) (θ : ℝ) (P : E → Prop)
    (Jδ : SmoothDirections U (fun y => α (y, θ) - θ))
    (M H t : ℝ) (shift : ℕ)
    (hδ : ∀ k : ℕ, 0 < k → k ≤ K → ∀ v : Fin k → E,
      (∀ i, P (v i)) → ‖Jδ.D k x v‖ ≤
        M * parameterHeightWeight H k * t ^ (shift * k))
    (hb : ∀ k : ℕ, k ≤ K → ∀ u : ℕ, u ≤ s → ∀ v : Fin k → E,
      (∀ i, P (v i)) →
      ‖(smoothDirections_angularStateSlice Jb u θ).D k x v‖ ≤
        M * parameterHeightWeight H k * t ^ (u + shift * k)) :
    N04BoundaryPositiveWordBounds Jα K s 1 x θ P M H t shift := by
  intro n hn w hk ha v hv hp
  let u := w.stateDirections v
  have hu (i : Fin w.stateArity) : P (u i) := by
    obtain ⟨j, hj, he⟩ := w.stateDirections_mem_range v i
    change P (w.stateDirections v i)
    rw [he]
    exact hp j
  have he := smoothDirections_joint_pureSlots Jα
    (smoothDirections_angularStateSlice Jα) w hx θ u
  rw [w.pureSlots_stateDirections v hv] at he
  by_cases hz : w.angleArity = 0
  · have hkpos : 0 < w.stateArity := by have hs := w.arity_sum; omega
    rw [hz] at he
    have hd := smoothDirections_D_sub_constant (smoothDirections_stateSlice Jα θ)
      Jδ hkpos hx u
    have he' : Jα.D n (x, θ) v = Jδ.D w.stateArity x u := he.trans hd.symm
    simpa only [hz, Nat.zero_sub, Nat.zero_add] using
      (congrArg norm he').trans_le (hδ _ hkpos hk u hu)
  · have hpos : 0 < w.angleArity := Nat.pos_of_ne_zero hz
    have hfun (y : E) :
        iteratedDeriv w.angleArity (fun η => α (y, η)) θ =
          iteratedDeriv (w.angleArity - 1) (fun η => deriv (fun ν => α (y, ν)) η) θ := by
      have hs : w.angleArity = (w.angleArity - 1) + 1 := by omega
      conv_lhs => rw [hs, iteratedDeriv_succ']
    let JA := (smoothDirections_angularStateSlice Jα w.angleArity θ).congr
      (fun y _ => hfun y)
    have hsame := congrArg (fun A : E [×w.stateArity]→L[ℝ] ℝ => A u)
      (JA.unique (smoothDirections_angularStateSlice Jb (w.angleArity - 1) θ)
        w.stateArity x hx)
    have he' : Jα.D n (x, θ) v =
        (smoothDirections_angularStateSlice Jb (w.angleArity - 1) θ).D
          w.stateArity x u := he.trans hsame
    exact (congrArg norm he').trans_le (hb _ hk _ (by omega) u hu)

end ContinuousFlexibility.Analysis
