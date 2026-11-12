import ContinuousFlexibility.Analysis.N01cOrdinaryFlowAngularBounds

/-!
# Transporting the actual angular prefix to arbitrary genuine towers

The source estimate selects one actual mixed-derivative tower before
its state-order quantifier. Uniqueness transports the same estimate to
any genuine angular tower. Choosing the spatial cutoff equal to the
angular order preserves one fixed offset for the whole state prefix.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

private theorem n01c_abs_bound_enlarge_positive_coefficient
    {a B H E W : ℝ} (hB : 0 < B) (hb : |a| ≤ B * H * E * W) :
    |a| ≤ (1 + B) * H * E * W := by
  have hraw : |a| ≤ B * (H * E * W) := by
    simpa only [mul_assoc] using hb
  have hnonneg : 0 ≤ B * (H * E * W) := (abs_nonneg a).trans hraw
  have hW : 0 ≤ H * E * W := by
    by_contra h
    exact (not_lt_of_ge hnonneg)
      (mul_neg_of_pos_of_neg hB (lt_of_not_ge h))
  calc
    |a| ≤ B * (H * E * W) := hraw
    _ ≤ (1 + B) * (H * E * W) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hW
    _ = _ := by ring

/-- A full positive state prefix yields the fixed-order input used by
the physical graph estimate. All existential elimination is performed
on the generic state space. -/
theorem angularPositivePrefix_to_fixedBounds
    {X ι : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    (p : ℕ → Seminorm ℝ X) (center : X) (base loss K : ℕ)
    {U : Set X} (I : ι → Set ℝ) (H E : ι → ℝ)
    (Θ : ι → X → PolarPoint → ℝ)
    (hprefix : ∃ dK : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m b q, b ≤ s → q.1 ∈ I m →
      ∃ J : SmoothDirections U (fun x => mixedDerivative 0 b (Θ m x) q),
      ∀ j : ℕ, j ≤ K → 0 < j → ∀ x ∈ U, ∀ v : Fin j → X,
        |J.D j x v| ≤ B * H m * E m ^ B *
          oneHighVariationWeight p base (s + loss + dK) (x - center) v) :
    ∃ offset : ℕ, ∀ β : ℕ, ∃ Cp Ap : ℝ, 1 ≤ Cp ∧ 0 ≤ Ap ∧
      ∀ m r, r ∈ I m → ∀ θ : ℝ,
      ∀ J : SmoothDirections U
        (fun x => iteratedDeriv β (fun η => Θ m x (r, η)) θ),
      ∀ j : ℕ, j ≤ K → 0 < j → ∀ x ∈ U, ∀ v : Fin j → X,
        |J.D j x v| ≤ Cp * H m * E m ^ Ap *
          oneHighVariationWeight p base (β + offset) (x - center) v := by
  obtain ⟨dK, hprefix⟩ := hprefix
  refine ⟨loss + dK, ?_⟩
  intro β
  obtain ⟨B, hB, hbound⟩ := hprefix β
  refine ⟨1 + B, B, le_add_of_nonneg_right hB.le, hB.le, ?_⟩
  intro m r hr θ J j hj hjpos x hx v
  obtain ⟨J₀, hb⟩ := hbound m β (r, θ) le_rfl hr
  let Ja : SmoothDirections U
      (fun y => iteratedDeriv β (fun η => Θ m y (r, η)) θ) :=
    J₀.congr (fun _ _ => by simp only [mixedDerivative, iteratedDeriv_zero])
  have he : J.D j x v = J₀.D j x v :=
    congrArg (fun A : X [×j]→L[ℝ] ℝ => A v)
      (HasProjectiveJetsOn.unique J.open_domain
        J.hasProjectiveJetsOn Ja.hasProjectiveJetsOn j x hx)
  have hh := n01c_abs_bound_enlarge_positive_coefficient hB (hb j hj hjpos x hx v)
  rw [← he] at hh
  simpa only [Nat.add_assoc] using hh

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

/-- The actual prefix from the angular-flow theorem is passed as one
opaque argument. Its neighbourhood, prefix and material samples remain
unchanged, and the output applies to every genuine angular tower. -/
theorem ordinaryFlowAngularPositivePrefix_to_fixedBounds
    {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss K : ℕ} {ε : ℝ}
    (hprefix : ∃ dK : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m b q, b ≤ s → q.1 ∈ Ioo (C.left m) (C.right m) →
      ∃ J : SmoothDirections (stateNeighborhood S C base ε)
        (fun z => mixedDerivative 0 b (fun t => C.minusFlow z m t.1 t.2) q),
      ∀ j : ℕ, j ≤ K → 0 < j →
      ∀ z ∈ stateNeighborhood S C base ε, ∀ v : Fin j → (AnnularState S × ℝ),
        |J.D j z v| ≤ B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
            base (s + loss + dK) (z - (C.referenceState, 0)) v) :
    ∃ offset : ℕ, ∀ β : ℕ, ∃ Cp Ap : ℝ, 1 ≤ Cp ∧ 0 ≤ Ap ∧
      ∀ m r, r ∈ Ioo (C.left m) (C.right m) → ∀ θ : ℝ,
      ∀ J : SmoothDirections (stateNeighborhood S C base ε)
        (fun z => iteratedDeriv β (fun η => C.minusFlow z m r η) θ),
      ∀ j : ℕ, j ≤ K → 0 < j →
      ∀ z ∈ stateNeighborhood S C base ε, ∀ v : Fin j → (AnnularState S × ℝ),
        |J.D j z v| ≤ Cp * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ Ap *
          oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
            base (β + offset) (z - (C.referenceState, 0)) v :=
  angularPositivePrefix_to_fixedBounds
    (X := AnnularState S × ℝ) (ι := ℕ)
    (pairGrading (stateGrading S) realGrading) (C.referenceState, 0) base loss K
    (U := stateNeighborhood S C base ε)
    (fun m => Ioo (C.left m) (C.right m))
    (fun m => T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ))
    (fun m => T.E0 (T.sample (C.cell m)))
    (fun m z t => C.minusFlow z m t.1 t.2) hprefix

end ContinuousFlexibility.Statements
