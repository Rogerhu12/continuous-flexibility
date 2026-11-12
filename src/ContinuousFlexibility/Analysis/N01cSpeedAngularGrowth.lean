import ContinuousFlexibility.Analysis.N01cSpeedLowBounds

/-!
# Actual angular speed growth on the original common neighbourhood

The zero parameter jet is evaluated at its genuine value. The complete
material weight is bounded on the radial core, so a spatial order changes
only the constant and the high grading index, never the common base.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem mixedFamily_zero_angular_growth
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    (p : ℕ → Seminorm ℝ X) (center : X) (U : Set X) (base loss : ℕ)
    (F : ℕ → ℕ → PolarPoint → X → ℝ) (left right : ℕ → ℝ)
    (weight : ℝ → ℕ → ℝ)
    (hweight : ∀ B : ℝ, 0 < B → ∃ M : ℝ, 0 < M ∧ ∀ m, weight B m ≤ M)
    (hbound : ∀ k : ℕ, ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m a b q, a + b ≤ s → q.1 ∈ Ioo (left m) (right m) →
        ∃ J : SmoothDirections U (F a b q),
          ∀ x ∈ U, ∀ v : Fin k → X,
            min (q.1 - left m) (right m - q.1) ^ a * |J.D k x v| ≤
              weight B m * oneHighVariationWeight p base (s + loss + d)
                (x - center) v) :
    ∃ d : ℕ, ∀ s : ℕ, ∃ M : ℝ, 0 < M ∧ ∀ x ∈ U, ∀ m b q,
      b ≤ s → q.1 ∈ Ioo (left m) (right m) →
        |F 0 b q x| ≤ M * (1 + p (s + loss + d) (x - center)) := by
  obtain ⟨d, hd⟩ := hbound 0
  refine ⟨d, ?_⟩
  intro s
  obtain ⟨B, hB, hb⟩ := hd s
  obtain ⟨M, hM, hw⟩ := hweight B hB
  refine ⟨M, hM, ?_⟩
  intro x hx m b q hbq hq
  obtain ⟨J, hJ⟩ := hb m 0 b q (by simpa only [zero_add] using hbq) hq
  have h := hJ x hx Fin.elim0
  rw [J.zero x hx] at h
  have hzero : oneHighVariationWeight p base (s + loss + d)
      (x - center) (Fin.elim0 : Fin 0 → X) =
        1 + p (s + loss + d) (x - center) := by
    simp [oneHighVariationWeight]
  simp only [pow_zero, one_mul, hzero] at h
  exact h.trans (mul_le_mul_of_nonneg_right (hw m)
    (add_nonneg zero_le_one (apply_nonneg _ _)))

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Blueprint

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true in
/-- All spatial orders retain the original common neighbourhood. The
single loss below is the speed estimate's parameter-order-zero loss. -/
theorem n01_speedDifference_angular_growth
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (hSpeed : CharacteristicSpeedTameBounds D T S C base loss ε) :
    ∃ d : ℕ, ∀ s : ℕ, ∃ M : ℝ, 0 < M ∧
      ∀ z ∈ stateNeighborhood S C base ε, ∀ m b q,
        b ≤ s → q.1 ∈ Ioo (C.left m) (C.right m) →
          |characteristicSpeedFamily D S C 0 b q z| ≤
            M * (1 + pairGrading (stateGrading S) realGrading
              (s + loss + d) (z - (C.referenceState, 0))) := by
  exact mixedFamily_zero_angular_growth
    (pairGrading (stateGrading S) realGrading) (C.referenceState, 0)
    (stateNeighborhood S C base ε) base loss
    (characteristicSpeedFamily D S C) C.left C.right
    (fun B m => B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
      T.E0 (T.sample (C.cell m)) ^ B)
    (fun B hB => by
      obtain ⟨M, hM, hw⟩ :=
        materialHeight_E0_weight_bounded hT (γ := (3 / 4 : ℝ)) (by norm_num) B
      refine ⟨B * M, mul_pos hB hM, ?_⟩
      intro m
      have hs := materialSample_mem_radialCore hT hRef.choose_spec.2.1 (C.cell m)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hw _ hs) hB.le)
    hSpeed.2

end ContinuousFlexibility.Blueprint
