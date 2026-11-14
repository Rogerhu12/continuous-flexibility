module

public import ContinuousFlexibility.Analysis.N01cFlowOrderConstants
public import ContinuousFlexibility.Analysis.StateNeighborhood
public import ContinuousFlexibility.Scalar.WeightedTowerCalculus

/-!
# Finite collection of actual scalar jet towers

The spatial evaluation indices use the existing product topology. Their
genuine scalar towers assemble by the existing Pi constructor. Only the
finite outer family is used to choose common losses and constants; the
open parameter domain and low grading order are unchanged.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

section ScalarTowers

variable {X I P : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  {U : Set X} {f : X → I → ℕ → ℕ → ℕ → P → ℝ}

/-- The existing Pi assembler applied to the five actual jet indices. -/
def n04Realization_scalarJetTower (hU : IsOpen U)
    (J : ∀ a m i j q, SmoothDirections U (fun x => f x a m i j q)) :
    SmoothDirections U f :=
  smoothDirectionsScalarPi hU (fun a =>
    smoothDirectionsScalarPi hU (fun m =>
      smoothDirectionsScalarPi hU (fun i =>
        smoothDirectionsScalarPi hU (fun j =>
          smoothDirectionsScalarPi hU (fun q => J a m i j q)))))

theorem n04Realization_scalarJetTower_D_apply (hU : IsOpen U)
    (J : ∀ a m i j q, SmoothDirections U (fun x => f x a m i j q))
    (k : ℕ) (x : X) (v : Fin k → X) (a : I) (m i j : ℕ) (q : P) :
    (n04Realization_scalarJetTower hU J).D k x v a m i j q =
      (J a m i j q).D k x v := by
  simp only [n04Realization_scalarJetTower, smoothDirectionsScalarPi,
    ContinuousMultilinearMap.pi_apply]

end ScalarTowers

private theorem n04Realization_weightedCoefficient_mono
    {A B E H W V : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    (hE : 1 ≤ E) (hH : 0 ≤ H) (hW : 0 ≤ W) (hWV : W ≤ V) :
    A * E ^ A * H * W ≤ B * E ^ B * H * V := by
  have hE0 : 0 ≤ E := zero_le_one.trans hE
  have hB : 0 ≤ B := hA.le.trans hAB
  have hcost : A * E ^ A ≤ B * E ^ B :=
    mul_le_mul hAB (Real.rpow_le_rpow_of_exponent_le hE hAB)
      (Real.rpow_nonneg hE0 A) hB
  exact mul_le_mul (mul_le_mul_of_nonneg_right hcost hH) hWV hW
    (mul_nonneg (mul_nonneg hB (Real.rpow_nonneg hE0 B)) hH)

/-- Collect a finite family on one fixed open set. The value loss is
selected before the spatial order; each parameter-order loss is selected
before its spatial order. The assembled tower is selected before every
parameter order and differentiates the supplied full function. -/
theorem n04Realization_collect_scalarJet_bounds
    {X I P : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [Fintype I] {U : Set X} (hU : IsOpen U)
    (f : X → I → ℕ → ℕ → ℕ → P → ℝ)
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (base : ℕ)
    (E H : ℕ → ℝ) (hE : ∀ m, 1 ≤ E m) (hH : ∀ m, 0 ≤ H m)
    (J : ∀ a m i j q, SmoothDirections U (fun x => f x a m i j q))
    (hvalue : ∀ a, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ x ∈ U, ∀ m q i j, i + j ≤ s →
        |f x a m i j q| ≤ B * E m ^ B * H m * p (s + loss) x)
    (hparameter : ∀ a k, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ x ∈ U, ∀ v : Fin k → X, ∀ m q i j, i + j ≤ s →
        |(J a m i j q).D k x v| ≤ B * E m ^ B * H m *
          oneHighVariationWeight p base (s + loss) x v) :
    (∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ x ∈ U, ∀ m a q i j, i + j ≤ s →
        |f x a m i j q| ≤ B * E m ^ B * H m * p (s + loss) x) ∧
    ∃ T : SmoothDirections U f,
      ∀ k, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
        ∀ x ∈ U, ∀ v : Fin k → X, ∀ m a q i j, i + j ≤ s →
          |T.D k x v a m i j q| ≤ B * E m ^ B * H m *
            oneHighVariationWeight p base (s + loss) x v := by
  classical
  let P0 : I → ℕ → ℕ → ℝ → Prop := fun a s high B =>
    ∀ x ∈ U, ∀ m q i j, i + j ≤ s →
      |f x a m i j q| ≤ B * E m ^ B * H m * p high x
  have hP0 : ∀ a, ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      P0 a s (s + 0 + d) B := by
    intro a
    simpa only [P0, Nat.add_zero] using hvalue a
  obtain ⟨d0, hd0⟩ := n01c_finite_offsets_uniform P0 0
    (fun a s low high A B hh hA hAB hbound x hx m q i j hij =>
      (hbound x hx m q i j hij).trans
        (n04Realization_weightedCoefficient_mono hA hAB (hE m) (hH m)
          (apply_nonneg _ _) (hp hh x))) hP0
  refine ⟨?_, n04Realization_scalarJetTower hU J, ?_⟩
  · refine ⟨d0, fun s => ?_⟩
    obtain ⟨B, hB, hbound⟩ := hd0 s
    exact ⟨B, hB, fun x hx m a q i j hij => hbound a x hx m q i j hij⟩
  · intro k
    let Pk : I → ℕ → ℕ → ℝ → Prop := fun a s high B =>
      ∀ x ∈ U, ∀ v : Fin k → X, ∀ m q i j, i + j ≤ s →
        |(J a m i j q).D k x v| ≤ B * E m ^ B * H m *
          oneHighVariationWeight p base high x v
    have hPk : ∀ a, ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
        Pk a s (s + 0 + d) B := by
      intro a
      simpa only [Pk, Nat.add_zero] using hparameter a k
    obtain ⟨dk, hdk⟩ := n01c_finite_offsets_uniform Pk 0
      (fun a s low high A B hh hA hAB hbound x hx v m q i j hij =>
        (hbound x hx v m q i j hij).trans
          (n04Realization_weightedCoefficient_mono hA hAB (hE m) (hH m)
            (oneHighVariationWeight_nonneg p base low x v)
            (ContinuousFlexibility.Analysis.oneHighVariationWeight_mono
              hp le_rfl hh x v))) hPk
    refine ⟨dk, fun s => ?_⟩
    obtain ⟨B, hB, hbound⟩ := hdk s
    refine ⟨B, hB, fun x hx v m a q i j hij => ?_⟩
    rw [n04Realization_scalarJetTower_D_apply]
    exact hbound a x hx v m q i j hij

end ContinuousFlexibility.Analysis
