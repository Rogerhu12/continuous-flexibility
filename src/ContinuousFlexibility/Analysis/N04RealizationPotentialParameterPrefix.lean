import ContinuousFlexibility.Analysis.N04RealizationParameterRescale
import ContinuousFlexibility.Analysis.N04RealizationPotentialProductBounds

/-!
# Potential products with a finite parameter interpolation cost

The extra cost is linear in the parameter order. One rescaling removes
it from every raw factor, so the existing seven-term product estimate
applies unchanged. The final genuine multilinear map restores precisely
the total parameter cost. The common low order is not enlarged.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem n04Realization_potential_shifted_parameter_bound (k a b : ℕ) (RH : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ U : Set X, IsOpen U →
      ∀ Ω : Set PolarPoint, IsOpen Ω → ∀ A : X → SymmetricCoefficients,
      ∀ H Q : X → PolarPoint → ℝ,
      ∀ RF : ∀ i : Fin 5, MixedJetRegularity U Ω
        (fun x => n04RealizationPotentialInputs (A x) (H x) (Q x) i),
      ∀ q (hq : q ∈ Ω), ∀ J : SmoothDirections U
        (fun x => mixedDerivative a b
          (fun p => H x p * divergenceOperator (A x) (Q x) p) q),
      ∀ x ∈ U, ∀ v : Fin k → X, ∀ s λ : ℕ, a + b + 2 ≤ s →
      ∀ W E C P R : ℝ, 0 ≤ W → W ≤ RH → 1 ≤ E → 1 ≤ C → 0 ≤ P → 1 ≤ R →
      (∀ i : Fin 5, ∀ u w : ℕ, u + w ≤ a + b + 2 →
        ‖mixedDerivative u w (n04RealizationPotentialInputs (A x) (H x) (Q x) i) q‖ ≤
          C * E ^ P * R ^ (((u + w : ℕ) : ℝ) / ((s : ℝ) + 1))) →
      (∀ i : Fin 5, ∀ u w : ℕ, ∀ (huw : u + w ≤ a + b + 2)
        (d : OrderedFinpartition k) (j : Fin d.length),
        ‖((RF i).parameter u w q hq).D (d.partSize j) x (v ∘ d.emb j)‖ ≤
          W * (C * E ^ P *
            R ^ (((u + w + λ * d.partSize j : ℕ) : ℝ) / ((s : ℝ) + 1)))) →
      ‖J.D k x v‖ ≤ B * C ^ 3 * E ^ (P * 3) * parameterHeightWeight W k *
        R ^ (((a + b + 2 + λ * k : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  obtain ⟨B, hB, hb⟩ := n04Realization_potential_parameter_bound (X := X) k a b RH
  refine ⟨B, hB, ?_⟩
  intro U hU Ω hΩ A H Q RF q hq J x hx v s λ hs W E C P R
    hW hWR hE hC hP hR hbase hjet
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  let α : ℝ := (λ : ℝ) / ((s : ℝ) + 1)
  let v' : Fin k → X := fun i => R ^ (-α) • v i
  let ρ : ℝ := R ^ ((((a + b + 2 : ℕ) : ℝ) + 1) / ((s : ℝ) + 1))
  have hρ : 1 ≤ ρ := Real.one_le_rpow hR (by positivity)
  have hρpow (n : ℕ) :
      ρ ^ ((n : ℝ) / (((a + b + 2 : ℕ) : ℝ) + 1)) =
        R ^ ((n : ℝ) / ((s : ℝ) + 1)) :=
    n04Realization_rpow_change_budget hRpos.le (by positivity) _ _
  have hbase' (i : Fin 5) (u w : ℕ) (huw : u + w ≤ a + b + 2) :
      ‖mixedDerivative u w (n04RealizationPotentialInputs (A x) (H x) (Q x) i) q‖ ≤
        C * E ^ P * ρ ^ (((u + w : ℕ) : ℝ) / (((a + b + 2 : ℕ) : ℝ) + 1)) := by
    rw [hρpow]
    exact hbase i u w huw
  have hjet' (i : Fin 5) (u w : ℕ) (huw : u + w ≤ a + b + 2)
      (d : OrderedFinpartition k) (j : Fin d.length) :
      ‖((RF i).parameter u w q hq).D (d.partSize j) x (v' ∘ d.emb j)‖ ≤
        W * (C * E ^ P *
          ρ ^ (((u + w : ℕ) : ℝ) / (((a + b + 2 : ℕ) : ℝ) + 1))) := by
    rw [hρpow]
    have hexp : (((u + w + λ * d.partSize j : ℕ) : ℝ) / ((s : ℝ) + 1)) =
        (((u + w : ℕ) : ℝ) / ((s : ℝ) + 1)) + α * (d.partSize j : ℝ) := by
      dsimp only [α]
      push_cast
      ring
    have hraw := hjet i u w huw d j
    rw [hexp] at hraw
    have hraw' :
        ‖((RF i).parameter u w q hq).D (d.partSize j) x (v ∘ d.emb j)‖ ≤
          (W * (C * E ^ P)) *
            R ^ ((((u + w : ℕ) : ℝ) / ((s : ℝ) + 1)) + α * (d.partSize j : ℝ)) := by
      simpa only [mul_assoc] using hraw
    have h := n04Realization_parameter_rescale_bound
      (((RF i).parameter u w q hq).D (d.partSize j) x) (v ∘ d.emb j)
      hRpos α (((u + w : ℕ) : ℝ) / ((s : ℝ) + 1)) (W * (C * E ^ P)) hraw'
    simpa only [v', Function.comp_apply, mul_assoc] using h
  have hraw := hb U hU Ω hΩ A H Q RF q hq J x hx v' (a + b + 2) le_rfl
    W E C P ρ hW hWR hE hC hP hρ hbase' hjet'
  rw [hρpow] at hraw
  let M : ℝ := B * C ^ 3 * E ^ (P * 3) * parameterHeightWeight W k
  have hraw' : ‖J.D k x (fun i => R ^ (-α) • v i)‖ ≤
      M * R ^ (((a + b + 2 : ℕ) : ℝ) / ((s : ℝ) + 1)) := hraw
  have h := n04Realization_parameter_unscale_bound (J.D k x) v hRpos α
    (((a + b + 2 : ℕ) : ℝ) / ((s : ℝ) + 1)) M hraw'
  have hexp : (((a + b + 2 : ℕ) : ℝ) / ((s : ℝ) + 1)) + α * (k : ℝ) =
      (((a + b + 2 + λ * k : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
    dsimp only [α]
    push_cast
    ring
  rw [hexp] at h
  exact h

end ContinuousFlexibility.Analysis
