module

public import ContinuousFlexibility.Analysis.N04RealizationMixedProductJets

/-!
# Full weights in raw mixed products

Each original factor contributes its own positive coefficient exactly
once, including at parameter order zero. In particular, a sampled
physical height retained by one factor is not discarded at order zero.
The existing spatial Leibniz expansion and genuine parameter product
tower keep the sum of the assigned spatial and fixed prefix costs.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Raw factor estimates are multiplied before any one-high
normalization. The constant precedes all factors, weights and costs. -/
theorem n04Realization_fullWeightProduct_parameter_bound (m k a b : ℕ) :
    ∃ B : ℝ, 0 < B ∧
      ∀ U : Set X, IsOpen U → ∀ Ω : Set PolarPoint, IsOpen Ω →
      ∀ f : Fin m → X → PolarPoint → ℝ,
      ∀ RF : ∀ i, MixedJetRegularity U Ω (f i),
      ∀ q (hq : q ∈ Ω), ∀ J : SmoothDirections U
        (fun x => mixedDerivative a b (fun p => ∏ i, f i x p) q),
      ∀ x ∈ U, ∀ v : Fin k → X, ∀ s : ℕ, ∀ offset : Fin m → ℕ,
      ∀ W : Fin m → ℝ, (∀ i, 0 < W i) → ∀ R : ℝ, 0 < R →
      (∀ i : Fin m, ∀ u w : ℕ, u + w ≤ a + b →
        ‖mixedDerivative u w (f i x) q‖ ≤
          W i * R ^ (((u + w + offset i : ℕ) : ℝ) / ((s : ℝ) + 1))) →
      (∀ i : Fin m, ∀ u w : ℕ, u + w ≤ a + b →
        ∀ (d : OrderedFinpartition k) (j : Fin d.length),
        ‖((RF i).parameter u w q hq).D (d.partSize j) x (v ∘ d.emb j)‖ ≤
          W i * R ^ (((u + w + offset i : ℕ) : ℝ) / ((s : ℝ) + 1))) →
      ‖J.D k x v‖ ≤ B * (∏ i, W i) *
        R ^ (((a + b + ∑ i, offset i : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  classical
  let e := mixedProductLeibniz m a b
  obtain ⟨B₀, hB₀, hb₀⟩ :=
    exists_finiteProduct_allParameterJet_bound (X := X) m k 1
  let B : ℝ := 1 + (Fintype.card e.Index : ℝ) * B₀
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro U hU Ω hΩ f RF q hq J x hx v s offset W hW R hR hbase hjet
  let terms : e.Index → X → ℝ := fun t y => ∏ i,
    mixedDerivative (e.radial t i) (e.angular t i) (f i y) q
  let JT : ∀ t : e.Index, SmoothDirections U (terms t) := fun t =>
    smoothDirections_finiteProduct hU (fun i =>
      (RF i).parameter (e.radial t i) (e.angular t i) q hq)
  let M : ℝ := (∏ i, W i) *
    R ^ (((a + b + ∑ i, offset i : ℕ) : ℝ) / ((s : ℝ) + 1))
  have hM : 0 ≤ M :=
    mul_nonneg (Finset.prod_nonneg (fun i _ => (hW i).le)) (Real.rpow_nonneg hR.le _)
  have ht (t : e.Index) : ‖(JT t).D k x v‖ ≤ B₀ * M := by
    let u : Fin m → ℕ := e.radial t
    let w : Fin m → ℕ := e.angular t
    let orders : Fin m → ℕ := fun i => u i + w i + offset i
    have hsum : (∑ i, (u i + w i)) = a + b := by
      rw [Finset.sum_add_distrib, e.radial_order, e.angular_order]
    have hi (i : Fin m) : u i + w i ≤ a + b :=
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hsum.le
    have horders : (∑ i, orders i) = a + b + ∑ i, offset i := by
      dsimp only [orders]
      rw [Finset.sum_add_distrib, hsum]
    let Bi : Fin m → ℝ := fun i =>
      W i * R ^ ((orders i : ℝ) / ((s : ℝ) + 1))
    have hBi (i : Fin m) : 0 < Bi i :=
      mul_pos (hW i) (Real.rpow_pos_of_pos hR _)
    have hprod := hb₀
      (fun i => (RF i).parameter (u i) (w i) q hq) (JT t) x hx
      1 zero_le_one le_rfl Bi hBi
      (fun i => hbase i (u i) (w i) (hi i)) v
      (fun i d j => by
        simpa only [one_mul] using hjet i (u i) (w i) (hi i) d j)
    have hBiProd : (∏ i, Bi i) = M := by
      dsimp only [Bi, M]
      rw [Finset.prod_mul_distrib,
        n01c_finset_prod_spatialOrder _ orders hR s, horders]
    simpa only [ite_self, mul_one, hBiProd] using hprod
  have hd := smoothDirections_D_eq_linearCombination J JT (fun _ => (1 : ℝ))
    (fun y hy => by
      simpa only [one_mul] using n04Realization_mixedProductLeibniz_on_open e hΩ
        (fun i => f i y) (fun i => (RF i).spatial y hy) hq) k hx v
  simp only [one_mul] at hd
  rw [hd]
  calc
    ‖∑ t : e.Index, (JT t).D k x v‖ ≤ ∑ t : e.Index, ‖(JT t).D k x v‖ := norm_sum_le _ _
    _ ≤ ∑ _t : e.Index, B₀ * M := Finset.sum_le_sum (fun t _ => ht t)
    _ = ((Fintype.card e.Index : ℝ) * B₀) * M := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ B * M := mul_le_mul_of_nonneg_right (by dsimp only [B]; linarith) hM
    _ = _ := by dsimp only [M]; ring

end ContinuousFlexibility.Analysis
