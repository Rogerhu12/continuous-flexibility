import ContinuousFlexibility.Analysis.N04RealizationPotentialProductBounds
import ContinuousFlexibility.Analysis.N01cMixedPowerNormalization

/-!
# One-high normalization of the raw potential products

The raw five-field bounds are used at the enlarged spatial budget `s+2`.
All products have been estimated before the genuine multilinear output
is normalized. Only the finite parameter prefix through `K` is needed;
the high seminorm may therefore depend on that prefix in applications.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- The reciprocal-height potential retains one original height gain and
one high parameter seminorm. The constant is uniform over the finite
parameter and spatial prefixes and precedes all actual input fields. -/
theorem n04Realization_potential_positive_oneHigh (K s : ℕ) (RH : ℝ) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (p : ℕ → Seminorm ℝ X) (center : X) (base high : ℕ),
      ∀ U : Set X, IsOpen U → ∀ Ω : Set PolarPoint, IsOpen Ω →
      ∀ A : X → SymmetricCoefficients, ∀ H Q : X → PolarPoint → ℝ,
      ∀ RF : ∀ i : Fin 5, MixedJetRegularity U Ω
        (fun x => n04RealizationPotentialInputs (A x) (H x) (Q x) i),
      ∀ W E : PolarPoint → ℝ, ∀ C P : ℝ, 1 ≤ C → 0 ≤ P →
      (∀ q ∈ Ω, 0 ≤ W q ∧ W q ≤ RH ∧ 1 ≤ E q) →
      (∀ i : Fin 5, ∀ j : ℕ, j ≤ K → ∀ u w : ℕ, u + w ≤ s + 2 →
        ∀ q (hq : q ∈ Ω), ∀ x ∈ U, p base (x - center) ≤ 1 →
        ∀ v : Fin j → X, (∀ t, p base (v t) ≤ 1) →
        ∀ R : ℝ, 1 ≤ R → p high (x - center) ≤ R →
          (∀ t, p high (v t) ≤ R) →
        ‖((RF i).parameter u w q hq).D j x v‖ ≤
          C * E q ^ P * parameterHeightWeight (W q) j *
            R ^ (((u + w : ℕ) : ℝ) / (((s + 2 : ℕ) : ℝ) + 1))) →
      ∀ k : ℕ, k ≤ K → 0 < k → ∀ a b : ℕ, a + b ≤ s →
      ∀ q (hq : q ∈ Ω), ∀ J : SmoothDirections U
        (fun x => mixedDerivative a b
          (fun z => H x z * divergenceOperator (A x) (Q x) z) q),
      ∀ x ∈ U, p base (x - center) ≤ 1 → ∀ v : Fin k → X,
        ‖J.D k x v‖ ≤ B * C ^ 3 * W q * E q ^ (P * 3) *
          oneHighVariationWeight p base high (x - center) v := by
  classical
  let I : Type := Fin (K + 1) × Fin (s + 1) × Fin (s + 1)
  choose c hc hcb using fun i : I =>
    n04Realization_potential_parameter_bound (X := X) i.1.val i.2.1.val i.2.2.val RH
  let B : ℝ := 1 + ∑ i : I, c i
  have hB : 0 < B := by
    dsimp only [B]
    have hsum : 0 ≤ ∑ i : I, c i := Finset.sum_nonneg (fun i _ => (hc i).le)
    linarith
  have hcB (i : I) : c i ≤ B :=
    (Finset.single_le_sum (fun j _ => (hc j).le) (Finset.mem_univ i)).trans
      (by dsimp only [B]; linarith)
  refine ⟨B, hB, ?_⟩
  intro p center base high U hU Ω hΩ A H Q RF W E C P hC hP hweight hraw
  intro k hk hkpos a b hab q hq J x hx hlow
  let i : I := (⟨k, Nat.lt_succ_of_le hk⟩,
    ⟨a, by omega⟩, ⟨b, by omega⟩)
  have hW := (hweight q hq).1
  have hWR := (hweight q hq).2.1
  have hE := (hweight q hq).2.2
  let M : ℝ := B * C ^ 3 * W q * E q ^ (P * 3)
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg (mul_nonneg (mul_nonneg hB.le
      (pow_nonneg (zero_le_one.trans hC) _)) hW)
      (Real.rpow_nonneg (zero_le_one.trans hE) _)
  have hn := multilinear_bound_of_unitBall (J.D k x) (normSeminorm ℝ ℝ)
    (p base) (p high) hM (a := 1 + p high (x - center)) (fun v hv => by
      let R : ℝ := (1 + p high (x - center)) + ∑ t, p high (v t)
      have hsum : 0 ≤ ∑ t, p high (v t) :=
        Finset.sum_nonneg (fun t _ => apply_nonneg _ _)
      have hR : 1 ≤ R := by
        dsimp only [R]
        linarith [apply_nonneg (p high) (x - center)]
      have hxR : p high (x - center) ≤ R := by dsimp only [R]; linarith
      have hvR (t : Fin k) : p high (v t) ≤ R :=
        (Finset.single_le_sum (fun j _ => apply_nonneg _ _) (Finset.mem_univ t)).trans
          (le_add_of_nonneg_left (by positivity))
      have hbase (j : Fin 5) (u w : ℕ) (huw : u + w ≤ s + 2) :
          ‖mixedDerivative u w (n04RealizationPotentialInputs (A x) (H x) (Q x) j) q‖ ≤
            C * E q ^ P * R ^ (((u + w : ℕ) : ℝ) / (((s + 2 : ℕ) : ℝ) + 1)) := by
        have h := hraw j 0 (Nat.zero_le _) u w huw q hq x hx hlow
          Fin.elim0 (fun t => t.elim0) R hR hxR (fun t => t.elim0)
        rw [smoothDirections_D_zero_apply ((RF j).parameter u w q hq) hx Fin.elim0] at h
        simpa only [parameterHeightWeight, if_pos rfl, ite_true, mul_one] using h
      have hjet (j : Fin 5) (u w : ℕ) (huw : u + w ≤ s + 2)
          (d : OrderedFinpartition k) (t : Fin d.length) :
          ‖((RF j).parameter u w q hq).D (d.partSize t) x (v ∘ d.emb t)‖ ≤
            W q * (C * E q ^ P *
              R ^ (((u + w : ℕ) : ℝ) / (((s + 2 : ℕ) : ℝ) + 1))) := by
        have h := hraw j (d.partSize t) ((d.partSize_le t).trans hk)
          u w huw q hq x hx hlow (v ∘ d.emb t)
          (fun n => (hv (d.emb t n)).le) R hR hxR (fun n => hvR (d.emb t n))
        simpa only [parameterHeightWeight, if_neg (Nat.ne_of_gt (d.partSize_pos t)),
          mul_assoc, mul_left_comm, mul_comm] using h
      have h := hcb i U hU Ω hΩ A H Q RF q hq J x hx v (s + 2)
        (Nat.add_le_add_right hab 2) (W q) (E q) C P R hW hWR hE hC hP hR hbase hjet
      have hraw' : ‖J.D k x v‖ ≤ (c i * C ^ 3 * W q * E q ^ (P * 3)) *
          R ^ (((a + b + 2 : ℕ) : ℝ) / (((s + 2 : ℕ) : ℝ) + 1)) := by
        simpa only [i, parameterHeightWeight, if_neg (Nat.ne_of_gt hkpos),
          mul_assoc, mul_left_comm, mul_comm] using h
      have hcoeff : c i * C ^ 3 * W q * E q ^ (P * 3) ≤ M :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hcB i) (pow_nonneg (zero_le_one.trans hC) _)) hW)
          (Real.rpow_nonneg (zero_le_one.trans hE) _)
      have hpow := Real.rpow_le_self_of_one_le hR
        (spatialOrder_fraction_le_one (Nat.add_le_add_right hab 2))
      have hbound : ‖J.D k x v‖ ≤ M * R := hraw'.trans
        ((mul_le_mul_of_nonneg_right hcoeff
          (Real.rpow_nonneg (zero_le_one.trans hR) _)).trans
            (mul_le_mul_of_nonneg_left hpow hM))
      simpa only [coe_normSeminorm, R] using hbound)
  simpa only [coe_normSeminorm, multilinearTameSize, oneHighVariationWeight, M] using hn

end ContinuousFlexibility.Analysis
