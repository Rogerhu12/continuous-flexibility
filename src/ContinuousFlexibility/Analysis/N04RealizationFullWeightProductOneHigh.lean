module

public import ContinuousFlexibility.Analysis.N04RealizationFullWeightProduct
public import ContinuousFlexibility.Analysis.N01cMixedPowerNormalization

/-!
# One high seminorm for the full raw source product

The physical pullback and source multiplier are multiplied first.
Each factor retains its complete coefficient, including sampled height
at order zero. Only the genuine product is normalized. Its finite
prefix costs enlarge the high order without changing the supplied
low order, parameter neighborhood, or fields.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem n04Realization_fullWeightProduct_oneHigh (m K s : ℕ) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (p : ℕ → Seminorm ℝ X) (center : X) (base high : ℕ),
      ∀ offset : Fin m → ℕ,
      ∀ U : Set X, IsOpen U → ∀ Ω : Set PolarPoint, IsOpen Ω →
      ∀ f : Fin m → X → PolarPoint → ℝ,
      ∀ RF : ∀ i, MixedJetRegularity U Ω (f i),
      ∀ W : Fin m → PolarPoint → ℝ, (∀ i q, q ∈ Ω → 0 < W i q) →
      (∀ i : Fin m, ∀ j : ℕ, j ≤ K → ∀ u w : ℕ, u + w ≤ s →
        ∀ q (hq : q ∈ Ω), ∀ x ∈ U, p base (x - center) ≤ 1 →
        ∀ v : Fin j → X, (∀ t, p base (v t) ≤ 1) →
        ∀ R : ℝ, 1 ≤ R → p high (x - center) ≤ R →
          (∀ t, p high (v t) ≤ R) →
        ‖((RF i).parameter u w q hq).D j x v‖ ≤
          W i q * R ^ (((u + w + offset i : ℕ) : ℝ) /
            (((s + ∑ i, offset i : ℕ) : ℝ) + 1))) →
      ∀ k : ℕ, k ≤ K → ∀ a b : ℕ, a + b ≤ s →
      ∀ q (hq : q ∈ Ω), ∀ J : SmoothDirections U
        (fun x => mixedDerivative a b (fun z => ∏ i, f i x z) q),
      ∀ x ∈ U, p base (x - center) ≤ 1 → ∀ v : Fin k → X,
        ‖J.D k x v‖ ≤ B * (∏ i, W i q) *
          oneHighVariationWeight p base high (x - center) v := by
  classical
  let I : Type := Fin (K + 1) × Fin (s + 1) × Fin (s + 1)
  choose c hc hcb using fun i : I =>
    n04Realization_fullWeightProduct_parameter_bound (X := X)
      m i.1.val i.2.1.val i.2.2.val
  let B : ℝ := 1 + ∑ i : I, c i
  have hB : 0 < B := by
    dsimp only [B]
    have hsum : 0 ≤ ∑ i : I, c i := Finset.sum_nonneg (fun i _ => (hc i).le)
    linarith
  have hcB (i : I) : c i ≤ B :=
    (Finset.single_le_sum (fun j _ => (hc j).le) (Finset.mem_univ i)).trans
      (by dsimp only [B]; linarith)
  refine ⟨B, hB, ?_⟩
  intro p center base high offset U hU Ω hΩ f RF W hW hraw
  intro k hk a b hab q hq J x hx hlow
  let i : I := (⟨k, Nat.lt_succ_of_le hk⟩, ⟨a, by omega⟩, ⟨b, by omega⟩)
  let M : ℝ := B * ∏ j, W j q
  have hWprod : 0 ≤ ∏ j, W j q :=
    Finset.prod_nonneg (fun j _ => (hW j q hq).le)
  have hM : 0 ≤ M := mul_nonneg hB.le hWprod
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
      have hbase (j : Fin m) (u w : ℕ) (huw : u + w ≤ a + b) :
          ‖mixedDerivative u w (f j x) q‖ ≤ W j q *
            R ^ (((u + w + offset j : ℕ) : ℝ) /
              (((s + ∑ i, offset i : ℕ) : ℝ) + 1)) := by
        have h := hraw j 0 (Nat.zero_le _) u w (huw.trans hab)
          q hq x hx hlow Fin.elim0 (fun t => t.elim0) R hR hxR (fun t => t.elim0)
        rw [smoothDirections_D_zero_apply ((RF j).parameter u w q hq) hx Fin.elim0] at h
        exact h
      have hjet (j : Fin m) (u w : ℕ) (huw : u + w ≤ a + b)
          (d : OrderedFinpartition k) (t : Fin d.length) :
          ‖((RF j).parameter u w q hq).D (d.partSize t) x (v ∘ d.emb t)‖ ≤
            W j q * R ^ (((u + w + offset j : ℕ) : ℝ) /
              (((s + ∑ i, offset i : ℕ) : ℝ) + 1)) :=
        hraw j (d.partSize t) ((d.partSize_le t).trans hk) u w (huw.trans hab)
          q hq x hx hlow (v ∘ d.emb t) (fun n => (hv (d.emb t n)).le)
          R hR hxR (fun n => hvR (d.emb t n))
      have h := hcb i U hU Ω hΩ f RF q hq J x hx v
        (s + ∑ i, offset i) offset (fun j => W j q) (fun j => hW j q hq)
        R (zero_lt_one.trans_le hR) hbase hjet
      have hcoeff : c i * (∏ j, W j q) ≤ M :=
        mul_le_mul_of_nonneg_right (hcB i) hWprod
      have hpow := Real.rpow_le_self_of_one_le hR
        (spatialOrder_fraction_le_one (Nat.add_le_add_right hab (∑ i, offset i)))
      have hbound : ‖J.D k x v‖ ≤ M * R := h.trans
        ((mul_le_mul_of_nonneg_right hcoeff
          (Real.rpow_nonneg (zero_le_one.trans hR) _)).trans
            (mul_le_mul_of_nonneg_left hpow hM))
      simpa only [coe_normSeminorm, R] using hbound)
  simpa only [coe_normSeminorm, multilinearTameSize, oneHighVariationWeight, M] using hn

end ContinuousFlexibility.Analysis
