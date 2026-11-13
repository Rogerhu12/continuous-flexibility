import ContinuousFlexibility.Analysis.N04SourceColumnsPrefix
import ContinuousFlexibility.Analysis.N04SourceColumnsProduct

/-!
# Products of full current families

Unlike a reference difference, a full family has no height gain at
parameter order zero. The finite Leibniz formula retains a height gain
at every positive parameter order, since every such term differentiates
at least one factor. The uniform bound on the height absorbs additional
height factors without changing the one-high grading.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X I : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem n04SourceColumns_fullProduct_parameter_bound (m k a b : ℕ) (RH : ℝ) :
    ∃ B : ℝ, 0 < B ∧
      ∀ U : Set X, IsOpen U → ∀ Ω : Set PolarPoint, IsOpen Ω →
      ∀ f : Fin m → X → PolarPoint → ℝ,
      ∀ RF : ∀ i, MixedJetRegularity U Ω (f i),
      ∀ q (hq : q ∈ Ω), ∀ J : SmoothDirections U
        (fun x => mixedDerivative a b (fun p => ∏ i, f i x p) q),
      ∀ x ∈ U, ∀ v : Fin k → X, ∀ s : ℕ, ∀ offset : Fin m → ℕ,
      ∀ W : Fin m → ℝ, (∀ i, 0 < W i) → ∀ H R : ℝ,
      0 ≤ H → H ≤ RH → 0 < R →
      (∀ i : Fin m, ∀ u w : ℕ, u + w ≤ a + b →
        ‖mixedDerivative u w (f i x) q‖ ≤
          W i * R ^ (((u + w + offset i : ℕ) : ℝ) / ((s : ℝ) + 1))) →
      (∀ i : Fin m, ∀ u w : ℕ, u + w ≤ a + b →
        ∀ (d : OrderedFinpartition k) (j : Fin d.length),
        ‖((RF i).parameter u w q hq).D (d.partSize j) x (v ∘ d.emb j)‖ ≤
          H * (W i * R ^ (((u + w + offset i : ℕ) : ℝ) / ((s : ℝ) + 1)))) →
      ‖J.D k x v‖ ≤ B * (∏ i, W i) * parameterHeightWeight H k *
        R ^ (((a + b + ∑ i, offset i : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  classical
  let e := mixedProductLeibniz m a b
  obtain ⟨B₀, hB₀, hb₀⟩ := exists_finiteProduct_allParameterJet_bound (X := X) m k RH
  let B : ℝ := 1 + (Fintype.card e.Index : ℝ) * B₀
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro U hU Ω hΩ f RF q hq J x hx v s offset W hW H R hH hHR hR hbase hjet
  let terms : e.Index → X → ℝ := fun t y => ∏ i,
    mixedDerivative (e.radial t i) (e.angular t i) (f i y) q
  let JT : ∀ t : e.Index, SmoothDirections U (terms t) := fun t =>
    smoothDirections_finiteProduct hU (fun i =>
      (RF i).parameter (e.radial t i) (e.angular t i) q hq)
  let M : ℝ := (∏ i, W i) * parameterHeightWeight H k *
    R ^ (((a + b + ∑ i, offset i : ℕ) : ℝ) / ((s : ℝ) + 1))
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg (Finset.prod_nonneg (fun i _ => (hW i).le))
      (parameterHeightWeight_nonneg hH k)) (Real.rpow_nonneg hR.le _)
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
    let Bi : Fin m → ℝ := fun i => W i * R ^ ((orders i : ℝ) / ((s : ℝ) + 1))
    have hBi (i : Fin m) : 0 < Bi i :=
      mul_pos (hW i) (Real.rpow_pos_of_pos hR _)
    have hprod := hb₀ (fun i => (RF i).parameter (u i) (w i) q hq) (JT t) x hx
      H hH hHR Bi hBi (fun i => hbase i (u i) (w i) (hi i)) v
      (fun i d j => hjet i (u i) (w i) (hi i) d j)
    have hBiProd : (∏ i, Bi i) = (∏ i, W i) *
        R ^ (((a + b + ∑ i, offset i : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
      dsimp only [Bi]
      rw [Finset.prod_mul_distrib,
        n01c_finset_prod_spatialOrder _ orders hR s, horders]
    simpa only [hBiProd, M, mul_assoc, mul_left_comm, mul_comm] using hprod
  have hd := smoothDirections_D_eq_linearCombination J JT (fun _ => (1 : ℝ))
    (fun y hy => by simpa only [one_mul] using
      n04Realization_mixedProductLeibniz_on_open e hΩ
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

/-- Normalize the full product once. At positive order its entire
height gain is retained by the final one-high estimate. -/
theorem n04SourceColumns_fullProduct_raw_oneHigh (m K s : ℕ) (RH : ℝ) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (p : ℕ → Seminorm ℝ X) (base high : ℕ), ∀ offset : Fin m → ℕ,
      ∀ U : Set X, IsOpen U → ∀ Ω : Set PolarPoint, IsOpen Ω →
      ∀ f : Fin m → X → PolarPoint → ℝ,
      ∀ RF : ∀ i, MixedJetRegularity U Ω (f i),
      ∀ W : Fin m → PolarPoint → ℝ, (∀ i q, q ∈ Ω → 0 < W i q) →
      ∀ H : PolarPoint → ℝ, (∀ q ∈ Ω, 0 ≤ H q ∧ H q ≤ RH) →
      (∀ i : Fin m, ∀ j : ℕ, j ≤ K → ∀ u w : ℕ, u + w ≤ s →
        ∀ q (hq : q ∈ Ω), ∀ x ∈ U, p base x ≤ 1 →
        ∀ v : Fin j → X, (∀ t, p base (v t) ≤ 1) →
        ∀ R : ℝ, 1 ≤ R → p high x ≤ R → (∀ t, p high (v t) ≤ R) →
        ‖((RF i).parameter u w q hq).D j x v‖ ≤
          W i q * parameterHeightWeight (H q) j *
            R ^ (((u + w + offset i : ℕ) : ℝ) /
              (((s + ∑ i, offset i : ℕ) : ℝ) + 1))) →
      ∀ k : ℕ, k ≤ K → ∀ a b : ℕ, a + b ≤ s →
      ∀ q (hq : q ∈ Ω), ∀ J : SmoothDirections U
        (fun x => mixedDerivative a b (fun y => ∏ i, f i x y) q),
      ∀ x ∈ U, p base x ≤ 1 → ∀ v : Fin k → X,
        ‖J.D k x v‖ ≤ B * (∏ i, W i q) * parameterHeightWeight (H q) k *
          oneHighVariationWeight p base high x v := by
  classical
  let J := Fin (K + 1) × Fin (s + 1) × Fin (s + 1)
  choose c hc hb using fun i : J =>
    n04SourceColumns_fullProduct_parameter_bound (X := X) m i.1.val i.2.1.val i.2.2.val RH
  let B : ℝ := 1 + ∑ i : J, c i
  have hsum : 0 ≤ ∑ i : J, c i := Finset.sum_nonneg (fun i _ => (hc i).le)
  have hB : 0 < B := by dsimp only [B]; linarith
  have hcB (i : J) : c i ≤ B :=
    (Finset.single_le_sum (fun j _ => (hc j).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨B, hB, ?_⟩
  intro p base high offset U hU Ω hΩ f RF W hW H hH hraw k hk a b hab q hq Jq x hx hlow
  let i : J := (⟨k, Nat.lt_succ_of_le hk⟩, ⟨a, by omega⟩, ⟨b, by omega⟩)
  let M : ℝ := B * (∏ j, W j q) * parameterHeightWeight (H q) k
  have hWp : 0 ≤ ∏ j, W j q := Finset.prod_nonneg (fun j _ => (hW j q hq).le)
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg hB.le hWp)
    (parameterHeightWeight_nonneg (hH q hq).1 k)
  have hn := multilinear_bound_of_unitBall (Jq.D k x) (normSeminorm ℝ ℝ)
    (p base) (p high) hM (a := 1 + p high x) (fun v hv => by
      let R : ℝ := 1 + p high x + ∑ j, p high (v j)
      have hs : 0 ≤ ∑ j, p high (v j) := Finset.sum_nonneg (fun _ _ => apply_nonneg _ _)
      have hR : 1 ≤ R := by dsimp only [R]; linarith [apply_nonneg (p high) x]
      have hxR : p high x ≤ R := by dsimp only [R]; linarith
      have hvR (j : Fin k) : p high (v j) ≤ R :=
        (Finset.single_le_sum (fun _ _ => apply_nonneg _ _) (Finset.mem_univ j)).trans
          (le_add_of_nonneg_left (by positivity))
      have hbase (j : Fin m) (u w : ℕ) (huw : u + w ≤ a + b) :
          ‖mixedDerivative u w (f j x) q‖ ≤ W j q *
            R ^ (((u + w + offset j : ℕ) : ℝ) /
              (((s + ∑ i, offset i : ℕ) : ℝ) + 1)) := by
        have h := hraw j 0 (Nat.zero_le _) u w (huw.trans hab) q hq x hx hlow
          Fin.elim0 (fun t => t.elim0) R hR hxR (fun t => t.elim0)
        simpa only [smoothDirections_D_zero_apply ((RF j).parameter u w q hq) hx,
          parameterHeightWeight, if_pos rfl, mul_one] using h
      have hjet (j : Fin m) (u w : ℕ) (huw : u + w ≤ a + b)
          (d : OrderedFinpartition k) (t : Fin d.length) :
          ‖((RF j).parameter u w q hq).D (d.partSize t) x (v ∘ d.emb t)‖ ≤
            H q * (W j q * R ^ (((u + w + offset j : ℕ) : ℝ) /
              (((s + ∑ i, offset i : ℕ) : ℝ) + 1))) := by
        have h := hraw j (d.partSize t) ((d.partSize_le t).trans hk) u w (huw.trans hab)
          q hq x hx hlow (v ∘ d.emb t) (fun n => (hv _).le) R hR hxR (fun n => hvR _)
        simpa only [parameterHeightWeight, if_neg (Nat.ne_of_gt (d.partSize_pos t)),
          mul_assoc, mul_left_comm, mul_comm] using h
      have h := hb i U hU Ω hΩ f RF q hq Jq x hx v (s + ∑ j, offset j) offset
        (fun j => W j q) (fun j => hW j q hq) (H q) R (hH q hq).1 (hH q hq).2
        (zero_lt_one.trans_le hR) hbase hjet
      have hcoef : c i * (∏ j, W j q) * parameterHeightWeight (H q) k ≤ M :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hcB i) hWp)
          (parameterHeightWeight_nonneg (hH q hq).1 k)
      have hpow := Real.rpow_le_self_of_one_le hR
        (spatialOrder_fraction_le_one (Nat.add_le_add_right hab (∑ j, offset j)))
      have hfinal := h.trans ((mul_le_mul_of_nonneg_right hcoef
        (Real.rpow_nonneg (zero_le_one.trans hR) _)).trans
          (mul_le_mul_of_nonneg_left hpow hM))
      simpa only [coe_normSeminorm, R] using hfinal)
  simpa only [coe_normSeminorm, M, multilinearTameSize, oneHighVariationWeight] using hn

end ContinuousFlexibility.Analysis
