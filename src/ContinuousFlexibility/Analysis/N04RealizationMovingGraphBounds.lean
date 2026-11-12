import ContinuousFlexibility.Analysis.N04RealizationPhysicalJointBounds
import ContinuousFlexibility.Analysis.N01cPhysicalFlowGraph

/-!
# Weighted finite partitions for a genuine moving-point graph

The outer physical field retains its complete height factor. Only
positive derivatives of the moving point occur. A pure spatial block
costs one less order before it is inserted into the outer joint jet;
a block containing parameter directions has its supplied finite-prefix
offset. The two costs combine without changing the parameter domain.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

/-- The spatial factor introduced by the outer derivative cancels the
one-order saving of a pure spatial inverse-point derivative. -/
theorem n04Realization_movingGraph_block_order
    (κ β offset : ℕ) (hpart : 0 < κ + β) :
    (if κ = 0 then β - 1 else β + offset) + 1 ≤ β + (offset + 1) * κ := by
  by_cases hk : κ = 0
  · simp only [hk, if_pos rfl, Nat.mul_zero, Nat.add_zero]
    omega
  · have hm : offset + 1 ≤ (offset + 1) * κ := by
      simpa only [Nat.mul_one] using
        Nat.mul_le_mul_left (offset + 1) (show 1 ≤ κ by omega)
    simp only [if_neg hk]
    omega

/-- The graph's actual physical slot is estimated through its max norm;
its state slot is left unchanged. The constant is uniform in both
physical coordinates and all block orders. -/
theorem n04Realization_movingGraph_slot_bound
    {E : Type*} (q : E → ℝ) (w : E × PolarPoint)
    (κ β offset : ℕ) (hpart : 0 < κ + β)
    {M t : ℝ} (hM : 1 ≤ M) (ht : 1 ≤ t)
    (hq : q w.1 ≤ 2)
    (hpoint : ‖w.2‖ ≤ M * t ^ (if κ = 0 then β - 1 else β + offset)) :
    q w.1 + t * |w.2.1| + t * |w.2.2| ≤
      (4 * M) * t ^ (β + (offset + 1) * κ) := by
  let j : ℕ := if κ = 0 then β - 1 else β + offset
  let d : ℕ := β + (offset + 1) * κ
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hpow : t ^ (j + 1) ≤ t ^ d :=
    pow_le_pow_right₀ ht (n04Realization_movingGraph_block_order κ β offset hpart)
  have hone : 1 ≤ M * t ^ d :=
    one_le_mul_of_one_le_of_one_le hM (one_le_pow₀ ht)
  have hr : |w.2.1| ≤ M * t ^ j :=
    (by simpa only [Real.norm_eq_abs] using norm_fst_le w.2).trans hpoint
  have ha : |w.2.2| ≤ M * t ^ j :=
    (by simpa only [Real.norm_eq_abs] using norm_snd_le w.2).trans hpoint
  have hrad : t * |w.2.1| ≤ M * t ^ d := by
    calc
      _ ≤ t * (M * t ^ j) := mul_le_mul_of_nonneg_left hr ht0
      _ = M * t ^ (j + 1) := by rw [pow_succ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hM0
  have hang : t * |w.2.2| ≤ M * t ^ d := by
    calc
      _ ≤ t * (M * t ^ j) := mul_le_mul_of_nonneg_left ha ht0
      _ = M * t ^ (j + 1) := by rw [pow_succ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hM0
  dsimp only [d] at hone hrad hang
  nlinarith

variable {X Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {U : Set X} {V : Set Y} {f : X → Y} {g : Y → ℝ}

/-- A pointwise weighted estimate for the actual projective chain rule.
The single outer constant may already contain the entire physical
height and material weight. Positive inner jets have only their raw
block costs; no estimate for the composition is assumed. -/
theorem n04Realization_realComp_weighted_power_bound
    (J : SmoothDirections U f) (K : SmoothDirections V g)
    (hmap : MapsTo f U V) (q : Y → ℝ) (hq : ∀ y, 0 ≤ q y)
    {C M t : ℝ} (hC : 0 ≤ C) (hM : 1 ≤ M) (ht : 1 ≤ t)
    (n budget : ℕ) (x : X) (v : Fin n → X)
    (cost : ∀ c : OrderedFinpartition n, Fin c.length → ℕ)
    (hcost : ∀ c, ∑ i, cost c i ≤ budget)
    (houter : ∀ j : ℕ, j ≤ n → ∀ w : Fin j → Y,
      |K.D j (f x) w| ≤ C * ∏ i, q (w i))
    (hinner : ∀ c : OrderedFinpartition n, ∀ i : Fin c.length,
      q (J.D (c.partSize i) x (v ∘ c.emb i)) ≤ M * t ^ cost c i) :
    |(smoothDirections_realCompTVS J K hmap).D n x v| ≤
      (Fintype.card (OrderedFinpartition n) : ℝ) * C * M ^ n * t ^ budget := by
  classical
  have hterm (c : OrderedFinpartition n) :
      |K.D c.length (f x) (fun i => J.D (c.partSize i) x (v ∘ c.emb i))| ≤
        C * M ^ n * t ^ budget := by
    have hprod :
        (∏ i : Fin c.length, q (J.D (c.partSize i) x (v ∘ c.emb i))) ≤
          M ^ c.length * t ^ (∑ i, cost c i) := by
      calc
        _ ≤ ∏ i : Fin c.length, M * t ^ cost c i :=
          Finset.prod_le_prod₀ (fun i _ => hq _) (fun i _ => hinner c i)
        _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hpowers : M ^ c.length * t ^ (∑ i, cost c i) ≤ M ^ n * t ^ budget :=
      mul_le_mul (pow_le_pow_right₀ hM c.length_le)
        (pow_le_pow_right₀ ht (hcost c))
        (pow_nonneg (zero_le_one.trans ht) _)
        (pow_nonneg (zero_le_one.trans hM) _)
    exact (houter c.length c.length_le _).trans
      ((mul_le_mul_of_nonneg_left (hprod.trans hpowers) hC).trans_eq (by ring))
  rw [smoothDirections_realCompTVS_D_apply]
  calc
    _ ≤ ∑ c : OrderedFinpartition n,
        |K.D c.length (f x) (fun i => J.D (c.partSize i) x (v ∘ c.emb i))| := by
      simpa only [Real.norm_eq_abs] using norm_sum_le
        (Finset.univ : Finset (OrderedFinpartition n))
        (fun c => K.D c.length (f x) (fun i => J.D (c.partSize i) x (v ∘ c.emb i)))
    _ ≤ ∑ _c : OrderedFinpartition n, C * M ^ n * t ^ budget :=
      Finset.sum_le_sum (fun c _ => hterm c)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end ContinuousFlexibility.Analysis
