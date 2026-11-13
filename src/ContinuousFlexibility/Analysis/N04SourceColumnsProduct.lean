import ContinuousFlexibility.Analysis.N04RealizationFixedBasePrefix
import ContinuousFlexibility.Analysis.N04RealizationFullWeightProductOneHigh
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# Multiplication of scalar families with one high parameter seminorm

The original towers may have a different loss at each parameter order.
The low order is selected only once, before the parameter order.  For a
finite parameter prefix, interpolation distributes its loss among the
factors; the full product is then normalized by multilinearity.  Every
external scalar weight is retained, including the order-zero weights.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X I : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Pack finitely many coefficients before any piece or evaluation point
is chosen. The spatial order in the seminorm is not enlarged here. -/
private theorem n04SourceColumns_finite_prefix
    (p : ℕ → Seminorm ℝ X) (base : ℕ) (L : ℕ → ℕ)
    {m : ℕ} {U : Set X} {Ω : Set PolarPoint}
    (E : I → ℝ) (W : Fin m → I → ℝ)
    (hE : ∀ t, 1 ≤ E t) (hW : ∀ i t, 0 < W i t)
    (f : Fin m → I → X → PolarPoint → ℝ)
    (RF : ∀ i t, MixedJetRegularity U Ω (f i t))
    (hbound : ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ i t q (hq : q ∈ Ω) a b, a + b ≤ s →
      ∀ x ∈ U, ∀ v : Fin k → X,
        |((RF i t).parameter a b q hq).D k x v| ≤
          B * E t ^ B * W i t * oneHighVariationWeight p base (s + L k) x v)
    (K s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ k, k ≤ K → ∀ i t q (hq : q ∈ Ω) a b,
      a + b ≤ s → ∀ x ∈ U, ∀ v : Fin k → X,
        |((RF i t).parameter a b q hq).D k x v| ≤
          B * E t ^ B * W i t * oneHighVariationWeight p base (a + b + L k) x v := by
  classical
  let J := Fin (K + 1) × Fin (s + 1)
  choose c hc hb using fun j : J => hbound j.1.val j.2.val
  let B : ℝ := 1 + ∑ j : J, c j
  have hsum : 0 ≤ ∑ j : J, c j := Finset.sum_nonneg (fun j _ => (hc j).le)
  have hB : 0 < B := by dsimp only [B]; linarith
  have hcB (j : J) : c j ≤ B :=
    (Finset.single_le_sum (fun j _ => (hc j).le) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨B, hB, ?_⟩
  intro k hk i t q hq a b hab x hx v
  let j : J := (⟨k, Nat.lt_succ_of_le hk⟩, ⟨a + b, Nat.lt_succ_of_le hab⟩)
  have hcoef : c j * E t ^ c j ≤ B * E t ^ B :=
    mul_le_mul (hcB j) (Real.rpow_le_rpow_of_exponent_le (hE t) (hcB j))
      (Real.rpow_nonneg (zero_le_one.trans (hE t)) _) hB.le
  exact (hb j i t q hq a b le_rfl x hx v).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (hW i t).le)
      (oneHighVariationWeight_nonneg p base (a + b + L k) x v))

/-- The same low order works for every parameter order of a finite
product. The larger loss may depend on that order, but not on the spatial
order, the piece, the point, or the directions. -/
theorem n04SourceColumns_product_oneHigh
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (hI : HasInterpolation p)
    (oldBase : ℕ) (L : ℕ → ℕ)
    {m : ℕ} {U : Set X} {Ω : Set PolarPoint}
    (hU : IsOpen U) (hΩ : IsOpen Ω)
    (E : I → ℝ) (W : Fin m → I → ℝ)
    (hE : ∀ t, 1 ≤ E t) (hW : ∀ i t, 0 < W i t)
    (f : Fin m → I → X → PolarPoint → ℝ)
    (RF : ∀ i t, MixedJetRegularity U Ω (f i t))
    (hbound : ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ i t q (hq : q ∈ Ω) a b, a + b ≤ s →
      ∀ x ∈ U, ∀ v : Fin k → X,
        |((RF i t).parameter a b q hq).D k x v| ≤
          B * E t ^ B * W i t * oneHighVariationWeight p oldBase (s + L k) x v) :
    ∃ base : ℕ, oldBase ≤ base ∧ ∀ k : ℕ, ∃ loss : ℕ, ∀ s : ℕ,
      ∃ B : ℝ, 0 < B ∧ ∀ t q (hq : q ∈ Ω) a b, a + b ≤ s →
      ∀ J : SmoothDirections U
        (fun x => mixedDerivative a b (fun y => ∏ i, f i t x y) q),
      ∀ x ∈ U, p base x ≤ 1 → ∀ v : Fin k → X,
        |J.D k x v| ≤ B * E t ^ B * (∏ i, W i t) *
          oneHighVariationWeight p base (s + loss) x v := by
  classical
  obtain ⟨base, hbase, hprefix⟩ := n04Realization_fixedBase_prefix_power p hp hI oldBase L
  refine ⟨base, hbase, fun k => ?_⟩
  obtain ⟨shift, hshift⟩ := hprefix k
  let offset : ℕ := shift * k
  let loss : ℕ := base + m * offset + offset + 1
  refine ⟨loss, fun s => ?_⟩
  obtain ⟨A, hA, hAb⟩ := n04SourceColumns_finite_prefix p oldBase L E W hE hW f RF hbound k s
  obtain ⟨C, hC, hCb⟩ := hshift (s + m * offset)
  obtain ⟨P, hP, hPb⟩ := n04Realization_fullWeightProduct_oneHigh (X := X) m k s
  obtain ⟨B, hB, hBb⟩ := coefficientEnvelope_pack (P * (A * C) ^ m) (A * (m : ℝ))
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hhigh : base + (s + m * offset) + shift * k + 1 = s + loss := by
    dsimp only [loss, offset]
    omega
  have hsum : (∑ _i : Fin m, offset) = m * offset := by simp
  refine ⟨B, hB, ?_⟩
  intro t q hq a b hab J x hx hlow v
  let weights : Fin m → PolarPoint → ℝ := fun i _ => (A * C) * E t ^ A * W i t
  have hweights (i : Fin m) (q : PolarPoint) (hq : q ∈ Ω) : 0 < weights i q :=
    mul_pos (mul_pos (mul_pos hA hCpos)
      (Real.rpow_pos_of_pos (zero_lt_one.trans_le (hE t)) _)) (hW i t)
  have hraw : ∀ i : Fin m, ∀ j : ℕ, j ≤ k → ∀ u w : ℕ, u + w ≤ s →
      ∀ r (hr : r ∈ Ω), ∀ z ∈ U, p base (z - (0 : X)) ≤ 1 →
      ∀ v' : Fin j → X, (∀ n, p base (v' n) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → p (s + loss) (z - (0 : X)) ≤ R →
        (∀ n, p (s + loss) (v' n) ≤ R) →
      ‖((RF i t).parameter u w r hr).D j z v'‖ ≤
        weights i r * R ^ (((u + w + offset : ℕ) : ℝ) /
          (((s + ∑ _i : Fin m, offset : ℕ) : ℝ) + 1)) := by
    intro i j hj u w huw r hr z hz hzlow v' hv R hR hzR hvR
    have hzlow' : p base z ≤ 1 := by simpa only [sub_zero] using hzlow
    have hzR' : p (base + (s + m * offset) + shift * k + 1) z ≤ R := by
      simpa only [hhigh, sub_zero] using hzR
    have hvR' : ∀ n, p (base + (s + m * offset) + shift * k + 1) (v' n) ≤ R := by
      simpa only [hhigh] using hvR
    have hweight := hCb j hj (u + w) (huw.trans (Nat.le_add_right _ _)) z hzlow'
      v' hv R hR hzR' hvR'
    have hnum : (u + w + shift * j : ℕ) ≤ u + w + offset := by
      dsimp only [offset]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left shift hj) _
    have hden : ((s + m * offset : ℕ) : ℝ) + 1 ≤
        ((s + m * offset + shift * k : ℕ) : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right (Nat.le_add_right _ _) 1
    have hexp : ((u + w + shift * j : ℕ) : ℝ) /
        (((s + m * offset + shift * k : ℕ) : ℝ) + 1) ≤
        ((u + w + offset : ℕ) : ℝ) / (((s + m * offset : ℕ) : ℝ) + 1) := by
      apply div_le_div₀ (by positivity) (by exact_mod_cast hnum) (by positivity) hden
    have hone : oneHighVariationWeight p oldBase (u + w + L j) z v' ≤
        C * R ^ (((u + w + offset : ℕ) : ℝ) /
          (((s + m * offset : ℕ) : ℝ) + 1)) :=
      (oneHighVariationWeight_mono hp hbase le_rfl z v').trans
        (hweight.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hR hexp) hCpos.le))
    have hcost : 0 ≤ A * E t ^ A * W i t :=
      mul_nonneg (mul_nonneg hA.le (Real.rpow_nonneg (zero_le_one.trans (hE t)) _))
        (hW i t).le
    rw [Real.norm_eq_abs]
    calc
      _ ≤ A * E t ^ A * W i t *
          oneHighVariationWeight p oldBase (u + w + L j) z v' :=
        hAb j hj i t r hr u w huw z hz v'
      _ ≤ A * E t ^ A * W i t *
          (C * R ^ (((u + w + offset : ℕ) : ℝ) /
            (((s + m * offset : ℕ) : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hone hcost
      _ = _ := by rw [hsum]; dsimp only [weights]; ring
  have hpbound := hPb p (0 : X) base (s + loss) (fun _i : Fin m => offset)
    U hU Ω hΩ (fun i => f i t) (fun i => RF i t) weights hweights hraw
    k le_rfl a b hab q hq J x hx (by simpa only [sub_zero] using hlow) v
  have hprod : (∏ i, weights i q) =
      (A * C) ^ m * E t ^ (A * (m : ℝ)) * (∏ i, W i t) := by
    dsimp only [weights]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans (hE t)) A m]
  have hrest : 0 ≤ (∏ i, W i t) * oneHighVariationWeight p base (s + loss) x v :=
    mul_nonneg (Finset.prod_nonneg (fun i _ => (hW i t).le))
      (oneHighVariationWeight_nonneg _ _ _ _ _)
  have hpack := mul_le_mul_of_nonneg_right (hBb (E t) (hE t)) hrest
  simpa only [Real.norm_eq_abs, sub_zero, hprod, mul_assoc] using
    hpbound.trans (by simpa only [sub_zero, hprod, mul_assoc] using hpack)

end ContinuousFlexibility.Analysis
