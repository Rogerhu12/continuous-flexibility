import ContinuousFlexibility.Analysis.N04RealizationFiniteProductScale
import ContinuousFlexibility.Analysis.N01cMixedPowerNormalization

/-! Finite products with a height factor at positive parameter orders.
The direction rescaling is shared by all factors, so the interpolation
loss is paid at the total parameter order. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem n04NegativeHeight_product_shifted_bound (m k a b : ℕ) (RH : ℝ) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (U : Set X), IsOpen U → ∀ (Ω : Set PolarPoint), IsOpen Ω →
      ∀ f : Fin m → X → PolarPoint → ℝ,
      ∀ F : ∀ i, MixedJetRegularity U Ω (f i), ∀ q (hq : q ∈ Ω),
      ∀ J : SmoothDirections U (fun y => mixedDerivative a b (fun p => ∏ i, f i y p) q),
      ∀ x ∈ U, ∀ (P : X → Prop) (v : Fin k → X), (∀ i, P (v i)) →
      ∀ H M R : ℝ, 0 ≤ H → H ≤ RH → 1 ≤ M → 1 ≤ R →
      ∀ budget shift : ℕ,
      (∀ i : Fin m, ∀ j : ℕ, j ≤ k → ∀ u w : ℕ, u + w ≤ a + b →
        ∀ z : Fin j → X, (∀ l, P (z l)) →
        ‖((F i).parameter u w q hq).D j x z‖ ≤
          M * parameterHeightWeight H j *
            R ^ (((u + w + shift * j : ℕ) : ℝ) / ((budget : ℝ) + 1))) →
      ‖J.D k x v‖ ≤ B * M ^ m * parameterHeightWeight H k *
        R ^ (((a + b + shift * k : ℕ) : ℝ) / ((budget : ℝ) + 1)) := by
  obtain ⟨B, hB, hb⟩ := n04Realization_finiteProduct_scale_bound (X := X) m k a b RH
  refine ⟨B, hB, ?_⟩
  intro U hU Ω hΩ f F q hq J x hx P v hv H M R hH hHR hM hR budget shift hraw
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  let α : ℝ := (shift : ℝ) / ((budget : ℝ) + 1)
  let t : ℝ := R ^ (1 / ((budget : ℝ) + 1))
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have htpow (n : ℕ) : t ^ n = R ^ ((n : ℝ) / ((budget : ℝ) + 1)) := by
    dsimp only [t]
    rw [← Real.rpow_mul_natCast hRpos.le]
    congr 1
    ring
  have hcancel (w : X) : R ^ α • (R ^ (-α) • w) = w := by
    rw [smul_smul, ← Real.rpow_add hRpos, add_neg_cancel, Real.rpow_zero, one_smul]
  have hcancel' (w : X) : R ^ (-α) • (R ^ α • w) = w := by
    rw [smul_smul, ← Real.rpow_add hRpos, neg_add_cancel, Real.rpow_zero, one_smul]
  let P' : X → Prop := fun w => P (R ^ α • w)
  let v' : Fin k → X := fun i => R ^ (-α) • v i
  have hv' (i : Fin k) : P' (v' i) := by
    change P (R ^ α • (R ^ (-α) • v i))
    rw [hcancel]
    exact hv i
  have hraw' (i : Fin m) (j : ℕ) (hj : j ≤ k) (u w : ℕ) (huw : u + w ≤ a + b)
      (z : Fin j → X) (hz : ∀ l, P' (z l)) :
      ‖((F i).parameter u w q hq).D j x z‖ ≤
        M * parameterHeightWeight H j * t ^ (u + w) := by
    let z₀ : Fin j → X := fun l => R ^ α • z l
    have hz₀ (l : Fin j) : P (z₀ l) := hz l
    have hr := hraw i j hj u w huw z₀ hz₀
    have hexp : (((u + w + shift * j : ℕ) : ℝ) / ((budget : ℝ) + 1)) =
        ((u + w : ℕ) : ℝ) / ((budget : ℝ) + 1) + α * (j : ℝ) := by
      dsimp only [α]
      push_cast
      ring
    rw [hexp] at hr
    have hs := n04Realization_parameter_rescale_bound (((F i).parameter u w q hq).D j x)
      z₀ hRpos α (((u + w : ℕ) : ℝ) / ((budget : ℝ) + 1))
      (M * parameterHeightWeight H j) hr
    have hz_eq : (fun l => R ^ (-α) • z₀ l) = z := by
      funext l
      exact hcancel' (z l)
    rw [hz_eq] at hs
    rw [htpow]
    exact hs
  have hs := hb U hU Ω hΩ f F q hq J x hx P' v' hv'
    H M t hH hHR hM ht hraw'
  rw [htpow] at hs
  have hout := n04Realization_parameter_unscale_bound (J.D k x) v hRpos α
    (((a + b : ℕ) : ℝ) / ((budget : ℝ) + 1))
    (B * M ^ m * parameterHeightWeight H k) hs
  have hexp : (((a + b : ℕ) : ℝ) / ((budget : ℝ) + 1)) + α * (k : ℝ) =
      (((a + b + shift * k : ℕ) : ℝ) / ((budget : ℝ) + 1)) := by
    dsimp only [α]
    push_cast
    ring
  rw [hexp] at hout
  exact hout

/-- A complete finite product is normalized once, retaining one high
seminorm and the height gain at every positive parameter order. -/
theorem n04NegativeHeight_product_positive_oneHigh (m K s shift : ℕ) (RH : ℝ) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (p : ℕ → Seminorm ℝ X) (center : X) (base high : ℕ),
      ∀ (U : Set X), IsOpen U → ∀ (Ω : Set PolarPoint), IsOpen Ω →
      ∀ f : Fin m → X → PolarPoint → ℝ,
      ∀ F : ∀ i, MixedJetRegularity U Ω (f i), ∀ q (hq : q ∈ Ω),
      ∀ H M : ℝ, 0 ≤ H → H ≤ RH → 1 ≤ M →
      ∀ x ∈ U, p base (x - center) ≤ 1 →
      (∀ i : Fin m, ∀ j : ℕ, j ≤ K → ∀ u w : ℕ, u + w ≤ s →
        ∀ z : Fin j → X, (∀ l, p base (z l) ≤ 1) →
        ∀ R : ℝ, 1 ≤ R → p high (x - center) ≤ R → (∀ l, p high (z l) ≤ R) →
        ‖((F i).parameter u w q hq).D j x z‖ ≤ M * parameterHeightWeight H j *
          R ^ (((u + w + shift * j : ℕ) : ℝ) /
            (((s + shift * K : ℕ) : ℝ) + 1))) →
      ∀ k : ℕ, k ≤ K → 0 < k → ∀ a b : ℕ, a + b ≤ s →
      ∀ J : SmoothDirections U (fun y => mixedDerivative a b (fun z => ∏ i, f i y z) q),
      ∀ v : Fin k → X, ‖J.D k x v‖ ≤ B * M ^ m * H *
        oneHighVariationWeight p base high (x - center) v := by
  classical
  let I : Type := Fin (K + 1) × Fin (s + 1) × Fin (s + 1)
  choose c hc hb using fun i : I =>
    n04NegativeHeight_product_shifted_bound (X := X) m i.1.val i.2.1.val i.2.2.val RH
  let B : ℝ := 1 + ∑ i : I, c i
  have hB : 0 < B := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun i _ => (hc i).le))
  have hcB (i : I) : c i ≤ B :=
    (Finset.single_le_sum (fun j _ => (hc j).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨B, hB, ?_⟩
  intro p center base high U hU Ω hΩ f F q hq H M hH hHR hM x hx hlow hraw
    k hk hkpos a b hab J
  let i : I := (⟨k, Nat.lt_succ_of_le hk⟩, ⟨a, by omega⟩, ⟨b, by omega⟩)
  let C : ℝ := B * M ^ m * H
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg hB.le (pow_nonneg (zero_le_one.trans hM) _)) hH
  have hn := multilinear_bound_of_unitBall (J.D k x) (normSeminorm ℝ ℝ)
    (p base) (p high) hC (a := 1 + p high (x - center)) (fun v hv => by
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
      let P : X → Prop := fun w => p base w ≤ 1 ∧ p high w ≤ R
      have hvP (t : Fin k) : P (v t) := ⟨(hv t).le, hvR t⟩
      have hr := hb i U hU Ω hΩ f F q hq J x hx P v hvP
        H M R hH hHR hM hR (s + shift * K) shift
        (fun l j hj u w huw z hz => hraw l j (hj.trans hk) u w (huw.trans hab) z
          (fun t => (hz t).1) R hR hxR (fun t => (hz t).2))
      have hr' : ‖J.D k x v‖ ≤ (c i * M ^ m * H) *
          R ^ (((a + b + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
        simpa only [i, parameterHeightWeight, if_neg (Nat.ne_of_gt hkpos)] using hr
      have hcoef : c i * M ^ m * H ≤ C :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hcB i) (pow_nonneg (zero_le_one.trans hM) _)) hH
      have hbudget : a + b + shift * k ≤ s + shift * K := by
        have hmul := Nat.mul_le_mul_left shift hk
        omega
      have hpow := Real.rpow_le_self_of_one_le hR (spatialOrder_fraction_le_one hbudget)
      have hbound : ‖J.D k x v‖ ≤ C * R := hr'.trans
        ((mul_le_mul_of_nonneg_right hcoef
          (Real.rpow_nonneg (zero_le_one.trans hR) _)).trans
            (mul_le_mul_of_nonneg_left hpow hC))
      simpa only [coe_normSeminorm, R] using hbound)
  simpa only [coe_normSeminorm, multilinearTameSize, oneHighVariationWeight, C] using hn

end ContinuousFlexibility.Analysis
