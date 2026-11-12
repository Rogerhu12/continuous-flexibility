import ContinuousFlexibility.Analysis.N04RealizationPositiveHeightParameterPrefix
import ContinuousFlexibility.Analysis.N01cMixedPowerNormalization

/-!
# One high seminorm for the actual positive Taylor height

The retained finite raw endpoint bounds are sufficient for both the
height and reciprocal. The finite parameter cost enters the high order
only. The actual output map is normalized once, retaining one height
factor and the original low order, collar, and parameter neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem n04Realization_positiveHeightTaylor_positive_oneHigh
    (n K s shift : ℕ) (RH : ℝ) :
    ∃ B : ℝ, ∃ d : ℕ, 1 ≤ B ∧ 1 ≤ d ∧
      ∀ (p : ℕ → Seminorm ℝ X) (center : X) (base high : ℕ),
      ∀ (U : Set X), IsOpen U → ∀ l r δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ h : X → Bool → PolarPoint → ℝ,
      (∀ y ∈ U, ∀ side θ, ContDiffAt ℝ ∞ (h y side) (if side then r else l, θ)) →
      (∀ y ∈ U, ∀ side θ, 0 < h y side (if side then r else l, θ)) →
      ∀ JH : ∀ side, ∀ j : ℕ, j ≤ n → ∀ u θ,
        SmoothDirections U (fun y => iteratedDeriv u
          (radialBoundaryJet (h y side) (if side then r else l) j) θ),
      ∀ H M : ℝ, 0 ≤ H → H ≤ RH → 1 ≤ M → δ⁻¹ ≤ M →
      ∀ x ∈ U, p base (x - center) ≤ 1 →
      (∀ side θ, (h x side (if side then r else l, θ))⁻¹ ≤ M) →
      (∀ side, ∀ j : ℕ, ∀ hj : j ≤ n, ∀ e : ℕ, e ≤ K →
        ∀ u : ℕ, u ≤ s → ∀ θ, ∀ z : Fin e → X,
        (∀ i, p base (z i) ≤ 1) →
        ∀ R : ℝ, 1 ≤ R → p high (x - center) ≤ R → (∀ i, p high (z i) ≤ R) →
        ‖(JH side j hj u θ).D e x z‖ ≤ M * parameterHeightWeight H e *
          R ^ (((u + shift * e : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1))) →
      ∀ Mlow : ℝ, 0 ≤ Mlow →
      (∀ side j, 0 < j → j ≤ n → ∀ θ,
        |positiveHeightTaylorData l r (fun _ => 1) (h x) side j θ| ≤ Mlow) →
      ((n + 1 : ℕ) : ℝ) * Mlow * δ ≤ 1 →
      ∀ k : ℕ, k ≤ K → 0 < k → ∀ a b : ℕ, a + b ≤ s →
      ∀ inv : Bool, ∀ q : PolarPoint, ∀ J : SmoothDirections U
        (fun y => mixedDerivative a b (fun z => if inv then
          (positiveHeightTaylorInterpolation n l r δ (fun _ => 1) (h y) z)⁻¹
          else positiveHeightTaylorInterpolation n l r δ (fun _ => 1) (h y) z) q),
      ∀ v : Fin k → X, ‖J.D k x v‖ ≤ B * M ^ d * H *
        oneHighVariationWeight p base high (x - center) v := by
  classical
  let I : Type := Fin (K + 1) × Fin (s + 1) × Fin (s + 1)
  choose c d hc hd hb using fun i : I =>
    n04Realization_positiveHeightTaylor_shifted_parameter_bound (X := X)
      n i.1.val i.2.1.val i.2.2.val RH
  let B : ℝ := 1 + ∑ i : I, c i
  let D : ℕ := 1 + ∑ i : I, d i
  have hB : 1 ≤ B := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun i _ => zero_le_one.trans (hc i)))
  have hD : 1 ≤ D := Nat.le_add_right _ _
  have hcB (i : I) : c i ≤ B :=
    (Finset.single_le_sum (fun j _ => zero_le_one.trans (hc j)) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hdD (i : I) : d i ≤ D :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)).trans
      (Nat.le_add_left _ _)
  refine ⟨B, D, hB, hD, ?_⟩
  intro p center base high U hU l r δ hδ hδ1 h hroot hpos JH H M hH hHR hM hδM
    x hx hlow hinv hraw Mlow hMlow hTaylor hsmall k hk hkpos a b hab inv q J
  let i : I := (⟨k, Nat.lt_succ_of_le hk⟩, ⟨a, by omega⟩, ⟨b, by omega⟩)
  let C : ℝ := B * M ^ D * H
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg (zero_le_one.trans hB) (pow_nonneg (zero_le_one.trans hM) _)) hH
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
      have hr := hb i U hU l r δ hδ hδ1 h hroot hpos JH x hx P v hvP
        H M R hH hHR hM hR hδM (s + shift * K) shift hinv
        (fun side j hj e he u hu θ z hz =>
          hraw side j hj e (he.trans hk) u (hu.trans hab) θ z
            (fun t => (hz t).1) R hR hxR (fun t => (hz t).2))
        Mlow hMlow hTaylor hsmall inv q J
      have hr' : ‖J.D k x v‖ ≤ (c i * M ^ d i * H) *
          R ^ (((a + b + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
        simpa only [i, parameterHeightWeight, if_neg (Nat.ne_of_gt hkpos)] using hr
      have hcoef : c i * M ^ d i * H ≤ C :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (hcB i) (pow_le_pow_right₀ hM (hdD i))
            (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hB)) hH
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
