import ContinuousFlexibility.Analysis.N04PrincipalNegativeReciprocalFinite
import ContinuousFlexibility.Analysis.N01cMixedPowerNormalization

/-!
# One high seminorm for reciprocal jets

All spatial orders in a finite prefix share one scalar envelope.
Normalization is applied to the complete reciprocal jet, after scalar
composition has retained the additive spatial and parameter orders.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem n04PrincipalNegative_reciprocal_oneHigh (k s shift : ℕ) :
    ∃ B : ℝ, ∃ d : ℕ, 1 ≤ B ∧ 1 ≤ d ∧
      ∀ (p : ℕ → Seminorm ℝ X) (base high : ℕ),
      ∀ (U : Set X), IsOpen U → ∀ (Ω : Set PolarPoint), IsOpen Ω →
      ∀ f : X → PolarPoint → ℝ, ∀ F : MixedJetRegularity U Ω f,
      (∀ y ∈ U, ∀ q ∈ Ω, f y q ≠ 0) → ∀ M : ℝ, 1 ≤ M →
      (∀ y ∈ U, ∀ q ∈ Ω, |(f y q)⁻¹| ≤ M) →
      (∀ j : ℕ, j ≤ k → ∀ u w : ℕ, u + w ≤ s →
        ∀ q (hq : q ∈ Ω), ∀ x ∈ U, p base x ≤ 1 →
        ∀ v : Fin j → X, (∀ t, p base (v t) ≤ 1) →
        ∀ R : ℝ, 1 ≤ R → p high x ≤ R → (∀ t, p high (v t) ≤ R) →
        ‖((F.parameter u w q hq).D j x v)‖ ≤
          M * R ^ (((u + w + shift * j : ℕ) : ℝ) /
            (((s + shift * k : ℕ) : ℝ) + 1))) →
      ∀ a b : ℕ, a + b ≤ s → ∀ q (hq : q ∈ Ω),
      ∀ J : SmoothDirections U
        (fun y => mixedDerivative a b (fun z => (f y z)⁻¹) q),
      ∀ x ∈ U, p base x ≤ 1 → ∀ v : Fin k → X,
        ‖J.D k x v‖ ≤ B * M ^ d * oneHighVariationWeight p base high x v := by
  classical
  let I : Type := Fin (s + 1) × Fin (s + 1)
  choose c d hc hd hcb using fun i : I =>
    n04PrincipalNegative_finiteReciprocal_shifted_bound (X := X) k i.1.val i.2.val 1
  let B : ℝ := 1 + ∑ i : I, c i
  let D : ℕ := 1 + ∑ i : I, d i
  have hB : 1 ≤ B := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun i _ => zero_le_one.trans (hc i)))
  have hcB (i : I) : c i ≤ B :=
    (Finset.single_le_sum (fun j _ => zero_le_one.trans (hc j)) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hdD (i : I) : d i ≤ D :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans
      (Nat.le_add_left _ _)
  refine ⟨B, D, hB, by dsimp only [D]; omega, ?_⟩
  intro p base high U hU Ω hΩ f F hnonzero M hM hinv hraw a b hab q hq J x hx hlow
  let i : I := (⟨a, by omega⟩, ⟨b, by omega⟩)
  let C : ℝ := B * M ^ D
  have hC : 0 ≤ C := mul_nonneg (zero_le_one.trans hB)
    (pow_nonneg (zero_le_one.trans hM) _)
  have hn := multilinear_bound_of_unitBall (J.D k x) (normSeminorm ℝ ℝ)
    (p base) (p high) hC (a := 1 + p high x) (fun v hv => by
      let R : ℝ := (1 + p high x) + ∑ t, p high (v t)
      have hsum : 0 ≤ ∑ t, p high (v t) :=
        Finset.sum_nonneg (fun _ _ => apply_nonneg _ _)
      have hR : 1 ≤ R := by dsimp only [R]; linarith [apply_nonneg (p high) x]
      have hxR : p high x ≤ R := by dsimp only [R]; linarith
      have hvR (t : Fin k) : p high (v t) ≤ R :=
        (Finset.single_le_sum (fun _ _ => apply_nonneg _ _) (Finset.mem_univ t)).trans
          (le_add_of_nonneg_left (by positivity))
      let P : X → Prop := fun z => p base z ≤ 1 ∧ p high z ≤ R
      have hvP (t : Fin k) : P (v t) := ⟨(hv t).le, hvR t⟩
      have hsource (j : ℕ) (hj : j ≤ k) (u w : ℕ) (huw : u + w ≤ a + b)
          (z : Fin j → X) (hz : ∀ t, P (z t)) :
          ‖((F.parameter u w q hq).D j x z)‖ ≤
            M * parameterHeightWeight 1 j *
              R ^ (((u + w + shift * j : ℕ) : ℝ) /
                (((s + shift * k : ℕ) : ℝ) + 1)) := by
        have hh := hraw j hj u w (huw.trans hab) q hq x hx hlow z
          (fun t => (hz t).1) R hR hxR (fun t => (hz t).2)
        simpa only [parameterHeightWeight, ite_self, mul_one] using hh
      have hh := hcb i U hU Ω hΩ f F hnonzero q hq J x hx P v hvP
        (s + shift * k) shift 1 M R (by norm_num) le_rfl hM hR
        (hinv x hx q hq) hsource
      have hraw' : ‖J.D k x v‖ ≤ c i * M ^ d i *
          R ^ (((a + b + shift * k : ℕ) : ℝ) /
            (((s + shift * k : ℕ) : ℝ) + 1)) := by
        simpa only [i, parameterHeightWeight, ite_self, mul_one] using hh
      have hcoef : c i * M ^ d i ≤ C := mul_le_mul (hcB i)
        (pow_le_pow_right₀ hM (hdD i)) (pow_nonneg (zero_le_one.trans hM) _)
        (zero_le_one.trans hB)
      have hpow := Real.rpow_le_self_of_one_le hR
        (spatialOrder_fraction_le_one (Nat.add_le_add_right hab (shift * k)))
      have hbound : ‖J.D k x v‖ ≤ C * R := hraw'.trans
        ((mul_le_mul_of_nonneg_right hcoef
          (Real.rpow_nonneg (zero_le_one.trans hR) _)).trans
            (mul_le_mul_of_nonneg_left hpow hC))
      simpa only [coe_normSeminorm, R] using hbound)
  simpa only [coe_normSeminorm, multilinearTameSize, oneHighVariationWeight, C] using hn

end ContinuousFlexibility.Analysis
