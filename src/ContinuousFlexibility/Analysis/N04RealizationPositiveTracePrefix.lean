module

public import ContinuousFlexibility.Analysis.N04RealizationLogHeightTraceBounds

/-!
# One finite envelope for both actual positive logarithmic traces

The finite radial degree and the requested angular and parameter
prefixes are collected before either endpoint family is supplied. The
original raw towers are only restricted to their required radial prefix;
no source, parameter domain or endpoint is selected again.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem n04Realization_positiveTrace_prefix_bound (n K s : ℕ) (RH : ℝ) :
    ∃ B : ℝ, ∃ d : ℕ, 1 ≤ B ∧ 1 ≤ d ∧
      ∀ (U : Set X), IsOpen U → ∀ (f : X → Bool → PolarPoint → ℝ) (c : Bool → ℝ),
      (∀ y ∈ U, ∀ side θ, ContDiffAt ℝ ∞ (f y side) (c side, θ)) →
      (∀ y ∈ U, ∀ side θ, 0 < f y side (c side, θ)) →
      ∀ J : ∀ side, ∀ j : ℕ, j ≤ n → ∀ a θ,
        SmoothDirections U (fun y => iteratedDeriv a (radialBoundaryJet (f y side) (c side) j) θ),
      ∀ x ∈ U, ∀ P : X → Prop, ∀ H M t : ℝ,
      0 ≤ H → H ≤ RH → 1 ≤ M → 1 ≤ t →
      (∀ side θ, (f x side (c side, θ))⁻¹ ≤ M) →
      (∀ side, ∀ j : ℕ, ∀ hj : j ≤ n, ∀ l : ℕ, l ≤ K → ∀ a : ℕ, a ≤ s →
        ∀ θ, ∀ z : Fin l → X, (∀ i, P (z i)) →
        ‖(J side j hj a θ).D l x z‖ ≤ M * parameterHeightWeight H l * t ^ a) →
      ∀ side, ∀ j : ℕ, j ≤ n → ∀ k : ℕ, k ≤ K → ∀ b : ℕ, b ≤ s → ∀ θ,
      ∀ JL : SmoothDirections U (fun y => iteratedDeriv b
        (radialBoundaryJet (fun p => Real.log (f y side p)) (c side) j) θ),
      ∀ v : Fin k → X, (∀ i, P (v i)) →
      ‖JL.D k x v‖ ≤ B * M ^ d * parameterHeightWeight H k * t ^ b := by
  classical
  let I : Type := Fin (n + 1) × Fin (K + 1) × Fin (s + 1)
  choose c d hc hd hb using fun i : I =>
    n04Realization_logHeightTrace_parameter_bound (X := X) i.1.val i.2.1.val i.2.2.val RH
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
  intro U hU f ends hroot hpos J x hx P H M t hH hHR hM ht hinv hraw
    side j hj k hk b hbs θ JL v hv
  let i : I := (⟨j, Nat.lt_succ_of_le hj⟩,
    ⟨k, Nat.lt_succ_of_le hk⟩, ⟨b, Nat.lt_succ_of_le hbs⟩)
  have h := hb i U hU (fun y => f y side) (ends side)
    (fun y hy η => hroot y hy side η) (fun y hy η => hpos y hy side η)
    (fun a ha => J side a (ha.trans hj)) θ JL x hx P v hv H M t
    hH hHR hM ht (hinv side θ)
    (fun a ha l hl u hu z hz => hraw side a (ha.trans hj) l (hl.trans hk)
      u (hu.trans hbs) θ z hz)
  have hcoef : c i * M ^ d i ≤ B * M ^ D :=
    mul_le_mul (hcB i) (pow_le_pow_right₀ hM (hdD i))
      (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hB)
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef (parameterHeightWeight_nonneg hH k))
    (pow_nonneg (zero_le_one.trans ht) _))

end ContinuousFlexibility.Analysis
