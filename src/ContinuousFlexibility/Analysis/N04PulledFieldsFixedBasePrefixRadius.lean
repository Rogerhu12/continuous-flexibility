import ContinuousFlexibility.Analysis.N04RealizationFixedBasePrefix

/-!
# Fixed-base affine prefixes on arbitrary low-order balls

The interpolation base depends only on the zeroth parameter loss.
Positive parameter losses are paid once per parameter slot. The radius
of the low-order ball affects only the numerical coefficient, while the
power denominator remains the chosen spatial top plus one.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]

theorem n04PulledFields_fixedBase_affine_prefix_power
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (hI : HasInterpolation p)
    (requestedBase : ℕ) (L : ℕ → ℕ) :
    ∃ base : ℕ, requestedBase ≤ base ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ A : ℝ, 0 ≤ A → ∀ s : ℕ, ∃ C : ℝ, 1 ≤ C ∧
      ∀ k : ℕ, k ≤ K → ∀ n : ℕ, n ≤ s →
      ∀ x : X, p base x ≤ A → ∀ v : Fin k → X,
      (∀ i, p base (v i) ≤ 1) → ∀ R : ℝ, 1 ≤ R →
      p (base + s + shift * K + 1) x ≤ R →
      (∀ i, p (base + s + shift * K + 1) (v i) ≤ R) →
      (1 + p (n + L k) x) + (∑ i, p (n + L k) (v i)) ≤
        C * R ^ (((n + shift * k : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  classical
  obtain ⟨b₀, ℓ, hi⟩ := hI
  let base : ℕ := max requestedBase (max b₀ (L 0 + ℓ))
  have hbase : b₀ ≤ base := (le_max_left _ _).trans (le_max_right _ _)
  have hzero : L 0 + ℓ ≤ base := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨base, le_max_left _ _, fun K => ?_⟩
  let shift : ℕ := 1 + ∑ j : Fin (K + 1), (L j.val + ℓ)
  have hshift (k : ℕ) (hk : k ≤ K) : L k + ℓ ≤ shift := by
    have hterm : L k + ℓ ≤ ∑ j : Fin (K + 1), (L j.val + ℓ) :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (L j.val + ℓ))
        (Finset.mem_univ (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (K + 1)))
    exact hterm.trans (Nat.le_add_left _ _)
  refine ⟨shift, fun A hA s => ?_⟩
  let high : ℕ := base + s + shift * K + 1
  have hhigh : base < high := by dsimp only [high]; omega
  have horder (k : ℕ) (hk : k ≤ K) (n : ℕ) (hn : n ≤ s) :
      base < n + L k → n + L k + ℓ < high := by
    intro _
    by_cases hk0 : k = 0
    · subst k
      dsimp only [high]
      omega
    · have hkpos : 1 ≤ k := Nat.pos_of_ne_zero hk0
      have hshiftk : shift ≤ shift * k := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left shift hkpos
      have hshiftK : shift * k ≤ shift * K := Nat.mul_le_mul_left shift hk
      have hL := hshift k hk
      dsimp only [high]
      omega
  have hcost (k : ℕ) (hk : k ≤ K) (n : ℕ) :
      interpolationOrderCost base ℓ (n + L k) ≤ n + shift * k := by
    unfold interpolationOrderCost
    split_ifs with hn
    · by_cases hk0 : k = 0
      · subst k
        simp only [Nat.mul_zero, Nat.add_zero]
        omega
      · have hkpos : 1 ≤ k := Nat.pos_of_ne_zero hk0
        have hshiftk : shift ≤ shift * k := by
          simpa only [Nat.mul_one] using Nat.mul_le_mul_left shift hkpos
        have hL := hshift k hk
        omega
    · exact Nat.zero_le _
  let I : Type := Fin (K + 1) × Fin (s + 1)
  choose c hc hcb using fun i : I =>
    interpolation_affine_family_le_common_scale p hp base ℓ
      (i.2.val + L i.1.val) high hhigh
      (horder i.1.val (Nat.le_of_lt_succ i.1.isLt)
        i.2.val (Nat.le_of_lt_succ i.2.isLt))
      (fun b c hb hbc => hi base b c hbase hb hbc) A hA i.1.val
  let C : ℝ := 1 + ∑ i : I, c i
  have hC : 1 ≤ C := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun i _ => hc i))
  have hcC (i : I) : c i ≤ C :=
    (Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨C, hC, ?_⟩
  intro k hk n hn x hx v hv R hR hxR hvR
  let i : I := (⟨k, Nat.lt_succ_of_le hk⟩, ⟨n, Nat.lt_succ_of_le hn⟩)
  have h := hcb i x v R hx hv hxR hvR hR
  have hden : (high : ℝ) - base = (((s + shift * K : ℕ) : ℝ) + 1) := by
    dsimp only [high]
    push_cast
    ring
  change (1 + p (n + L k) x) + ∑ j, p (n + L k) (v j) ≤
    c i * R ^ ((interpolationOrderCost base ℓ (n + L k) : ℝ) /
      ((high : ℝ) - base)) at h
  rw [hden] at h
  have hexp : (interpolationOrderCost base ℓ (n + L k) : ℝ) /
      (((s + shift * K : ℕ) : ℝ) + 1) ≤
      ((n + shift * k : ℕ) : ℝ) / ((s : ℝ) + 1) := by
    calc
      _ ≤ ((n + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hcost k hk n) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
        (by exact_mod_cast Nat.add_le_add_right (Nat.le_add_right s (shift * K)) 1)
  exact h.trans
    ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR hexp) (hc i)).trans
      (mul_le_mul_of_nonneg_right (hcC i)
        (Real.rpow_nonneg (zero_le_one.trans hR) _)))

end ContinuousFlexibility.Analysis
