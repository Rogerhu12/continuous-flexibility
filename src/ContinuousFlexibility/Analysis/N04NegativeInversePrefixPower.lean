import ContinuousFlexibility.Analysis.JointJetInterpolationBudget
import ContinuousFlexibility.Analysis.TameMultilinearNormalization
import ContinuousFlexibility.Statements.Nonlinear
import ContinuousFlexibility.Analysis.N04RealizationFullWeightProductOneHigh
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# One saved spatial derivative in finite inverse prefixes

Increasing the fixed low order once saves one spatial derivative in
every positive joint order. This is the exact degree used by the
implicit inverse recursion. The base is chosen before the parameter
prefix; the positive parameter losses change only the prefix shift.

The scalar adapter preserves the complete external weight, including
the sampled height factor at every positive parameter order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]

theorem n04NegativeInverse_fixedBase_prefix_power
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (hI : HasInterpolation p)
    (requestedBase : ℕ) (L : ℕ → ℕ) :
    ∃ base : ℕ, requestedBase ≤ base ∧ ∀ K : ℕ, ∃ shift : ℕ, 1 ≤ shift ∧
      ∀ s : ℕ, ∃ C : ℝ, 1 ≤ C ∧
      ∀ k : ℕ, k ≤ K → ∀ n : ℕ, n ≤ s →
      ∀ x : X, p base x ≤ 1 → ∀ v : Fin k → X,
      (∀ i, p base (v i) ≤ 1) → ∀ R : ℝ, 1 ≤ R →
      p (base + s + shift * K + 1) x ≤ R →
      (∀ i, p (base + s + shift * K + 1) (v i) ≤ R) →
      oneHighVariationWeight p base (n + L k) x v ≤
        C * R ^ (((n + shift * k - 1 : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
  classical
  obtain ⟨b₀, ℓ, hi⟩ := hI
  let base : ℕ := max requestedBase (max b₀ (L 0 + ℓ + 1))
  have hbase : b₀ ≤ base := (le_max_left _ _).trans (le_max_right _ _)
  have hzero : L 0 + ℓ + 1 ≤ base := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨base, le_max_left _ _, fun K => ?_⟩
  let shift : ℕ := 1 + ∑ j : Fin (K + 1), (L j.val + ℓ + 1)
  have hshift (k : ℕ) (hk : k ≤ K) : L k + ℓ + 1 ≤ shift := by
    have hterm : L k + ℓ + 1 ≤ ∑ j : Fin (K + 1), (L j.val + ℓ + 1) :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (L j.val + ℓ + 1))
        (Finset.mem_univ (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (K + 1)))
    exact hterm.trans (Nat.le_add_left _ _)
  refine ⟨shift, by dsimp only [shift]; omega, fun s => ?_⟩
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
      interpolationOrderCost base ℓ (n + L k) ≤ n + shift * k - 1 := by
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
      (fun b c hb hbc => hi base b c hbase hb hbc) 1 zero_le_one i.1.val
  let C : ℝ := 1 + ∑ i : I, c i
  have hC : 1 ≤ C := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun i _ => hc i))
  have hcC (i : I) : c i ≤ C :=
    (Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨C, hC, ?_⟩
  intro k hk n hn x hx v hv R hR hxR hvR
  let i : I := (⟨k, Nat.lt_succ_of_le hk⟩, ⟨n, Nat.lt_succ_of_le hn⟩)
  have ha : oneHighVariationWeight p base (n + L k) x v ≤
      (1 + p (n + L k) x) + ∑ j, p (n + L k) (v j) := by
    simpa only [oneHighVariationWeight, multilinearTameSize] using
      multilinearTameSize_le_affine (p base) (p (n + L k)) k
        (by positivity : 0 ≤ 1 + p (n + L k) x) v hv
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
      ((n + shift * k - 1 : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1) :=
    div_le_div_of_nonneg_right (by exact_mod_cast hcost k hk n) (by positivity)
  exact ha.trans (h.trans
    ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR hexp) (hc i)).trans
      (mul_le_mul_of_nonneg_right (hcC i)
        (Real.rpow_nonneg (zero_le_one.trans hR) _))))

open Set
open scoped ContDiff

variable {I : Type*}
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Convert a tower with order-dependent losses into fractional raw
bounds on each finite prefix, preserving its entire external weight. -/
theorem n04NegativeInverse_scalar_prefix_power
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (hI : HasInterpolation p)
    (oldBase : ℕ) (L : ℕ → ℕ)
    {U : Set X} {Ω : Set PolarPoint}
    (E : I → ℝ) (W : ℕ → I → ℝ)
    (hE : ∀ t, 1 ≤ E t) (hW : ∀ k t, 0 ≤ W k t)
    (f : I → X → PolarPoint → ℝ)
    (RF : ∀ t, MixedJetRegularity U Ω (f t))
    (hbound : ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ t q (hq : q ∈ Ω) a b, a + b ≤ s →
      ∀ x ∈ U, ∀ v : Fin k → X,
        |((RF t).parameter a b q hq).D k x v| ≤
          B * E t ^ B * W k t * oneHighVariationWeight p oldBase (s + L k) x v) :
    ∃ base : ℕ, oldBase ≤ base ∧ ∀ K : ℕ, ∃ shift : ℕ, 1 ≤ shift ∧ ∀ s : ℕ,
      ∃ B : ℝ, 0 < B ∧ ∀ k, k ≤ K → ∀ t q (hq : q ∈ Ω) a b,
      a + b ≤ s → ∀ x ∈ U, p base x ≤ 1 →
      ∀ v : Fin k → X, (∀ i, p base (v i) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → p (base + s + shift * K + 1) x ≤ R →
        (∀ i, p (base + s + shift * K + 1) (v i) ≤ R) →
        |((RF t).parameter a b q hq).D k x v| ≤
          B * E t ^ B * W k t *
            R ^ (((a + b + shift * k - 1 : ℕ) : ℝ) /
              (((s + shift * K : ℕ) : ℝ) + 1)) := by
  classical
  obtain ⟨base, hbase, hprefix⟩ := n04NegativeInverse_fixedBase_prefix_power p hp hI oldBase L
  refine ⟨base, hbase, fun K => ?_⟩
  obtain ⟨shift, hshiftOne, hshift⟩ := hprefix K
  refine ⟨shift, hshiftOne, fun s => ?_⟩
  let J := Fin (K + 1) × Fin (s + 1)
  choose c hc hb using fun j : J => hbound j.1.val j.2.val
  let A : ℝ := 1 + ∑ j : J, c j
  have hsum : 0 ≤ ∑ j : J, c j := Finset.sum_nonneg (fun j _ => (hc j).le)
  have hA : 0 < A := by dsimp only [A]; linarith
  have hcA (j : J) : c j ≤ A :=
    (Finset.single_le_sum (fun j _ => (hc j).le) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_left zero_le_one)
  obtain ⟨C, hC, hCb⟩ := hshift s
  obtain ⟨B, hB, hBb⟩ := coefficientEnvelope_pack (A * C) A
  refine ⟨B, hB, ?_⟩
  intro k hk t q hq a b hab x hx hlow v hv R hR hxR hvR
  let j : J := (⟨k, Nat.lt_succ_of_le hk⟩, ⟨a + b, Nat.lt_succ_of_le hab⟩)
  have hcoef : c j * E t ^ c j ≤ A * E t ^ A :=
    mul_le_mul (hcA j) (Real.rpow_le_rpow_of_exponent_le (hE t) (hcA j))
      (Real.rpow_nonneg (zero_le_one.trans (hE t)) _) hA.le
  have hraw := (hb j t q hq a b le_rfl x hx v).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (hW k t))
      (oneHighVariationWeight_nonneg p oldBase (a + b + L k) x v))
  have hpower := (oneHighVariationWeight_mono hp hbase le_rfl x v).trans
    (hCb k hk (a + b) hab x hlow v hv R hR hxR hvR)
  have hcost : 0 ≤ A * E t ^ A * W k t :=
    mul_nonneg (mul_nonneg hA.le (Real.rpow_nonneg (zero_le_one.trans (hE t)) _)) (hW k t)
  calc
    _ ≤ A * E t ^ A * W k t *
        oneHighVariationWeight p oldBase (a + b + L k) x v := hraw
    _ ≤ A * E t ^ A * W k t *
        (C * R ^ (((a + b + shift * k - 1 : ℕ) : ℝ) /
          (((s + shift * K : ℕ) : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hpower hcost
    _ = (A * C) * E t ^ A * W k t *
        R ^ (((a + b + shift * k - 1 : ℕ) : ℝ) /
          (((s + shift * K : ℕ) : ℝ) + 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hBb (E t) (hE t)) (hW k t))
      (Real.rpow_nonneg (zero_le_one.trans hR) _)

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeInverse_scalar_prefix_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeInverse_scalar_prefix_power
