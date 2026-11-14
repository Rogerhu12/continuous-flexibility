module

public import ContinuousFlexibility.Analysis.N04RealizationFixedBasePrefix
public import ContinuousFlexibility.Analysis.N04RealizationFullWeightProductOneHigh
public import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# Interpolation of a finite prefix of current scalar towers

The external weight may depend on the parameter order. This includes
the weight which is one at order zero and the sampled height at every
positive order. The low order is fixed before the prefix is chosen.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X I : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Convert a tower with order-dependent losses into fractional raw
bounds on each finite prefix, preserving its entire external weight. -/
theorem n04SourceColumns_prefix_power
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
    ∃ base : ℕ, oldBase ≤ base ∧ ∀ K : ℕ, ∃ shift : ℕ, ∀ s : ℕ,
      ∃ B : ℝ, 0 < B ∧ ∀ k, k ≤ K → ∀ t q (hq : q ∈ Ω) a b,
      a + b ≤ s → ∀ x ∈ U, p base x ≤ 1 →
      ∀ v : Fin k → X, (∀ i, p base (v i) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → p (base + s + shift * K + 1) x ≤ R →
        (∀ i, p (base + s + shift * K + 1) (v i) ≤ R) →
        |((RF t).parameter a b q hq).D k x v| ≤
          B * E t ^ B * W k t *
            R ^ (((a + b + shift * k : ℕ) : ℝ) /
              (((s + shift * K : ℕ) : ℝ) + 1)) := by
  classical
  obtain ⟨base, hbase, hprefix⟩ := n04Realization_fixedBase_prefix_power p hp hI oldBase L
  refine ⟨base, hbase, fun K => ?_⟩
  obtain ⟨shift, hshift⟩ := hprefix K
  refine ⟨shift, fun s => ?_⟩
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
        (C * R ^ (((a + b + shift * k : ℕ) : ℝ) /
          (((s + shift * K : ℕ) : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hpower hcost
    _ = (A * C) * E t ^ A * W k t *
        R ^ (((a + b + shift * k : ℕ) : ℝ) /
          (((s + shift * K : ℕ) : ℝ) + 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hBb (E t) (hE t)) (hW k t))
      (Real.rpow_nonneg (zero_le_one.trans hR) _)

end ContinuousFlexibility.Analysis
