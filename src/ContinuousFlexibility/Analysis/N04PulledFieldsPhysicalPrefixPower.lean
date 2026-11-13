import ContinuousFlexibility.Analysis.N04RealizationFixedBasePrefix
import ContinuousFlexibility.Analysis.N01cMixedPowerBounds
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# Physical prefixes with parameter-order losses

A single low grading controls every parameter order. Its loss sequence
may grow with that order. Interpolation assigns this growth to one finite
prefix offset, chosen before the spatial top order. In particular, a
high parameter derivative at spatial order zero need not have zero power.
The sampled height factor is retained at every positive parameter order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {X ι : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]

/-- A fixed-base one-high certificate gives the physical prefix used in
moving-point composition, including its necessary parameter-order offset.
The family may contain every piece, coefficient, and physical point. -/
theorem n04PulledFields_physicalPrefix_of_oneHigh
    {U : Set X} (T : ∀ k : ℕ, ι → ℕ → ℕ → X → (Fin k → X) → ℝ)
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (hI : HasInterpolation p)
    (requestedBase : ℕ) (L : ℕ → ℕ) (E H : ι → ℝ)
    (hE : ∀ i, 1 ≤ E i) (hH : ∀ i, 0 ≤ H i)
    (hjet : ∀ k s : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ i a b, a + b ≤ s → ∀ x ∈ U, ∀ v : Fin k → X,
        |T k i a b x v| ≤ A * E i ^ A * parameterHeightWeight (H i) k *
          oneHighVariationWeight p requestedBase (s + L k) x v) :
    ∃ base : ℕ, requestedBase ≤ base ∧ ∀ K : ℕ, ∃ offset : ℕ,
      ∀ top : ℕ, ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ k : ℕ, k ≤ K → ∀ a b : ℕ, a + b ≤ top →
      ∀ i x, x ∈ U → p base x ≤ 1 → ∀ v : Fin k → X,
      (∀ d, p base (v d) ≤ 1) → ∀ R : ℝ, 1 ≤ R →
      p (top + (base + offset + 1)) x ≤ R →
      (∀ d, p (top + (base + offset + 1)) (v d) ≤ R) →
        |T k i a b x v| ≤ C * E i ^ A * parameterHeightWeight (H i) k *
          (R ^ (1 / ((top : ℝ) + 1))) ^ (a + b + offset) := by
  classical
  obtain ⟨base, hbase, hprefix⟩ :=
    n04Realization_fixedBase_prefix_power p hp hI requestedBase L
  refine ⟨base, hbase, fun K => ?_⟩
  obtain ⟨shift, hshift⟩ := hprefix K
  refine ⟨shift * K, fun top => ?_⟩
  obtain ⟨C₀, hC₀, hpower⟩ := hshift top
  let I := Fin (K + 1) × Fin (top + 1)
  let A : I → ℝ := fun j => (hjet j.1.val j.2.val).choose
  have hA (j : I) : 0 < A j := (hjet j.1.val j.2.val).choose_spec.1
  let A₀ : ℝ := 1 + ∑ j : I, A j
  have hA₀ : 0 < A₀ := by
    have hs : 0 ≤ ∑ j : I, A j := Finset.sum_nonneg (fun j _ => (hA j).le)
    dsimp only [A₀]
    linarith
  have hAA (j : I) : A j ≤ A₀ :=
    (Finset.single_le_sum (fun l _ => (hA l).le) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_left zero_le_one)
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack (A₀ * C₀) A₀
  refine ⟨1 + B, B, le_add_of_nonneg_right hB.le, hB.le, ?_⟩
  intro k hk a b hab i x hx hxlow v hvlow R hR hxhigh hvhigh
  let j : I := (⟨k, Nat.lt_succ_of_le hk⟩, ⟨a + b, Nat.lt_succ_of_le hab⟩)
  have hindex : base + top + shift * K + 1 = top + (base + shift * K + 1) := by omega
  have hw := hpower k hk (a + b) hab x hxlow v hvlow R hR
    (by simpa only [hindex] using hxhigh)
    (fun d => by simpa only [hindex] using hvhigh d)
  have hweight : oneHighVariationWeight p requestedBase (a + b + L k) x v ≤
      oneHighVariationWeight p base (a + b + L k) x v :=
    oneHighVariationWeight_mono hp hbase le_rfl x v
  have hexponent : ((a + b + shift * k : ℕ) : ℝ) /
      (((top + shift * K : ℕ) : ℝ) + 1) ≤
      ((a + b + shift * K : ℕ) : ℝ) / ((top : ℝ) + 1) := by
    calc
      _ ≤ ((a + b + shift * K : ℕ) : ℝ) /
          (((top + shift * K : ℕ) : ℝ) + 1) :=
        div_le_div_of_nonneg_right
          (by exact_mod_cast Nat.add_le_add_left (Nat.mul_le_mul_left shift hk) (a + b))
          (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
        (by exact_mod_cast Nat.add_le_add_right (Nat.le_add_right top (shift * K)) 1)
  have hw' : oneHighVariationWeight p requestedBase (a + b + L k) x v ≤
      C₀ * R ^ (((a + b + shift * K : ℕ) : ℝ) / ((top : ℝ) + 1)) :=
    (hweight.trans hw).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hR hexponent) (zero_le_one.trans hC₀))
  have hcoef : A j * E i ^ A j * C₀ ≤ (1 + B) * E i ^ B := by
    calc
      _ ≤ A₀ * E i ^ A₀ * C₀ := mul_le_mul_of_nonneg_right
        (mul_le_mul (hAA j) (Real.rpow_le_rpow_of_exponent_le (hE i) (hAA j))
          (Real.rpow_nonneg (zero_le_one.trans (hE i)) _) hA₀.le)
        (zero_le_one.trans hC₀)
      _ = (A₀ * C₀) * E i ^ A₀ := by ring
      _ ≤ B * E i ^ B := hpack (E i) (hE i)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
        (Real.rpow_nonneg (zero_le_one.trans (hE i)) _)
  have hheight : 0 ≤ parameterHeightWeight (H i) k := parameterHeightWeight_nonneg (hH i) k
  have hfactor : 0 ≤ A j * E i ^ A j * parameterHeightWeight (H i) k :=
    mul_nonneg (mul_nonneg (hA j).le (Real.rpow_nonneg (zero_le_one.trans (hE i)) _)) hheight
  have hraw : |T k i a b x v| ≤
      A j * E i ^ A j * parameterHeightWeight (H i) k *
        oneHighVariationWeight p requestedBase (a + b + L k) x v :=
    (hjet k (a + b)).choose_spec.2 i a b le_rfl x hx v
  have hnatpower : R ^ (((a + b + shift * K : ℕ) : ℝ) / ((top : ℝ) + 1)) =
      (R ^ (1 / ((top : ℝ) + 1))) ^ (a + b + shift * K) := by
    rw [← Real.rpow_mul_natCast (zero_le_one.trans hR)]
    congr 1
    ring
  calc
    |T k i a b x v| ≤ A j * E i ^ A j * parameterHeightWeight (H i) k *
        (C₀ * R ^ (((a + b + shift * K : ℕ) : ℝ) / ((top : ℝ) + 1))) :=
      hraw.trans (mul_le_mul_of_nonneg_left hw' hfactor)
    _ = (A j * E i ^ A j * C₀) * parameterHeightWeight (H i) k *
        R ^ (((a + b + shift * K : ℕ) : ℝ) / ((top : ℝ) + 1)) := by ring
    _ ≤ ((1 + B) * E i ^ B) * parameterHeightWeight (H i) k *
        R ^ (((a + b + shift * K : ℕ) : ℝ) / ((top : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hheight)
        (Real.rpow_nonneg (zero_le_one.trans hR) _)
    _ = _ := by rw [hnatpower]

end ContinuousFlexibility.Analysis
