import ContinuousFlexibility.Analysis.N04RealizationFixedBasePrefix
import ContinuousFlexibility.Analysis.N01cMixedPowerBounds
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# Fixed-base power bounds for scalar inverse prefixes

The input is a family of genuine scalar towers. Its zeroth parameter
loss is assigned to spatial order one less than the actual spatial
order. Positive parameter losses remain in a sequence indexed by the
parameter order. The fixed-base interpolation theorem chooses the low
order once, before the finite parameter prefix is specified.

An arbitrary family index lets both inverse-coordinate atoms use one
interpolation scale. In particular, no separate choice of scale for the
radial and angular coordinates has to be compared afterwards.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]

/-- Interpolate the original scalar towers with one low order. Only the
high-order shift depends on the parameter prefix. The height factor is
retained precisely at positive parameter order. -/
theorem n04PulledFields_inversePrefix_power
    {ι : Type*} {U : Set X} {Ω : Set PolarPoint}
    {f : ι → ℕ → ℕ → Ω → X → ℝ}
    (J : ∀ i a b q, SmoothDirections U (f i a b q))
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (hI : HasInterpolation p)
    (requestedBase : ℕ) (L : ℕ → ℕ) (E H : ι → ℝ)
    (hE : ∀ i, 1 ≤ E i) (hH : ∀ i, 0 ≤ H i)
    (hjet : ∀ k s : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ i (q : Ω) (a b : ℕ), a + b = s → 0 < k + s →
      ∀ x ∈ U, ∀ v : Fin k → X,
        |(J i a b q).D k x v| ≤ A * E i ^ A * parameterHeightWeight (H i) k *
          oneHighVariationWeight p requestedBase
            ((if k = 0 then s - 1 else s) + L k) x v) :
    ∃ base : ℕ, requestedBase ≤ base ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ N : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ k : ℕ, k ≤ K → ∀ a b : ℕ, a + b ≤ N → 0 < k + (a + b) →
      ∀ i (q : Ω), ∀ x ∈ U, p base x ≤ 1 →
      ∀ v : Fin k → X, (∀ j, p base (v j) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → p (base + N + shift * K + 1) x ≤ R →
        (∀ j, p (base + N + shift * K + 1) (v j) ≤ R) →
        |(J i a b q).D k x v| ≤ B * E i ^ B * parameterHeightWeight (H i) k *
          (R ^ (1 / (((N + shift * K : ℕ) : ℝ) + 1))) ^
            (if k = 0 then a + b - 1 else a + b + shift * K) := by
  classical
  obtain ⟨base, hbase, hprefix⟩ :=
    n04Realization_fixedBase_prefix_power p hp hI requestedBase L
  refine ⟨base, hbase, fun K => ?_⟩
  obtain ⟨shift, hshift⟩ := hprefix K
  refine ⟨shift, fun N => ?_⟩
  obtain ⟨C, hC, hpower⟩ := hshift N
  let I := Fin (K + 1) × Fin (N + 1)
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
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack (A₀ * C) A₀
  refine ⟨B, hB, fun k hk a b hab hpositive i q x hx hxlow v hvlow R hR hxhigh hvhigh => ?_⟩
  let j : I := (⟨k, Nat.lt_succ_of_le hk⟩, ⟨a + b, Nat.lt_succ_of_le hab⟩)
  let r : ℕ := if k = 0 then a + b - 1 else a + b
  let e : ℕ := if k = 0 then a + b - 1 else a + b + shift * K
  have hr : r ≤ N := by dsimp only [r]; split_ifs <;> omega
  have horder : r + shift * k ≤ e := by
    by_cases hk0 : k = 0
    · simp only [r, e, hk0, if_pos rfl, Nat.mul_zero, Nat.add_zero, le_refl]
    · simpa only [r, e, if_neg hk0] using Nat.add_le_add_left (Nat.mul_le_mul_left shift hk) (a + b)
  have hweight := oneHighVariationWeight_mono hp hbase le_rfl x v
    (high := r + L k) (high' := r + L k)
  have hw := hpower k hk r hr x hxlow v hvlow R hR hxhigh hvhigh
  have hexponent : ((r + shift * k : ℕ) : ℝ) / (((N + shift * K : ℕ) : ℝ) + 1) ≤
      (e : ℝ) / (((N + shift * K : ℕ) : ℝ) + 1) :=
    div_le_div_of_nonneg_right (by exact_mod_cast horder) (by positivity)
  have hpowers := Real.rpow_le_rpow_of_exponent_le hR hexponent
  have hw' : oneHighVariationWeight p requestedBase (r + L k) x v ≤
      C * R ^ ((e : ℝ) / (((N + shift * K : ℕ) : ℝ) + 1)) :=
    (hweight.trans hw).trans (mul_le_mul_of_nonneg_left hpowers (zero_le_one.trans hC))
  have hcoef : A j * E i ^ A j * C ≤ B * E i ^ B := by
    calc
      _ ≤ A₀ * E i ^ A₀ * C := mul_le_mul_of_nonneg_right
        (mul_le_mul (hAA j) (Real.rpow_le_rpow_of_exponent_le (hE i) (hAA j))
          (Real.rpow_nonneg (zero_le_one.trans (hE i)) _) hA₀.le)
        (zero_le_one.trans hC)
      _ = (A₀ * C) * E i ^ A₀ := by ring
      _ ≤ _ := hpack (E i) (hE i)
  have hheight : 0 ≤ parameterHeightWeight (H i) k := parameterHeightWeight_nonneg (hH i) k
  have hfactor : 0 ≤ A j * E i ^ A j * parameterHeightWeight (H i) k :=
    mul_nonneg (mul_nonneg (hA j).le (Real.rpow_nonneg (zero_le_one.trans (hE i)) _)) hheight
  have hraw : |(J i a b q).D k x v| ≤
      A j * E i ^ A j * parameterHeightWeight (H i) k *
        oneHighVariationWeight p requestedBase (r + L k) x v :=
    (hjet k (a + b)).choose_spec.2 i q a b rfl hpositive x hx v
  have hnatpower : R ^ ((e : ℝ) / (((N + shift * K : ℕ) : ℝ) + 1)) =
      (R ^ (1 / (((N + shift * K : ℕ) : ℝ) + 1))) ^ e := by
    rw [← Real.rpow_mul_natCast (zero_le_one.trans hR)]
    congr 1
    ring
  calc
    |(J i a b q).D k x v| ≤ A j * E i ^ A j * parameterHeightWeight (H i) k *
        (C * R ^ ((e : ℝ) / (((N + shift * K : ℕ) : ℝ) + 1))) :=
      hraw.trans (mul_le_mul_of_nonneg_left hw' hfactor)
    _ = (A j * E i ^ A j * C) * parameterHeightWeight (H i) k *
        R ^ ((e : ℝ) / (((N + shift * K : ℕ) : ℝ) + 1)) := by ring
    _ ≤ (B * E i ^ B) * parameterHeightWeight (H i) k *
        R ^ ((e : ℝ) / (((N + shift * K : ℕ) : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hheight)
        (Real.rpow_nonneg (zero_le_one.trans hR) _)
    _ = _ := by rw [hnatpower]

end ContinuousFlexibility.Analysis
