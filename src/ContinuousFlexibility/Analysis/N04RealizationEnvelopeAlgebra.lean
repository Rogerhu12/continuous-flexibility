import ContinuousFlexibility.Analysis.N01cOpticalNumericEnvelopes

/-!
# Finite envelopes on a fixed index set

The indices may contain a state, a piece and an actual evaluation point.
All constants are chosen before those indices. Finite collection and the
conversion to a natural state degree do not restrict the index set.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators

theorem HasPositiveEnvelope.mono {X : Type*} {E F G : X → ℝ}
    (hF : HasPositiveEnvelope E F) (hGF : ∀ x, G x ≤ F x) :
    HasPositiveEnvelope E G := by
  obtain ⟨C, A, hC, hA, hb⟩ := hF
  exact ⟨C, A, hC, hA, fun x => (hGF x).trans (hb x)⟩

theorem HasPositiveEnvelope.base_mono {X : Type*} {E Q F : X → ℝ}
    (hF : HasPositiveEnvelope E F) (hE : ∀ x, 0 ≤ E x)
    (hEQ : ∀ x, E x ≤ Q x) : HasPositiveEnvelope Q F := by
  obtain ⟨C, A, hC, hA, hb⟩ := hF
  refine ⟨C, A, hC, hA, fun x => (hb x).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (hE x) (hEQ x) hA.le) hC.le

/-- One pair of constants bounds a finite family of nonnegative functions. -/
theorem n04Realization_envelope_finite_uniform
    {X ι : Type*} [Fintype ι] {E : X → ℝ} (hE : ∀ x, 1 ≤ E x)
    (F : ι → X → ℝ) (hF₀ : ∀ i x, 0 ≤ F i x)
    (hF : ∀ i, HasPositiveEnvelope E (F i)) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ x i, F i x ≤ C * E x ^ A := by
  classical
  obtain ⟨C, A, hC, hA, hb⟩ := hasPositiveEnvelope_finsetSum hE
    (Finset.univ : Finset ι) F (fun i _ => hF i)
  refine ⟨C, A, hC, hA, fun x i => ?_⟩
  exact (Finset.single_le_sum (fun j _ => hF₀ j x) (Finset.mem_univ i)).trans (hb x)

/-- A combined coefficient/state envelope gives an ordinary natural
polynomial degree in the state factor, with the same index set. -/
theorem n04Realization_envelope_separate_state
    {X : Type*} {E R F : X → ℝ}
    (hE : ∀ x, 1 ≤ E x) (hR : ∀ x, 1 ≤ R x)
    (hF : HasPositiveEnvelope (fun x => E x * R x) F) :
    ∃ d : ℕ, ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      ∀ x, F x ≤ C * E x ^ A * R x ^ d := by
  obtain ⟨C, A, hC, hA, hb⟩ := hF
  refine ⟨⌈A⌉₊, C, A, hC, hA.le, fun x => ?_⟩
  have hpower : R x ^ A ≤ R x ^ (⌈A⌉₊ : ℕ) := by
    have h := Real.rpow_le_rpow_of_exponent_le (hR x) (Nat.le_ceil A)
    simpa only [Real.rpow_natCast] using h
  calc
    F x ≤ C * (E x * R x) ^ A := hb x
    _ = C * E x ^ A * R x ^ A := by
      rw [Real.mul_rpow (zero_le_one.trans (hE x)) (zero_le_one.trans (hR x))]
      ring
    _ ≤ C * E x ^ A * R x ^ (⌈A⌉₊ : ℕ) :=
      mul_le_mul_of_nonneg_left hpower
        (mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans (hE x)) _))

/-- Package an existing finite polynomial state bound into one combined
envelope. This does not restrict the state or change its grading order. -/
theorem n04Realization_envelope_of_product_bound
    {X : Type*} {E R F : X → ℝ}
    (hE : ∀ x, 1 ≤ E x) (hR : ∀ x, 1 ≤ R x)
    {C A : ℝ} {d : ℕ} (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hb : ∀ x, F x ≤ C * E x ^ A * R x ^ d) :
    HasPositiveEnvelope (fun x => E x * R x) F := by
  let B : ℝ := A + (d : ℝ) + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  have hAB : A ≤ B := by
    dsimp only [B]
    linarith only [Nat.cast_nonneg (α := ℝ) d]
  have hdB : (d : ℝ) ≤ B := by dsimp only [B]; linarith only [hA]
  refine ⟨C + 1, B, by positivity, hB, fun x => ?_⟩
  have hE0 : 0 ≤ E x := zero_le_one.trans (hE x)
  have hR0 : 0 ≤ R x := zero_le_one.trans (hR x)
  have hpowR : R x ^ d ≤ R x ^ B := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (hR x) hdB
  calc
    F x ≤ C * E x ^ A * R x ^ d := hb x
    _ ≤ C * E x ^ B * R x ^ B :=
      mul_le_mul (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (hE x) hAB) hC) hpowR
        (pow_nonneg hR0 d) (mul_nonneg hC (Real.rpow_nonneg hE0 B))
    _ = C * (E x * R x) ^ B := by rw [Real.mul_rpow hE0 hR0]; ring
    _ ≤ (C + 1) * (E x * R x) ^ B :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        (Real.rpow_nonneg (mul_nonneg hE0 hR0) B)

/-- Replacing the base by a proved envelope retains uniform constants. -/
theorem n04Realization_envelope_substitute
    {X : Type*} {E Q F : X → ℝ}
    (hE0 : ∀ x, 0 ≤ E x) (hQ : ∀ x, 1 ≤ Q x)
    (hE : HasPositiveEnvelope Q E) (hF : HasPositiveEnvelope E F) :
    HasPositiveEnvelope Q F := by
  obtain ⟨B, K, hB, hK, he⟩ := hE
  obtain ⟨C, A, hC, hA, hf⟩ := hF
  refine ⟨C * B ^ A, K * A, mul_pos hC (Real.rpow_pos_of_pos hB A),
    mul_pos hK hA, fun x => ?_⟩
  calc
    F x ≤ C * E x ^ A := hf x
    _ ≤ C * (B * Q x ^ K) ^ A :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hE0 x) (he x) hA.le) hC.le
    _ = (C * B ^ A) * Q x ^ (K * A) := by
      rw [Real.mul_rpow hB.le (Real.rpow_nonneg (zero_le_one.trans (hQ x)) K),
        ← Real.rpow_mul (zero_le_one.trans (hQ x))]
      ring

end ContinuousFlexibility.Analysis
