module

public import ContinuousFlexibility.Radial.ReferenceSchurInverse
public import ContinuousFlexibility.Radial.MatchedWeightLevelBounds
public import ContinuousFlexibility.Radial.MatchedWeightMorseFibers

/-!
# Actual four-channel envelopes imply a common reference inverse

Index zero denotes the scalar border and the successor indices denote
the actual physical cells. The established finite-fiber weight estimates
are applied to the norms of those actual blocks. This file only identifies
the channel weights and appends the scalar index to the cell-level map;
it introduces no replacement operator or output-space assumption.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open ContinuousFlexibility.Radial

/-- The scalar channel has level zero; every cell keeps its true level. -/
def referenceRawChannelLevel (D : ReferenceData) : ℕ → ℕ
  | 0 => 0
  | m + 1 => D.cellIndex m

theorem referenceRawChannelWeight_eq (D : ReferenceData) (γ M : ℝ) (k : ℕ) :
    matchedPhysicalChannelWeight D γ M k =
      Real.exp (M * radialQ (referenceRawChannelLevel D k) +
        γ * radialS (referenceRawChannelLevel D k)) := by
  cases k with
  | zero =>
      norm_num [matchedPhysicalChannelWeight, referenceRawChannelLevel, radialQ, radialS]
  | succ k => rfl

/-- Appending the one scalar index increases the level multiplicity by at most one. -/
theorem referenceRawChannelLevel_fiber_bound (D : ReferenceData) (N : ℕ)
    (hfibers : ∀ n, Set.Finite {m | D.cellIndex m = n})
    (hcard : ∀ n, Set.ncard {m | D.cellIndex m = n} ≤ N) (n : ℕ) :
    Set.Finite {k | referenceRawChannelLevel D k = n} ∧
      Set.ncard {k | referenceRawChannelLevel D k = n} ≤ N + 1 := by
  have hsub : {k | referenceRawChannelLevel D k = n} ⊆
      insert 0 (Nat.succ '' {m | D.cellIndex m = n}) := by
    intro k hk
    cases k with
    | zero => exact mem_insert _ _
    | succ m =>
        apply mem_insert_of_mem
        exact ⟨m, hk, rfl⟩
  have hfinite : (insert 0 (Nat.succ '' {m | D.cellIndex m = n})).Finite :=
    ((hfibers n).image Nat.succ).insert 0
  refine ⟨hfinite.subset hsub, ?_⟩
  calc
    Set.ncard {k | referenceRawChannelLevel D k = n} ≤
        Set.ncard (insert 0 (Nat.succ '' {m | D.cellIndex m = n})) :=
      Set.ncard_le_ncard hsub hfinite
    _ ≤ Set.ncard (Nat.succ '' {m | D.cellIndex m = n}) + 1 :=
      Set.ncard_insert_le _ _
    _ ≤ Set.ncard {m | D.cellIndex m = n} + 1 :=
      Nat.add_le_add_right (Set.ncard_image_le (f := Nat.succ) (hfibers n)) 1
    _ ≤ N + 1 := Nat.add_le_add_right (hcard n) 1

/-- The actual Morse partition therefore has at most four augmented channels at each level. -/
theorem referenceRawChannelLevel_morse_fiber_bound {T : MorseChainData}
    (G : MorseChainGeometryWitness T) (w phi chi chiLeft : ℝ → ℝ) (n : ℕ) :
    Set.Finite {k |
      referenceRawChannelLevel (morsePartitionReference G w phi chi chiLeft) k = n} ∧
      Set.ncard {k |
        referenceRawChannelLevel (morsePartitionReference G w phi chi chiLeft) k = n} ≤ 4 :=
  referenceRawChannelLevel_fiber_bound
    (morsePartitionReference G w phi chi chiLeft) 3
    (fun l => (morsePartitionReference_cellIndex_fiber_bound G w phi chi chiLeft l).1)
    (fun l => (morsePartitionReference_cellIndex_fiber_bound G w phi chi chiLeft l).2) n

/-- One unweighted envelope for the actual four kinds of block gives
common row and column bounds throughout the frozen exponent interval. -/
theorem referenceRawKernel_schur_majorants {D : ReferenceData}
    (hD : IsAccumulatingProfile D)
    (G : ℕ → RadialModePair D →L[ℝ] RadialModePair D) (N : ℕ)
    (hfibers : ∀ n, Set.Finite {m | D.cellIndex m = n})
    (hcard : ∀ n, Set.ncard {m | D.cellIndex m = n} ≤ N)
    {C₀ a : ℝ} (hC₀ : 0 < C₀)
    (henvelope : ∀ n k m,
      matchedPhysicalRawKernel D hD hD.choose_spec.2.1
          (G n ∘L matchedModeScalarGate D (decide (n = 0))) k m ≤
        C₀ * Real.exp
          (a * (radialQ (referenceRawChannelLevel D k) +
            radialQ (referenceRawChannelLevel D m)) -
            |radialS (referenceRawChannelLevel D k) -
              radialS (referenceRawChannelLevel D m)|)) :
    ∃ Mraw M₁ A : ℝ, a ≤ Mraw ∧ a ≤ M₁ ∧ 0 ≤ M₁ ∧ 0 < A ∧
      ∀ γ ∈ Icc (5 / 8 : ℝ) (7 / 8 : ℝ),
      ∃ K : ℕ → ℕ → ℕ → ℝ,
        (∀ n k m, 0 ≤ K n k m) ∧
        (∀ n k, Summable (K n k) ∧ ∑' m, K n k m ≤ A) ∧
        (∀ n m, Summable (fun k => K n k m) ∧ ∑' k, K n k m ≤ A) ∧
        (∀ n k m,
          matchedPhysicalChannelWeight D γ (-M₁) k *
              matchedPhysicalRawKernel D hD hD.choose_spec.2.1
                (G n ∘L matchedModeScalarGate D (decide (n = 0))) k m ≤
            K n k m * matchedPhysicalChannelWeight D γ Mraw m) := by
  let L : ℝ := max a 0 + 1
  have haL : a < L := by
    have hh := le_max_left a 0
    dsimp only [L]
    linarith
  have hL : 0 < L := by
    have hh := le_max_right a 0
    dsimp only [L]
    linarith
  let R : ℕ → ℕ → ℕ → ℝ := fun n =>
    matchedPhysicalRawKernel D hD hD.choose_spec.2.1
      (G n ∘L matchedModeScalarGate D (decide (n = 0)))
  have hR (n k m : ℕ) : 0 ≤ R n k m :=
    matchedPhysicalRawKernel_nonneg D hD hD.choose_spec.2.1
      (G n ∘L matchedModeScalarGate D (decide (n = 0))) k m
  have hfiber (n : ℕ) :=
    referenceRawChannelLevel_fiber_bound D N hfibers hcard n
  obtain ⟨C, hC, hest⟩ := matched_level_global_weightedKernel_estimates
    (referenceRawChannelLevel D) (N + 1)
    (fun n => (hfiber n).1) (fun n => (hfiber n).2)
    R L L C₀ a (5 / 8 : ℝ) (7 / 8 : ℝ) hC₀
    (by norm_num) (by norm_num) (by linarith) hR henvelope
  let A : ℝ := C * (((N + 1 : ℕ) : ℝ) * matchedSchurFactor ((1 - (7 / 8 : ℝ)) / 2))
  have hA : 0 < A := by
    have hh : 0 < matchedSchurFactor ((1 - (7 / 8 : ℝ)) / 2) :=
      matchedSchurFactor_pos (by norm_num)
    dsimp only [A]
    positivity
  refine ⟨L, L, A, haL.le, haL.le, hL.le, hA, ?_⟩
  intro γ hγ
  let K : ℕ → ℕ → ℕ → ℝ := fun n =>
    matchedLevelWeightedKernel (referenceRawChannelLevel D) L L γ (R n)
  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · intro n k m
    exact matchedLevelWeightedKernel_nonneg (hR n) k m
  · intro n k
    exact (hest γ hγ n).2.1 k
  · intro n m
    exact (hest γ hγ n).2.2 m
  · intro n k m
    have hratio : K n k m =
        matchedPhysicalChannelWeight D γ (-L) k * R n k m /
          matchedPhysicalChannelWeight D γ L m := by
      rw [referenceRawChannelWeight_eq, referenceRawChannelWeight_eq]
      exact matchedLevelWeightedKernel_eq_weight_ratio
        (referenceRawChannelLevel D) L L γ (R n) k m
    have hpos : 0 < matchedPhysicalChannelWeight D γ L m := by
      rw [referenceRawChannelWeight_eq]
      exact Real.exp_pos _
    exact ((div_eq_iff hpos.ne').mp hratio.symm).le

/-- This is a terminal bridge from actual unweighted block estimates and
true cell-level multiplicity to one inverse at all three frozen exponents. -/
theorem referenceSchur_common_inverse_of_raw_envelope {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (G : ℕ → RadialModePair D →L[ℝ] RadialModePair D)
    (hG : ∀ n : ℕ, ModeInverseProperties D (2 * (n + 1)) (G n))
    (N : ℕ) (hfibers : ∀ n, Set.Finite {m | D.cellIndex m = n})
    (hcard : ∀ n, Set.ncard {m | D.cellIndex m = n} ≤ N)
    {C₀ a : ℝ} (hC₀ : 0 < C₀)
    (henvelope : ∀ n k m,
      matchedPhysicalRawKernel D hD hD.choose_spec.2.1
          (G n ∘L matchedModeScalarGate D (decide (n = 0))) k m ≤
        C₀ * Real.exp
          (a * (radialQ (referenceRawChannelLevel D k) +
            radialQ (referenceRawChannelLevel D m)) -
            |radialS (referenceRawChannelLevel D k) -
              radialS (referenceRawChannelLevel D m)|)) :
    ∃ M₀ M₁ : ℝ, 0 ≤ M₁ ∧ ∃ H : RadialSource → RadialUnknown,
      ∀ γ : ℝ,
      γ = referenceBeta - 1 / 8 ∨ γ = referenceBeta ∨ γ = referenceBeta + 1 / 8 →
        ReferenceInverseProperties D γ M₀ M₁ H := by
  obtain ⟨Mraw, M₁, A, _, _, hM₁, hA, hraw⟩ :=
    referenceRawKernel_schur_majorants hD G N hfibers hcard hC₀ henvelope
  obtain ⟨M₀, H, hH⟩ := referenceSchur_common_inverse_of_raw_bounds
    hD hborder G hG (A := A) (B := A) (Mraw := Mraw) (M₁ := M₁)
    hA.le hA.le hM₁ (fun γ hγ => hraw γ (matched_reference_exponents_mem hγ))
  exact ⟨M₀, M₁, hM₁, H, hH⟩

end ContinuousFlexibility.Statements
