import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Schur test for block-localized operators

This file contains the analytic input for the "block Schur estimate" of paper section 6
(`06-global-reference-inverse.tex`): an operator whose localized blocks decay like
`exp (-η |S_k - S_m|)` along a sequence `S` with gaps bounded below is bounded, because
`sup_k ∑_m exp (-η |S_k - S_m|) ≤ 1 + 2 / (exp (η s₀) - 1)`.

* `ennreal_schur_test`: the scalar Schur test in `ℝ≥0∞`.
* `real_schur_test`: its real-valued corollary for nonnegative matrices indexed by `ℕ × ℕ`.
* `schur_operator_bound`: the operator form, bounding `‖T‖` by `√(A B c₁ c₂)`.
* `exp_row_sum_le`: the exponential row sums along a sequence with gaps `≥ s₀`.
* `cubic_gap_ge`: the gap condition for the paper's sequence `S n = (2/3) n ^ 3`.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open scoped ENNReal

/-- Cauchy-Schwarz for `tsum` in `ℝ≥0∞`, squared form (no summability assumptions). -/
theorem ennreal_cauchy_schwarz_tsum {α : Type*} (f g : α → ℝ≥0∞) :
    (∑' i, f i * g i) ^ 2 ≤ (∑' i, f i ^ 2) * ∑' i, g i ^ 2 := by
  have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / (2 : ℝ))) ^ 2 = x := by
    intro x
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have h : ∑' i, f i * g i ≤
      (∑' i, f i ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∑' i, g i ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    calc ∑' i, f i * g i = ⨆ s : Finset α, ∑ i ∈ s, f i * g i := ENNReal.tsum_eq_iSup_sum
      _ ≤ _ := by
        refine iSup_le fun s => ?_
        refine (ENNReal.inner_le_Lp_mul_Lq s f g Real.HolderConjugate.two_two).trans ?_
        exact mul_le_mul'
          (ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum s) (by norm_num))
          (ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum s) (by norm_num))
  simp_rw [ENNReal.rpow_two] at h
  calc (∑' i, f i * g i) ^ 2
      ≤ ((∑' i, f i ^ 2) ^ (1 / (2 : ℝ)) * (∑' i, g i ^ 2) ^ (1 / (2 : ℝ))) ^ 2 := by
        gcongr
    _ = (∑' i, f i ^ 2) * ∑' i, g i ^ 2 := by
        rw [mul_pow, hsq, hsq]

/-- **Scalar Schur test** in `ℝ≥0∞`, with no summability side conditions. -/
theorem ennreal_schur_test {ι κ : Type*}
    (a : ι → κ → ℝ≥0∞) (ξ : ι → ℝ≥0∞) (ζ : κ → ℝ≥0∞) {A B : ℝ≥0∞}
    (hrow : ∀ i, ∑' j, a i j ≤ A) (hcol : ∀ j, ∑' i, a i j ≤ B) :
    (∑' i, ∑' j, a i j * ξ i * ζ j) ^ 2 ≤ A * B * (∑' i, ξ i ^ 2) * (∑' j, ζ j ^ 2) := by
  have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / (2 : ℝ))) ^ 2 = x := by
    intro x
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hmm : ∀ x : ℝ≥0∞, x ^ (1 / (2 : ℝ)) * x ^ (1 / (2 : ℝ)) = x := fun x => by
    rw [← sq]; exact hsq x
  have hprod : ∀ p : ι × κ,
      (a p.1 p.2 ^ (1 / (2 : ℝ)) * ξ p.1) * (a p.1 p.2 ^ (1 / (2 : ℝ)) * ζ p.2)
        = a p.1 p.2 * ξ p.1 * ζ p.2 := by
    intro p
    calc (a p.1 p.2 ^ (1 / (2 : ℝ)) * ξ p.1) * (a p.1 p.2 ^ (1 / (2 : ℝ)) * ζ p.2)
        = (a p.1 p.2 ^ (1 / (2 : ℝ)) * a p.1 p.2 ^ (1 / (2 : ℝ))) * ξ p.1 * ζ p.2 := by ring
      _ = a p.1 p.2 * ξ p.1 * ζ p.2 := by rw [hmm]
  have hS : ∑' i, ∑' j, a i j * ξ i * ζ j
      = ∑' p : ι × κ, (a p.1 p.2 ^ (1 / (2 : ℝ)) * ξ p.1) * (a p.1 p.2 ^ (1 / (2 : ℝ)) * ζ p.2) :=
    ((tsum_congr fun p => hprod p).trans
      (ENNReal.tsum_prod (f := fun i j => a i j * ξ i * ζ j))).symm
  have hu : ∑' p : ι × κ, (a p.1 p.2 ^ (1 / (2 : ℝ)) * ξ p.1) ^ 2 ≤ A * ∑' i, ξ i ^ 2 := by
    calc ∑' p : ι × κ, (a p.1 p.2 ^ (1 / (2 : ℝ)) * ξ p.1) ^ 2
        = ∑' p : ι × κ, a p.1 p.2 * ξ p.1 ^ 2 :=
          tsum_congr fun p => by rw [mul_pow, hsq]
      _ = ∑' i, ∑' j, a i j * ξ i ^ 2 :=
          ENNReal.tsum_prod (f := fun i j => a i j * ξ i ^ 2)
      _ = ∑' i, (∑' j, a i j) * ξ i ^ 2 := tsum_congr fun i => ENNReal.tsum_mul_right
      _ ≤ ∑' i, A * ξ i ^ 2 := ENNReal.tsum_le_tsum fun i => by
          gcongr
          exact hrow i
      _ = A * ∑' i, ξ i ^ 2 := ENNReal.tsum_mul_left
  have hv : ∑' p : ι × κ, (a p.1 p.2 ^ (1 / (2 : ℝ)) * ζ p.2) ^ 2 ≤ B * ∑' j, ζ j ^ 2 := by
    calc ∑' p : ι × κ, (a p.1 p.2 ^ (1 / (2 : ℝ)) * ζ p.2) ^ 2
        = ∑' p : ι × κ, a p.1 p.2 * ζ p.2 ^ 2 :=
          tsum_congr fun p => by rw [mul_pow, hsq]
      _ = ∑' i, ∑' j, a i j * ζ j ^ 2 :=
          ENNReal.tsum_prod (f := fun i j => a i j * ζ j ^ 2)
      _ = ∑' j, ∑' i, a i j * ζ j ^ 2 := ENNReal.tsum_comm
      _ = ∑' j, (∑' i, a i j) * ζ j ^ 2 := tsum_congr fun j => ENNReal.tsum_mul_right
      _ ≤ ∑' j, B * ζ j ^ 2 := ENNReal.tsum_le_tsum fun j => by
          gcongr
          exact hcol j
      _ = B * ∑' j, ζ j ^ 2 := ENNReal.tsum_mul_left
  calc (∑' i, ∑' j, a i j * ξ i * ζ j) ^ 2
      = (∑' p : ι × κ,
          (a p.1 p.2 ^ (1 / (2 : ℝ)) * ξ p.1) * (a p.1 p.2 ^ (1 / (2 : ℝ)) * ζ p.2)) ^ 2 := by
        rw [hS]
    _ ≤ (∑' p : ι × κ, (a p.1 p.2 ^ (1 / (2 : ℝ)) * ξ p.1) ^ 2) *
          ∑' p : ι × κ, (a p.1 p.2 ^ (1 / (2 : ℝ)) * ζ p.2) ^ 2 :=
        ennreal_cauchy_schwarz_tsum _ _
    _ ≤ (A * ∑' i, ξ i ^ 2) * (B * ∑' j, ζ j ^ 2) := mul_le_mul' hu hv
    _ = A * B * (∑' i, ξ i ^ 2) * (∑' j, ζ j ^ 2) := by ring

/-- **Real Schur test** for nonnegative matrices indexed by `ℕ × ℕ`. -/
theorem real_schur_test (a : ℕ → ℕ → ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ k m, 0 ≤ a k m)
    (hrow : ∀ k, Summable (fun m => a k m) ∧ ∑' m, a k m ≤ A)
    (hcol : ∀ m, Summable (fun k => a k m) ∧ ∑' k, a k m ≤ B)
    (ξ ζ : ℕ → ℝ) (hξ0 : ∀ k, 0 ≤ ξ k) (hζ0 : ∀ m, 0 ≤ ζ m)
    (hξ : Summable (fun k => ξ k ^ 2)) (hζ : Summable (fun m => ζ m ^ 2)) :
    Summable (fun q : ℕ × ℕ => a q.1 q.2 * ξ q.1 * ζ q.2) ∧
      ∑' q : ℕ × ℕ, a q.1 q.2 * ξ q.1 * ζ q.2 ≤
        Real.sqrt (A * B) * Real.sqrt (∑' k, ξ k ^ 2) * Real.sqrt (∑' m, ζ m ^ 2) := by
  have hF0 : ∀ q : ℕ × ℕ, 0 ≤ a q.1 q.2 * ξ q.1 * ζ q.2 := fun q =>
    mul_nonneg (mul_nonneg (ha _ _) (hξ0 _)) (hζ0 _)
  have hrowE : ∀ k, ∑' m, ENNReal.ofReal (a k m) ≤ ENNReal.ofReal A := fun k => by
    rw [← ENNReal.ofReal_tsum_of_nonneg (ha k) (hrow k).1]
    exact ENNReal.ofReal_le_ofReal (hrow k).2
  have hcolE : ∀ m, ∑' k, ENNReal.ofReal (a k m) ≤ ENNReal.ofReal B := fun m => by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => ha k m) (hcol m).1]
    exact ENNReal.ofReal_le_ofReal (hcol m).2
  have key := ennreal_schur_test (fun k m => ENNReal.ofReal (a k m))
    (fun k => ENNReal.ofReal (ξ k)) (fun m => ENNReal.ofReal (ζ m)) hrowE hcolE
  have hX0 : 0 ≤ ∑' k, ξ k ^ 2 := tsum_nonneg fun k => sq_nonneg _
  have hY0 : 0 ≤ ∑' m, ζ m ^ 2 := tsum_nonneg fun m => sq_nonneg _
  have hXE : ∑' k, ENNReal.ofReal (ξ k) ^ 2 = ENNReal.ofReal (∑' k, ξ k ^ 2) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg (ξ k)) hξ]
    exact tsum_congr fun k => (ENNReal.ofReal_pow (hξ0 k) 2).symm
  have hYE : ∑' m, ENNReal.ofReal (ζ m) ^ 2 = ENNReal.ofReal (∑' m, ζ m ^ 2) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun m => sq_nonneg (ζ m)) hζ]
    exact tsum_congr fun m => (ENNReal.ofReal_pow (hζ0 m) 2).symm
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have hABX : 0 ≤ A * B * ∑' k, ξ k ^ 2 := mul_nonneg hAB hX0
  have hABXY : 0 ≤ A * B * (∑' k, ξ k ^ 2) * ∑' m, ζ m ^ 2 := mul_nonneg hABX hY0
  have hR : ENNReal.ofReal A * ENNReal.ofReal B * ENNReal.ofReal (∑' k, ξ k ^ 2) *
      ENNReal.ofReal (∑' m, ζ m ^ 2)
      = ENNReal.ofReal (A * B * (∑' k, ξ k ^ 2) * ∑' m, ζ m ^ 2) := by
    rw [ENNReal.ofReal_mul hABX, ENNReal.ofReal_mul hAB, ENNReal.ofReal_mul hA]
  have hmul : ∀ q : ℕ × ℕ, ENNReal.ofReal (a q.1 q.2 * ξ q.1 * ζ q.2)
      = ENNReal.ofReal (a q.1 q.2) * ENNReal.ofReal (ξ q.1) * ENNReal.ofReal (ζ q.2) := fun q => by
    rw [ENNReal.ofReal_mul (mul_nonneg (ha _ _) (hξ0 _)), ENNReal.ofReal_mul (ha _ _)]
  have hT : ∑' i, ∑' j, ENNReal.ofReal (a i j) * ENNReal.ofReal (ξ i) * ENNReal.ofReal (ζ j)
      = ∑' q : ℕ × ℕ, ENNReal.ofReal (a q.1 q.2 * ξ q.1 * ζ q.2) :=
    ((tsum_congr fun q => hmul q).trans
      (ENNReal.tsum_prod
        (f := fun i j => ENNReal.ofReal (a i j) * ENNReal.ofReal (ξ i) * ENNReal.ofReal (ζ j)))).symm
  have hT2 : (∑' q : ℕ × ℕ, ENNReal.ofReal (a q.1 q.2 * ξ q.1 * ζ q.2)) ^ 2
      ≤ ENNReal.ofReal (A * B * (∑' k, ξ k ^ 2) * ∑' m, ζ m ^ 2) := by
    calc (∑' q : ℕ × ℕ, ENNReal.ofReal (a q.1 q.2 * ξ q.1 * ζ q.2)) ^ 2
        = (∑' i, ∑' j,
            ENNReal.ofReal (a i j) * ENNReal.ofReal (ξ i) * ENNReal.ofReal (ζ j)) ^ 2 := by
          rw [hT]
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal B * (∑' k, ENNReal.ofReal (ξ k) ^ 2) *
            (∑' m, ENNReal.ofReal (ζ m) ^ 2) := key
      _ = ENNReal.ofReal (A * B * (∑' k, ξ k ^ 2) * ∑' m, ζ m ^ 2) := by
          rw [hXE, hYE, hR]
  have hsq : (∑' q : ℕ × ℕ, ENNReal.ofReal (a q.1 q.2 * ξ q.1 * ζ q.2)) ^ 2 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hT2
  have hTne : ∑' q : ℕ × ℕ, ENNReal.ofReal (a q.1 q.2 * ξ q.1 * ζ q.2) ≠ ⊤ := by
    intro h
    apply hsq
    rw [h]
    simp
  refine ⟨(ENNReal.summable_toReal hTne).congr fun q => ENNReal.toReal_ofReal (hF0 q), ?_⟩
  have hsumeq : ∑' q : ℕ × ℕ, a q.1 q.2 * ξ q.1 * ζ q.2
      = (∑' q : ℕ × ℕ, ENNReal.ofReal (a q.1 q.2 * ξ q.1 * ζ q.2)).toReal := by
    rw [ENNReal.tsum_toReal_eq (fun q => ENNReal.ofReal_ne_top)]
    exact tsum_congr fun q => (ENNReal.toReal_ofReal (hF0 q)).symm
  have hreal : ((∑' q : ℕ × ℕ, ENNReal.ofReal (a q.1 q.2 * ξ q.1 * ζ q.2)).toReal) ^ 2
      ≤ A * B * (∑' k, ξ k ^ 2) * ∑' m, ζ m ^ 2 := by
    rw [← ENNReal.toReal_pow]
    exact ENNReal.toReal_le_of_le_ofReal hABXY hT2
  rw [hsumeq]
  refine (Real.le_sqrt_of_sq_le hreal).trans (le_of_eq ?_)
  rw [Real.sqrt_mul hABX, Real.sqrt_mul hAB]

/-- **Operator form of the Schur test.** If the blocks of `T` are dominated by a nonnegative
matrix `a` with bounded row and column sums, paired with local-size functionals `p`, `n` that
are square-summable with bound `c₁ ‖x‖ ^ 2`, `c₂ ‖y‖ ^ 2`, then `‖T‖ ≤ √(A B c₁ c₂)`. -/
theorem schur_operator_bound {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →L[ℝ] F) (p : ℕ → E → ℝ) (n : ℕ → F → ℝ) (a : ℕ → ℕ → ℝ)
    {A B c₁ c₂ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (ha : ∀ k m, 0 ≤ a k m)
    (hrow : ∀ k, Summable (fun m => a k m) ∧ ∑' m, a k m ≤ A)
    (hcol : ∀ m, Summable (fun k => a k m) ∧ ∑' k, a k m ≤ B)
    (hp0 : ∀ m x, 0 ≤ p m x) (hn0 : ∀ k y, 0 ≤ n k y)
    (hp : ∀ x, Summable (fun m => p m x ^ 2) ∧ ∑' m, p m x ^ 2 ≤ c₁ * ‖x‖ ^ 2)
    (hn : ∀ y, Summable (fun k => n k y ^ 2) ∧ ∑' k, n k y ^ 2 ≤ c₂ * ‖y‖ ^ 2)
    (hT : ∀ x y, |inner ℝ y (T x)| ≤ ∑' q : ℕ × ℕ, a q.1 q.2 * n q.1 y * p q.2 x) :
    ‖T‖ ≤ Real.sqrt (A * B * c₁ * c₂) := by
  have hABc₁ : 0 ≤ A * B * c₁ := mul_nonneg (mul_nonneg hA hB) hc₁
  have hbil : ∀ x y, |inner ℝ y (T x)| ≤ Real.sqrt (A * B * c₁ * c₂) * ‖x‖ * ‖y‖ := by
    intro x y
    obtain ⟨_, hle⟩ := real_schur_test a hA hB ha hrow hcol (fun k => n k y) (fun m => p m x)
      (fun k => hn0 k y) (fun m => hp0 m x) (hn y).1 (hp x).1
    have h1 : Real.sqrt (∑' k, n k y ^ 2) ≤ Real.sqrt (c₂ * ‖y‖ ^ 2) :=
      Real.sqrt_le_sqrt (hn y).2
    have h2 : Real.sqrt (∑' m, p m x ^ 2) ≤ Real.sqrt (c₁ * ‖x‖ ^ 2) :=
      Real.sqrt_le_sqrt (hp x).2
    have h3 : Real.sqrt (A * B) * Real.sqrt (∑' k, n k y ^ 2) * Real.sqrt (∑' m, p m x ^ 2)
        ≤ Real.sqrt (A * B) * Real.sqrt (c₂ * ‖y‖ ^ 2) * Real.sqrt (c₁ * ‖x‖ ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)) h2 (Real.sqrt_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have h4 : Real.sqrt (A * B) * Real.sqrt (c₂ * ‖y‖ ^ 2) * Real.sqrt (c₁ * ‖x‖ ^ 2)
        = Real.sqrt (A * B * c₁ * c₂) * ‖x‖ * ‖y‖ := by
      rw [Real.sqrt_mul hc₂, Real.sqrt_mul hc₁, Real.sqrt_sq (norm_nonneg y),
        Real.sqrt_sq (norm_nonneg x), Real.sqrt_mul hABc₁, Real.sqrt_mul (mul_nonneg hA hB)]
      ring
    exact ((hT x y).trans hle).trans (h3.trans_eq h4)
  refine ContinuousLinearMap.opNorm_le_bound T (Real.sqrt_nonneg _) fun x => ?_
  by_cases h0 : T x = 0
  · rw [h0, norm_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  · have hpos : 0 < ‖T x‖ := norm_pos_iff.2 h0
    have h := hbil x (T x)
    rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at h
    refine le_of_mul_le_mul_right ?_ hpos
    calc ‖T x‖ * ‖T x‖ = ‖T x‖ ^ 2 := (sq _).symm
      _ ≤ Real.sqrt (A * B * c₁ * c₂) * ‖x‖ * ‖T x‖ := h

/-- One step of the gap bound: `s₀ * d ≤ S (m + d) - S m`. -/
theorem gap_ge {S : ℕ → ℝ} {s₀ : ℝ} (hS : ∀ m, s₀ ≤ S (m + 1) - S m) (m d : ℕ) :
    s₀ * d ≤ S (m + d) - S m := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h := hS (m + d)
    have e : S (m + (d + 1)) = S (m + d + 1) := rfl
    rw [e]
    push_cast
    linarith

/-- The index distance is controlled by the distance of `S`. -/
theorem index_dist_le {S : ℕ → ℝ} {s₀ : ℝ} (hS : ∀ m, s₀ ≤ S (m + 1) - S m) (k m : ℕ) :
    s₀ * |(k : ℝ) - m| ≤ |S k - S m| := by
  have aux : ∀ k m : ℕ, m ≤ k → s₀ * |(k : ℝ) - m| ≤ |S k - S m| := by
    intro k m h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have e : ((m + d : ℕ) : ℝ) - m = d := by push_cast; ring
    rw [e, abs_of_nonneg (Nat.cast_nonneg d)]
    exact (gap_ge hS m d).trans (le_abs_self _)
  rcases le_total m k with h | h
  · exact aux k m h
  · have := aux m k h
    rwa [abs_sub_comm (m : ℝ), abs_sub_comm (S m)] at this

/-- Algebra for the geometric bound: with `ρ = E⁻¹`,
`ρ / (1 - ρ) + 1 / (1 - ρ) = 1 + 2 / (E - 1)`. -/
theorem geom_algebra {E : ℝ} (hE : 1 < E) :
    E⁻¹ * (1 - E⁻¹)⁻¹ + (1 - E⁻¹)⁻¹ = 1 + 2 / (E - 1) := by
  have hE0 : E ≠ 0 := (lt_trans zero_lt_one hE).ne'
  have hE1 : E - 1 ≠ 0 := (sub_pos.2 hE).ne'
  have h1 : 1 - E⁻¹ = (E - 1) / E := by field_simp
  rw [h1, inv_div, ← mul_div_assoc, inv_mul_cancel₀ hE0, ← add_div]
  have h2 : 1 + E = (E - 1) + 2 := by ring
  rw [h2, add_div, div_self hE1]

/-- Row-sum bound for a nonnegative sequence dominated by `ρ ^ |k - m|`. -/
theorem sum_bound_of_le {g : ℕ → ℝ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hg0 : ∀ m, 0 ≤ g m) (k : ℕ)
    (h1 : ∀ m, m < k → g m ≤ ρ ^ (k - m)) (h2 : ∀ j, g (j + k) ≤ ρ ^ j) :
    Summable g ∧ ∑' m, g m ≤ ρ * (1 - ρ)⁻¹ + (1 - ρ)⁻¹ := by
  have hgeo := summable_geometric_of_lt_one hρ0 hρ1
  have hsh : Summable (fun j => g (j + k)) :=
    Summable.of_nonneg_of_le (fun j => hg0 _) h2 hgeo
  refine ⟨hsh.comp_nat_add, ?_⟩
  have hsplit : ∑' m, g m = ∑ i ∈ Finset.range k, g i + ∑' j, g (j + k) :=
    (HasSum.sum_range_add (f := g) hsh.hasSum).tsum_eq
  have htail : ∑' j, g (j + k) ≤ (1 - ρ)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hρ0 hρ1]
    exact hsh.tsum_le_tsum h2 hgeo
  have hhead : ∑ i ∈ Finset.range k, g i ≤ ρ * (1 - ρ)⁻¹ := by
    calc ∑ i ∈ Finset.range k, g i ≤ ∑ i ∈ Finset.range k, ρ ^ (k - i) :=
          Finset.sum_le_sum fun i hi => h1 i (Finset.mem_range.1 hi)
      _ = ∑ j ∈ Finset.range k, ρ ^ (j + 1) := by
          rw [← Finset.sum_range_reflect (fun i => ρ ^ (k - i)) k]
          refine Finset.sum_congr rfl fun j hj => ?_
          have := Finset.mem_range.1 hj
          show ρ ^ (k - (k - 1 - j)) = ρ ^ (j + 1)
          congr 1
          omega
      _ = ρ * ∑ j ∈ Finset.range k, ρ ^ j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ ρ * (1 - ρ)⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ hρ0
          rw [← tsum_geometric_of_lt_one hρ0 hρ1]
          exact hgeo.sum_le_tsum _ (fun i _ => pow_nonneg hρ0 i)
  rw [hsplit]
  linarith

/-- **Exponential row sums.** If `S (m + 1) - S m ≥ s₀ > 0` then
`∑ₘ exp (-(η |S k - S m|)) ≤ 1 + 2 / (exp (η s₀) - 1)`. -/
theorem exp_row_sum_le {S : ℕ → ℝ} {s₀ η : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (hS : ∀ m, s₀ ≤ S (m + 1) - S m) (k : ℕ) :
    Summable (fun m => Real.exp (-(η * |S k - S m|))) ∧
      ∑' m, Real.exp (-(η * |S k - S m|)) ≤ 1 + 2 / (Real.exp (η * s₀) - 1) := by
  have hE : 1 < Real.exp (η * s₀) := by
    have := Real.exp_lt_exp.2 (mul_pos hη hs₀)
    rwa [Real.exp_zero] at this
  have hρ0 : 0 ≤ Real.exp (-(η * s₀)) := (Real.exp_pos _).le
  have hρ1 : Real.exp (-(η * s₀)) < 1 := by
    rw [Real.exp_neg]
    exact inv_lt_one_of_one_lt₀ hE
  have key : ∀ m d : ℕ, Real.exp (-(η * |S (m + d) - S m|)) ≤ Real.exp (-(η * s₀)) ^ d := by
    intro m d
    have h1 := gap_ge hS m d
    have h2 : 0 ≤ S (m + d) - S m := le_trans (mul_nonneg hs₀.le (Nat.cast_nonneg d)) h1
    rw [abs_of_nonneg h2, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    nlinarith [mul_le_mul_of_nonneg_left h1 hη.le]
  have le_case : ∀ k m : ℕ, m ≤ k →
      Real.exp (-(η * |S k - S m|)) ≤ Real.exp (-(η * s₀)) ^ (k - m) := by
    intro k m h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_sub_cancel_left]
    exact key m d
  have ge_case : ∀ m : ℕ, k ≤ m →
      Real.exp (-(η * |S k - S m|)) ≤ Real.exp (-(η * s₀)) ^ (m - k) := by
    intro m h
    rw [abs_sub_comm]
    exact le_case m k h
  have hmain := sum_bound_of_le (g := fun m => Real.exp (-(η * |S k - S m|))) hρ0 hρ1
    (fun m => (Real.exp_pos _).le) k (fun m hm => le_case k m hm.le)
    (fun j => by
      have := ge_case (j + k) (Nat.le_add_left k j)
      rwa [Nat.add_sub_cancel] at this)
  refine ⟨hmain.1, hmain.2.trans (le_of_eq ?_)⟩
  rw [Real.exp_neg]
  exact geom_algebra hE

/-- The gap condition for the paper's sequence `S n = (2/3) n ^ 3`. -/
theorem cubic_gap_ge (m : ℕ) :
    (2 / 3 : ℝ) ≤ (2 / 3) * ((m : ℝ) + 1) ^ 3 - (2 / 3) * (m : ℝ) ^ 3 := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith [mul_nonneg hm hm]

end ContinuousFlexibility.Radial
