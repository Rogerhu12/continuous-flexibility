module

public import ContinuousFlexibility.Statements.Analysis
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# One high factor from the frozen interpolation estimate

The interpolation loss occurs in every active interpolation exponent.  A
single low order at least `interpLoss + 2` absorbs that cost.  Consequently
the base and high-order shift below are independent of the number of factors.
The numerical constants may depend on that number and on the distribution of
derivatives, as is appropriate for a fixed derivative order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped BigOperators

/-- A finite product of interpolated factors is bounded by the sum in which
one factor is high and every other factor is low.  Zero low factors are
included; no division by a possibly vanishing seminorm is left in the result. -/
theorem prod_interpolated_le_oneHigh
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (a b θ : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i)
    (hθ : ∀ i, 0 ≤ θ i) (hθlt : ∀ i, θ i < 1) (hθsum : ∑ i, θ i ≤ 1) :
    (∏ i, (a i) ^ (1 - θ i) * (b i) ^ θ i) ≤
      ∑ i, b i * ∏ j ∈ Finset.univ.erase i, a j := by
  classical
  have hb (i : ι) : 0 ≤ b i := (ha i).trans (hab i)
  by_cases hz : ∃ i, a i = 0
  · obtain ⟨i, hi⟩ := hz
    have hzero : (∏ j, (a j) ^ (1 - θ j) * (b j) ^ θ j) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [hi, Real.zero_rpow (sub_pos.mpr (hθlt i)).ne', zero_mul]
    rw [hzero]
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (hb i) (Finset.prod_nonneg (fun j _ => ha j)))
  · have hap (i : ι) : 0 < a i := by
      have hne : a i ≠ 0 := fun hi => hz ⟨i, hi⟩
      exact lt_of_le_of_ne (ha i) hne.symm
    let r : ι → ℝ := fun i => b i / a i
    let R : ℝ := ∑ i, r i
    have hr (i : ι) : 1 ≤ r i := by
      apply (le_div_iff₀ (hap i)).mpr
      simpa only [one_mul] using hab i
    have hr0 (i : ι) : 0 ≤ r i := zero_le_one.trans (hr i)
    have hrR (i : ι) : r i ≤ R :=
      Finset.single_le_sum (fun j _ => hr0 j) (Finset.mem_univ i)
    have hR : 1 ≤ R := (hr (Classical.arbitrary ι)).trans (hrR _)
    have hRp : 0 < R := zero_lt_one.trans_le hR
    have hprod : (∏ i, (r i) ^ θ i) ≤ R := by
      calc
        _ ≤ ∏ i, R ^ θ i :=
          Finset.prod_le_prod₀ (fun i _ => Real.rpow_nonneg (hr0 i) _)
            (fun i _ => Real.rpow_le_rpow (hr0 i) (hrR i) (hθ i))
        _ = R ^ (∑ i, θ i) := (Real.rpow_sum_of_pos hRp θ Finset.univ).symm
        _ ≤ R ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR hθsum
        _ = R := Real.rpow_one R
    calc
      (∏ i, (a i) ^ (1 - θ i) * (b i) ^ θ i) =
          ∏ i, a i * (r i) ^ θ i := by
        apply Finset.prod_congr rfl
        intro i _
        dsimp [r]
        rw [Real.rpow_sub (hap i), Real.rpow_one, Real.div_rpow (hb i) (ha i)]
        ring
      _ = (∏ i, a i) * ∏ i, (r i) ^ θ i := Finset.prod_mul_distrib
      _ ≤ (∏ i, a i) * R :=
        mul_le_mul_of_nonneg_left hprod (Finset.prod_nonneg (fun i _ => ha i))
      _ = ∑ i, b i * ∏ j ∈ Finset.univ.erase i, a j := by
        dsimp [R]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [r]
        rw [← Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)]
        field_simp [(hap i).ne'] <;> ring

section SeminormInterpolation

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  {p : ℕ → Seminorm ℝ E}

/-- The precise interpolation hypothesis in `HasInterpolation` gives one
common base and loss for every positive arity and every allocation of at most
`s` ordinary derivatives.  The two extra derivatives on each factor are the
fixed cylinder evaluation cost. -/
theorem HasInterpolation.oneHigh_product
    (hinterp : HasInterpolation p) (hp : Monotone p) :
    ∃ base loss : ℕ, 2 ≤ base ∧ ∀ k s : ℕ, ∀ d : Fin (k + 1) → ℕ,
      (∑ i, d i) ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Fin (k + 1) → E,
        (∏ i, p (d i + 2) (v i)) ≤
          C * ∑ i, p (s + loss) (v i) * ∏ j ∈ Finset.univ.erase i, p base (v j) := by
  classical
  obtain ⟨interpBase, interpLoss, hI⟩ := hinterp
  let B : ℕ := max interpBase (interpLoss + 2)
  let L : ℕ := B + interpLoss + 3
  have hIB : interpBase ≤ B := le_max_left _ _
  have hLB : interpLoss + 2 ≤ B := le_max_right _ _
  have hB : 2 ≤ B := by omega
  refine ⟨B, L, hB, ?_⟩
  intro k s d hd
  let H : ℕ := s + L
  let den : ℝ := (H : ℝ) - (B : ℝ)
  have hdeneq : den = (s : ℝ) + (interpLoss : ℝ) + 3 := by
    dsimp [den, H, L]
    push_cast
    ring
  have hden : 0 < den := by rw [hdeneq]; positivity
  have hdi (i : Fin (k + 1)) : d i ≤ s :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hd
  have hhigh (i : Fin (k + 1)) : d i + 2 + interpLoss < H := by
    dsimp [H, L]
    have := hdi i
    omega
  have hBH : B ≤ H := by dsimp [H, L]; omega
  let θ : Fin (k + 1) → ℝ := fun i =>
    if d i + 2 ≤ B then 0 else
      (((d i + 2 : ℕ) : ℝ) - (B : ℝ) + (interpLoss : ℝ)) / den
  have hθ0 (i : Fin (k + 1)) : 0 ≤ θ i := by
    dsimp [θ]
    split_ifs with hi
    · exact le_rfl
    · apply div_nonneg _ hden.le
      have hlt : (B : ℝ) < ((d i + 2 : ℕ) : ℝ) := by exact_mod_cast (lt_of_not_ge hi)
      linarith [Nat.cast_nonneg (α := ℝ) interpLoss]
  have hθlt (i : Fin (k + 1)) : θ i < 1 := by
    dsimp [θ]
    split_ifs with hi
    · exact zero_lt_one
    · apply (div_lt_one hden).mpr
      have hlt : ((d i + 2 : ℕ) : ℝ) + (interpLoss : ℝ) < (H : ℝ) := by
        exact_mod_cast hhigh i
      dsimp [den]
      linarith
  have hθd (i : Fin (k + 1)) : θ i ≤ (d i : ℝ) / den := by
    dsimp [θ]
    split_ifs with hi
    · exact div_nonneg (Nat.cast_nonneg _) hden.le
    · apply div_le_div_of_nonneg_right _ hden.le
      have hlow : (interpLoss : ℝ) + 2 ≤ (B : ℝ) := by exact_mod_cast hLB
      push_cast
      linarith
  have hθsum : (∑ i, θ i) ≤ 1 := by
    calc
      (∑ i, θ i) ≤ ∑ i, (d i : ℝ) / den := Finset.sum_le_sum (fun i _ => hθd i)
      _ = ((∑ i, d i : ℕ) : ℝ) / den := by
        rw [← Finset.sum_div, Nat.cast_sum]
      _ ≤ (s : ℝ) / den :=
        div_le_div_of_nonneg_right (by exact_mod_cast hd) hden.le
      _ ≤ 1 := by
        apply (div_le_one hden).mpr
        rw [hdeneq]
        linarith [Nat.cast_nonneg (α := ℝ) interpLoss]
  have hfactor (i : Fin (k + 1)) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E,
        p (d i + 2) x ≤ C * ((p B x) ^ (1 - θ i) * (p H x) ^ θ i) := by
    by_cases hi : d i + 2 ≤ B
    · refine ⟨1, zero_le_one, fun x => ?_⟩
      simpa only [θ, if_pos hi, sub_zero, Real.rpow_one, Real.rpow_zero,
        mul_one, one_mul] using hp hi x
    · obtain ⟨C, hC, hCx⟩ := hI B (d i + 2) H hIB (lt_of_not_ge hi) (hhigh i)
      refine ⟨C, hC, fun x => ?_⟩
      have hθeq : θ i =
          (((d i + 2 : ℕ) : ℝ) - (B : ℝ) + (interpLoss : ℝ)) / den := by
        simp only [θ, if_neg hi]
      have hloweq : ((H : ℝ) - ((d i + 2 : ℕ) : ℝ) - (interpLoss : ℝ)) /
          ((H : ℝ) - (B : ℝ)) = 1 - θ i := by
        rw [hθeq]
        change ((H : ℝ) - ((d i + 2 : ℕ) : ℝ) - (interpLoss : ℝ)) / den = _
        field_simp [hden.ne'] <;> dsimp [den] <;> ring
      have h := hCx x
      rw [hloweq] at h
      change p (d i + 2) x ≤
        C * (p B x) ^ (1 - θ i) *
          (p H x) ^ ((((d i + 2 : ℕ) : ℝ) - (B : ℝ) + (interpLoss : ℝ)) / den) at h
      rw [← hθeq, mul_assoc] at h
      exact h
  choose C hC hCx using hfactor
  refine ⟨∏ i, C i, Finset.prod_nonneg (fun i _ => hC i), ?_⟩
  intro v
  calc
    (∏ i, p (d i + 2) (v i)) ≤
        ∏ i, C i * ((p B (v i)) ^ (1 - θ i) * (p H (v i)) ^ θ i) :=
      Finset.prod_le_prod₀ (fun i _ => apply_nonneg _ _) (fun i _ => hCx i (v i))
    _ = (∏ i, C i) * ∏ i, (p B (v i)) ^ (1 - θ i) * (p H (v i)) ^ θ i :=
      Finset.prod_mul_distrib
    _ ≤ (∏ i, C i) *
        ∑ i, p H (v i) * ∏ j ∈ Finset.univ.erase i, p B (v j) :=
      mul_le_mul_of_nonneg_left
        (prod_interpolated_le_oneHigh (fun i => p B (v i)) (fun i => p H (v i)) θ
          (fun _ => apply_nonneg _ _) (fun i => hp hBH (v i)) hθ0 hθlt hθsum)
        (Finset.prod_nonneg (fun i _ => hC i))

end SeminormInterpolation

end ContinuousFlexibility.Statements
