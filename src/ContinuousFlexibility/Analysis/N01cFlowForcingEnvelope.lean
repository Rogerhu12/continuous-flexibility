import ContinuousFlexibility.Analysis.N01cCircleForcingProducts
import ContinuousFlexibility.Analysis.N01cFlowForcingSobolev

/-!
# Retaining one material factor in the variational forcing

The distinguished factor is the actual speed jet. Its material weight
survives whether the one high Sobolev norm falls on that factor or on a
lower variation. The remaining factors contribute only a polynomial in
fixed lower spatial orders.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators

/-- One designated factor keeps its weight in a nonnegative product. -/
theorem n01c_prod_le_marked_factor {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (i₀ : ι) (hi₀ : i₀ ∈ s)
    (f : ι → ℝ) {W B : ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hW : 0 ≤ W) (hB : 0 ≤ B)
    (hmarked : f i₀ ≤ W * B)
    (hother : ∀ i ∈ s, i ≠ i₀ → f i ≤ B) :
    ∏ i ∈ s, f i ≤ W * B ^ s.card := by
  have hprod : ∏ i ∈ s.erase i₀, f i ≤ B ^ (s.erase i₀).card := by
    calc
      _ ≤ ∏ _i ∈ s.erase i₀, B := Finset.prod_le_prod₀
        (fun i hi => hf i (Finset.mem_of_mem_erase hi))
        (fun i hi => hother i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi))
      _ = _ := by rw [Finset.prod_const]
  have hcard : (s.erase i₀).card + 1 = s.card := Finset.card_erase_add_one hi₀
  calc
    ∏ i ∈ s, f i = (∏ i ∈ s.erase i₀, f i) * f i₀ :=
      (Finset.prod_erase_mul s f hi₀).symm
    _ ≤ B ^ (s.erase i₀).card * (W * B) :=
      mul_le_mul hprod hmarked (hf i₀ hi₀) (pow_nonneg hB _)
    _ = W * B ^ ((s.erase i₀).card + 1) := by rw [pow_succ]; ring
    _ = W * B ^ s.card := by rw [hcard]

/-- The material weight remains once in every term of a one-high sum. -/
theorem n01c_oneHigh_sum_le_marked {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) (high low : ι → ℝ) {W A B : ℝ}
    (hhigh : ∀ i, 0 ≤ high i) (hlow : ∀ i, 0 ≤ low i)
    (hW : 0 ≤ W) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hheadHigh : high i₀ ≤ W * A) (hheadLow : low i₀ ≤ W * B)
    (hotherHigh : ∀ i, i ≠ i₀ → high i ≤ A)
    (hotherLow : ∀ i, i ≠ i₀ → low i ≤ B) :
    ∑ j, high j * ∏ i ∈ Finset.univ.erase j, low i ≤
      (Fintype.card ι : ℝ) * W * A * B ^ Fintype.card ι := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hterm (j : ι) :
      high j * ∏ i ∈ Finset.univ.erase j, low i ≤
        W * A * B ^ Fintype.card ι := by
    by_cases hj : j = i₀
    · subst j
      have hp : ∏ i ∈ Finset.univ.erase i₀, low i ≤ B ^ Fintype.card ι := by
        calc
          _ ≤ ∏ _i ∈ Finset.univ.erase i₀, B :=
            Finset.prod_le_prod₀ (fun i _ => hlow i)
              (fun i hi => hotherLow i (Finset.ne_of_mem_erase hi))
          _ = B ^ (Finset.univ.erase i₀).card := by rw [Finset.prod_const]
          _ ≤ B ^ Fintype.card ι := pow_le_pow_right₀ hB
            (by simpa only [Finset.card_univ] using Finset.card_erase_le
              (Finset.univ : Finset ι) i₀)
      exact mul_le_mul hheadHigh hp
        (Finset.prod_nonneg (fun i _ => hlow i)) (mul_nonneg hW hA)
    · have hmem : i₀ ∈ Finset.univ.erase j := Finset.mem_erase.mpr
        ⟨Ne.symm hj, Finset.mem_univ _⟩
      have hp₀ := n01c_prod_le_marked_factor (Finset.univ.erase j) i₀ hmem low
        (fun i _ => hlow i) hW hB0 hheadLow
        (fun i _ hi => hotherLow i hi)
      have hp : ∏ i ∈ Finset.univ.erase j, low i ≤
          W * B ^ Fintype.card ι :=
        hp₀.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hB
            (by simpa only [Finset.card_univ] using Finset.card_erase_le
              (Finset.univ : Finset ι) j)) hW)
      calc
        _ ≤ A * (W * B ^ Fintype.card ι) :=
          mul_le_mul (hotherHigh j hj) hp
            (Finset.prod_nonneg (fun i _ => hlow i)) hA
        _ = _ := by ring
  calc
    _ ≤ ∑ _j : ι, W * A * B ^ Fintype.card ι :=
      Finset.sum_le_sum (fun j _ => hterm j)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- A uniform polynomial form suitable for all partition choices of a
fixed positive parameter order. Only the requested-order aggregate U
occurs linearly. -/
theorem n01c_oneHigh_sum_polynomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) (high low : ι → ℝ) (N : ℕ)
    (hcard : Fintype.card ι ≤ N + 1)
    {C W U R : ℝ} (hC : 1 ≤ C) (hW : 0 ≤ W) (hU : 0 ≤ U) (hR : 1 ≤ R)
    (hhigh : ∀ i, 0 ≤ high i) (hlow : ∀ i, 0 ≤ low i)
    (hheadHigh : high i₀ ≤ C * W * U * R)
    (hheadLow : low i₀ ≤ C * W * R ^ 2)
    (hotherHigh : ∀ i, i ≠ i₀ → high i ≤ C * U)
    (hotherLow : ∀ i, i ≠ i₀ → low i ≤ C * R) :
    ∑ j, high j * ∏ i ∈ Finset.univ.erase j, low i ≤
      ((N : ℝ) + 1) * C ^ (N + 2) * W * U * R ^ (2 * N + 3) := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hRR : R ≤ R ^ 2 := by nlinarith
  have hB : 1 ≤ C * R ^ 2 :=
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hR)
  have hb := n01c_oneHigh_sum_le_marked i₀ high low hhigh hlow hW
    (mul_nonneg (mul_nonneg hC0 hU) hR0) hB
    (by nlinarith [hheadHigh])
    (by nlinarith [hheadLow])
    (fun i hi => (hotherHigh i hi).trans
      (le_mul_of_one_le_right (mul_nonneg hC0 hU) hR))
    (fun i hi => (hotherLow i hi).trans
      (mul_le_mul_of_nonneg_left hRR hC0))
  have hpow := pow_le_pow_right₀ hB hcard
  have hcardR : (Fintype.card ι : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hcard
  have hnonneg : 0 ≤ W * (C * U * R) * (C * R ^ 2) ^ Fintype.card ι := by
    positivity
  calc
    _ ≤ (Fintype.card ι : ℝ) * W * (C * U * R) *
        (C * R ^ 2) ^ Fintype.card ι := hb
    _ ≤ ((N : ℝ) + 1) * W * (C * U * R) * (C * R ^ 2) ^ (N + 1) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcardR hW) (by positivity)
      · exact hpow
      · positivity
      · positivity
    _ = _ := by
      have hCp : C ^ (N + 2) = C ^ (N + 1) * C := pow_succ C (N + 1)
      have hRp : R ^ (2 * N + 3) = R ^ (2 * (N + 1)) * R := by
        rw [show 2 * N + 3 = 2 * (N + 1) + 1 by omega, pow_succ]
      rw [hCp, hRp, mul_pow, ← pow_mul]
      ring

/-- The exact finite Sobolev forcing majorant preserves the marked
material weight and has a parameter-order polynomial degree. -/
theorem n01c_forcingMajorant_polynomial
    (P : ℝ) (N s : ℕ)
    (high low : ∀ ω : FlowForcingChoice N, Fin (ω.1.length + 1) → ℝ)
    {C W U R : ℝ} (hC : 1 ≤ C) (hW : 0 ≤ W) (hU : 0 ≤ U) (hR : 1 ≤ R)
    (hhigh : ∀ ω i, 0 ≤ high ω i) (hlow : ∀ ω i, 0 ≤ low ω i)
    (hheadHigh : ∀ ω, high ω 0 ≤ C * W * U * R)
    (hheadLow : ∀ ω, low ω 0 ≤ C * W * R ^ 2)
    (hotherHigh : ∀ ω i, high ω i.succ ≤ C * U)
    (hotherLow : ∀ ω i, low ω i.succ ≤ C * R) :
    (2 : ℝ) ^ (s + 1) *
      ∑ ω : FlowForcingChoice N, circleProductSobolevConstant P ω.1.length s *
        ∑ j, high ω j * ∏ i ∈ Finset.univ.erase j, low ω i ≤
      ((2 : ℝ) ^ (s + 1) *
        (∑ ω : FlowForcingChoice N, circleProductSobolevConstant P ω.1.length s) *
        ((N : ℝ) + 1) * C ^ (N + 2)) * W * U * R ^ (2 * N + 3) := by
  classical
  have hterm (ω : FlowForcingChoice N) :
      ∑ j, high ω j * ∏ i ∈ Finset.univ.erase j, low ω i ≤
        ((N : ℝ) + 1) * C ^ (N + 2) * W * U * R ^ (2 * N + 3) := by
    apply n01c_oneHigh_sum_polynomial 0 (high ω) (low ω) N
      (by simpa only [Fintype.card_fin] using Nat.add_le_add_right ω.1.length_le 1)
      hC hW hU hR (hhigh ω) (hlow ω) (hheadHigh ω) (hheadLow ω)
    · intro i
      refine Fin.cases ?_ ?_ i
      · intro hi
        exact False.elim (hi rfl)
      · intro j _
        exact hotherHigh ω j
    · intro i
      refine Fin.cases ?_ ?_ i
      · intro hi
        exact False.elim (hi rfl)
      · intro j _
        exact hotherLow ω j
  calc
    _ ≤ (2 : ℝ) ^ (s + 1) *
        ∑ ω : FlowForcingChoice N, circleProductSobolevConstant P ω.1.length s *
          (((N : ℝ) + 1) * C ^ (N + 2) * W * U * R ^ (2 * N + 3)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hterm ω)
        (zero_le_one.trans (circleProductSobolevConstant_one_le P ω.1.length s)))
    _ = _ := by rw [← Finset.sum_mul]; ring

end ContinuousFlexibility.Analysis
