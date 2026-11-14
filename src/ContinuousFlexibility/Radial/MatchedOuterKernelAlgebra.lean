module

public import ContinuousFlexibility.Radial.OuterKernelEnvelopeAlgebra

/-!
# The core and return terms preserve the full cell attenuation

All exponents are chosen before the transition index.  The near-label
bounds are applied only to the actual core labels; a tail label merely
has to lie beyond the transition up to the fixed overlap displacement.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real
open ContinuousFlexibility.Statements

/-- One exponent controls the four terms of the actual whole Green
decomposition, including its return through the core. -/
theorem exists_matchedOuter_whole_kernel_exponent
    {B₀ An Ak : ℝ} (hB₀ : 0 ≤ B₀) (hAn : 0 ≤ An) (hAk : 0 ≤ Ak) :
    ∃ A : ℝ, 0 < A ∧ ∀ N k m : ℕ, 1 ≤ N → 1 ≤ k → 1 ≤ m →
      (N ≤ k + 2 → k ≤ N + 2 → N ≤ m + 2 → m ≤ N + 2 →
        exp (B₀ * radialQ N) ≤
          exp (A * (radialQ k + radialQ m) - |radialS k - radialS m|)) ∧
      (N ≤ k + 2 → k ≤ N + 2 →
        exp (B₀ * radialQ N) *
          exp (An * (radialQ m + radialQ N) - |radialS m - radialS N|) ≤
            exp (A * (radialQ k + radialQ m) - |radialS k - radialS m|)) ∧
      (N ≤ k + 2 →
        exp (B₀ * radialQ N) *
          exp (An * (radialQ k + radialQ N) - |radialS k - radialS N|) *
          exp (An * (radialQ m + radialQ N) - |radialS m - radialS N|) ≤
            exp (A * (radialQ k + radialQ m) - |radialS k - radialS m|)) ∧
      exp (Ak * (radialQ k + radialQ m) - |radialS k - radialS m|) ≤
        exp (A * (radialQ k + radialQ m) - |radialS k - radialS m|) := by
  let B := B₀ + 2 * An
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨As, hAs, hshift⟩ := outer_localized_envelope_shift hB
  obtain ⟨Ar, hAr, hnear⟩ := outer_coefficient_weight_nearby hB
  let A := As + Ar + An + Ak + 1
  have hA : 0 < A := by dsimp only [A]; positivity
  have hAsA : As ≤ A := by dsimp only [A]; linarith only [hAr, hAn, hAk]
  have hArAnA : Ar + An ≤ A := by dsimp only [A]; linarith only [hAs, hAk]
  have hAnA : An ≤ A := by dsimp only [A]; linarith only [hAs, hAr, hAk]
  have hAkA : Ak ≤ A := by dsimp only [A]; linarith only [hAs, hAr, hAn]
  have hshift' : ∀ p q i k : ℕ, 1 ≤ p → 1 ≤ q → 1 ≤ i → 1 ≤ k →
      p ≤ i + 2 → i ≤ p + 2 → q ≤ k + 2 → k ≤ q + 2 →
      exp (B * (radialQ p + radialQ q) - |radialS p - radialS q|) ≤
        exp (A * (radialQ i + radialQ k) - |radialS i - radialS k|) := by
    intro p q i k hp hq hi hk hpi hip hqk hkq
    calc
      _ = radialE p ^ B * radialE q ^ B *
          exp (-|radialS p - radialS q|) := by
        rw [outer_radialE_rpow, outer_radialE_rpow, ← exp_add, ← exp_add]
        congr 1 <;> ring
      _ ≤ radialE i ^ As * radialE k ^ As *
          exp (-|radialS i - radialS k|) :=
        hshift p q i k hp hq hi hk hpi hip hqk hkq
      _ = exp (As * (radialQ i + radialQ k) -
          |radialS i - radialS k|) := by
        rw [outer_radialE_rpow, outer_radialE_rpow, ← exp_add, ← exp_add]
        congr 1 <;> ring
      _ ≤ _ := exp_le_exp.mpr (sub_le_sub_right
        (mul_le_mul_of_nonneg_right hAsA
          (add_nonneg (radialQ_nonneg i) (radialQ_nonneg k))) _)
  refine ⟨A, hA, ?_⟩
  intro N k m hN hk hm
  have hQN := radialQ_nonneg N
  have hQk := radialQ_nonneg k
  have hQm := radialQ_nonneg m
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hNk hkN hNm hmN
    apply le_trans _ (hshift' N N k m hN hN hk hm hNk hkN hNm hmN)
    simp only [sub_self, abs_zero, sub_zero]
    apply exp_le_exp.mpr
    have hb := mul_nonneg hB₀ hQN
    have ha := mul_nonneg hAn hQN
    dsimp only [B]
    nlinarith only [hb, ha]
  · intro hNk hkN
    apply le_trans _ (hshift' N m k m hN hm hk hm hNk hkN (by omega) (by omega))
    rw [← exp_add, abs_sub_comm (radialS m) (radialS N)]
    apply exp_le_exp.mpr
    have hb := mul_nonneg hB₀ hQm
    have haN := mul_nonneg hAn hQN
    have ham := mul_nonneg hAn hQm
    dsimp only [B]
    nlinarith only [hb, haN, ham]
  · intro hNk
    have hr := hnear N k hk hNk
    rw [outer_radialE_rpow, outer_radialE_rpow] at hr
    have hr' := exp_le_exp.mp hr
    have htri := abs_sub_le (radialS k) (radialS N) (radialS m)
    rw [abs_sub_comm (radialS N) (radialS m)] at htri
    rw [← exp_add, ← exp_add]
    apply exp_le_exp.mpr
    have hkA := mul_le_mul_of_nonneg_right hArAnA hQk
    have hmA := mul_le_mul_of_nonneg_right hAnA hQm
    dsimp only [B] at hr'
    nlinarith only [hr', htri, hkA, hmA]
  · exact exp_le_exp.mpr (sub_le_sub_right
      (mul_le_mul_of_nonneg_right hAkA (add_nonneg hQk hQm)) _)

end ContinuousFlexibility.Radial
