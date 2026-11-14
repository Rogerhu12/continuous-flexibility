module

public import ContinuousFlexibility.Analysis.OneHighCompositionJets
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Fixed finite-jet bounds for an actual exponential

The output amplitude is retained explicitly. Only positive-order
derivatives of the exponent enter the polynomial factor, so a large
constant logarithmic offset does not enter the derivative envelope.
This is a new reconstruction after the workspace reset.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators ContDiff

/-- The constant depends only on the order; the actual amplitude and
positive-order input jet envelope are supplied afterwards. -/
theorem exists_exp_finiteJet_polynomial_envelope
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {M A : ℝ}, 1 ≤ M → 0 ≤ A →
      ∀ (f : E → ℝ) (x : E), ContDiffAt ℝ ∞ f x → Real.exp (f x) ≤ A →
      (∀ k, 1 ≤ k → k ≤ N → ‖iteratedFDeriv ℝ k f x‖ ≤ M) →
      ∀ k, k ≤ N →
        ‖iteratedFDeriv ℝ k (fun y => Real.exp (f y)) x‖ ≤ C * A * M ^ N := by
  classical
  let K : ℕ → ℝ := fun k => Fintype.card (OrderedFinpartition k)
  have hK (k : ℕ) : 0 ≤ K k := Nat.cast_nonneg _
  let C : ℝ := 1 + ∑ j ∈ Finset.range (N + 1), K j
  have hC : 1 ≤ C := by
    have hp : 0 ≤ ∑ j ∈ Finset.range (N + 1), K j :=
      Finset.sum_nonneg fun j _ => hK j
    dsimp only [C]
    linarith only [hp]
  refine ⟨C, hC, ?_⟩
  intro M A hM hA f x hf hexp hraw k hk
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hout (j : ℕ) : ‖iteratedFDeriv ℝ j Real.exp (f x)‖ ≤ A := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
      Real.iter_deriv_exp, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hexp
  have hterm (π : OrderedFinpartition k) :
      ‖iteratedFDeriv ℝ π.length Real.exp (f x)‖ *
          ∏ j, ‖iteratedFDeriv ℝ (π.partSize j) f x‖ ≤ A * M ^ N := by
    have hprod : (∏ j, ‖iteratedFDeriv ℝ (π.partSize j) f x‖) ≤ M ^ π.length := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (Finset.prod_le_prod₀ (s := Finset.univ)
          (f := fun j : Fin π.length => ‖iteratedFDeriv ℝ (π.partSize j) f x‖)
          (g := fun _ : Fin π.length => M) (fun _ _ => norm_nonneg _)
          (fun j _ => hraw (π.partSize j) (π.partSize_pos j)
            ((π.partSize_le j).trans hk)))
    exact (mul_le_mul (hout π.length) hprod
      (Finset.prod_nonneg fun _ _ => norm_nonneg _) hA).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM (π.length_le.trans hk)) hA)
  have hcard : K k ≤ C := by
    have hm : k ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    exact (Finset.single_le_sum (fun j _ => hK j) hm).trans
      (le_add_of_nonneg_left zero_le_one)
  calc
    _ ≤ ∑ π : OrderedFinpartition k,
        ‖iteratedFDeriv ℝ π.length Real.exp (f x)‖ *
          ∏ j, ‖iteratedFDeriv ℝ (π.partSize j) f x‖ :=
      norm_iteratedFDeriv_comp_le_partition_sum Real.contDiff_exp.contDiffAt hf k
    _ ≤ ∑ _π : OrderedFinpartition k, A * M ^ N :=
      Finset.sum_le_sum fun π _ => hterm π
    _ = K k * (A * M ^ N) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, K]
    _ ≤ C * (A * M ^ N) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg hA (pow_nonneg hM0 _))
    _ = C * A * M ^ N := (mul_assoc _ _ _).symm

end ContinuousFlexibility.Analysis
