import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryKernelBounds
import ContinuousFlexibility.Analysis.PointwiseAffineMaterialJets
import ContinuousFlexibility.Analysis.N04RealizationEnvelopeComposition
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Polynomial material costs of actual multilinear evaluation

The evaluation kernel is the diagonal of an actual continuous
multilinear map. Its ordinary derivatives therefore have a polynomial
bound in the values of the operator and its arguments. The constants
depend only on the finite orders and the normed spaces.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Restriction of a fixed continuous multilinear map to a linear
diagonal has polynomially bounded ordinary jets. -/
theorem n04PositiveGeometry_multilinearDiagonal_prefix
    {ι : Type*} [Fintype ι]
    (A : ContinuousMultilinearMap ℝ (fun _ : ι => F) G)
    (L : E →L[ℝ] (ι → F)) (hL : ‖L‖ ≤ 1) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ M : ℝ, 1 ≤ M → ∀ z : E, ‖z‖ ≤ M →
      ∀ j : ℕ, j ≤ N →
        ‖iteratedFDeriv ℝ j (A ∘ L) z‖ ≤ C * M ^ Fintype.card ι := by
  classical
  let C : ℝ := 1 + ∑ j ∈ Finset.range (N + 1),
    ((Fintype.card ι).descFactorial j : ℝ) * ‖A‖
  have hC : 1 ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg
    (fun j _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)))
  refine ⟨C, hC, ?_⟩
  intro M hM z hz j hj
  have hpoint : ‖L z‖ ≤ M := (L.le_opNorm z).trans
    ((mul_le_mul_of_nonneg_right hL (norm_nonneg z)).trans
      (by simpa only [one_mul] using hz))
  have hp : ‖L‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) hL
  have hcomp := norm_iteratedFDeriv_comp_linear_le_at L
    (A.contDiff.contDiffAt (x := L z)) j
  have hbase : ‖iteratedFDeriv ℝ j (A ∘ L) z‖ ≤
      ‖iteratedFDeriv ℝ j A (L z)‖ := hcomp.trans
    ((mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (mul_one _))
  have hcoef : ((Fintype.card ι).descFactorial j : ℝ) * ‖A‖ ≤ C :=
    (Finset.single_le_sum (fun k _ => mul_nonneg (Nat.cast_nonneg
      ((Fintype.card ι).descFactorial k)) (norm_nonneg A))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))).trans
      (le_add_of_nonneg_left zero_le_one)
  have hpow : ‖L z‖ ^ (Fintype.card ι - j) ≤ M ^ Fintype.card ι :=
    (pow_le_pow_left₀ (norm_nonneg _) hpoint _).trans
      (pow_le_pow_right₀ hM (Nat.sub_le _ _))
  exact (hbase.trans (A.norm_iteratedFDeriv_le j (L z))).trans
    (mul_le_mul hcoef hpow (pow_nonneg (norm_nonneg _) _)
      (zero_le_one.trans hC))

/-- The true variable multilinear evaluation kernel, including its
zeroth jet, has a common material polynomial on every finite prefix. -/
theorem n04PositiveGeometry_multilinearEvaluation_prefix (n N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ M : ℝ, 1 ≤ M →
      ∀ z : (E [×n]→L[ℝ] F) × (Fin n → E), ‖z‖ ≤ M →
      ∀ j : ℕ, j ≤ N →
        ‖iteratedFDeriv ℝ j
          (fun p : (E [×n]→L[ℝ] F) × (Fin n → E) => p.1 p.2) z‖ ≤
          C * M ^ (n + 1) := by
  let V := (E [×n]→L[ℝ] F) × (Fin n → E)
  let I : (E [×n]→L[ℝ] F) →L[ℝ] (E [×n]→L[ℝ] F) :=
    ContinuousLinearMap.id ℝ _
  let A : ContinuousMultilinearMap ℝ (fun _ : Option (Fin n) => V) F :=
    I.continuousMultilinearMapOption
  let L : V →L[ℝ] (Option (Fin n) → V) :=
    ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ V)
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    rw [one_mul]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
    intro i
    exact le_rfl
  have he : (fun p : V => p.1 p.2) = A ∘ L := by
    funext p
    change p.1 p.2 = I.continuousMultilinearMapOption (fun _ => p)
    rw [ContinuousLinearMap.continuousMultilinearMapOption_apply_eq_self]
    rfl
  obtain ⟨C, hC, hb⟩ := n04PositiveGeometry_multilinearDiagonal_prefix A L hL N
  refine ⟨C, hC, ?_⟩
  intro M hM z hz j hj
  rw [he]
  simpa only [Fintype.card_option, Fintype.card_fin] using hb M hM z hz j hj

private theorem linear_prefix {M : ℝ} (hM : 1 ≤ M)
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) (z : E) (hz : ‖z‖ ≤ M)
    (k : ℕ) : ‖iteratedFDeriv ℝ k L z‖ ≤ M := by
  cases k with
  | zero =>
      rw [norm_iteratedFDeriv_zero]
      exact (L.le_opNorm z).trans
        ((mul_le_mul_of_nonneg_right hL (norm_nonneg z)).trans
          (by simpa only [one_mul] using hz))
  | succ k => exact (flowJet_norm_iteratedFDeriv_clm_le L
      (Nat.succ_pos k) z).trans (hL.trans hM)

/-- The signed application used by the inverse recurrence is a
bilinear kernel with the same quadratic material cost. -/
theorem n04PositiveGeometry_negClmEvaluation_prefix
    (N : ℕ) {M : ℝ} (hM : 1 ≤ M)
    (z : (E →L[ℝ] F) × E) (hz : ‖z‖ ≤ M)
    (j : ℕ) (hj : j ≤ N) :
    ‖iteratedFDeriv ℝ j (fun p : (E →L[ℝ] F) × E => -p.1 p.2) z‖ ≤
      (2 : ℝ) ^ N * M ^ 2 := by
  let B : (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F := -ContinuousLinearMap.id ℝ _
  have hB : ‖B‖ ≤ 1 := by
    change ‖-(ContinuousLinearMap.id ℝ (E →L[ℝ] F))‖ ≤ 1
    rw [ContinuousLinearMap.opNorm_neg]
    exact ContinuousLinearMap.norm_id_le
  have hraw := n04Realization_norm_iteratedFDeriv_bilinear_le_at B
    (contDiffAt_fst (p := z)) (contDiffAt_snd (p := z)) j
  have hsum : (∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) *
      ‖iteratedFDeriv ℝ k (fun p : (E →L[ℝ] F) × E => p.1) z‖ *
      ‖iteratedFDeriv ℝ (j - k) (fun p : (E →L[ℝ] F) × E => p.2) z‖) ≤
      (2 : ℝ) ^ N * M ^ 2 := by
    calc
      _ ≤ ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * M ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        have hb := mul_le_mul
          (mul_le_mul_of_nonneg_left
            (linear_prefix hM (ContinuousLinearMap.fst ℝ (E →L[ℝ] F) E)
              (ContinuousLinearMap.norm_fst_le ℝ (E →L[ℝ] F) E) z hz k)
            (Nat.cast_nonneg (j.choose k)))
          (linear_prefix hM (ContinuousLinearMap.snd ℝ (E →L[ℝ] F) E)
            (ContinuousLinearMap.norm_snd_le ℝ (E →L[ℝ] F) E) z hz (j - k))
          (ContinuousMultilinearMap.opNorm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hM))
        exact hb.trans_eq (by ring)
      _ = (2 : ℝ) ^ j * M ^ 2 := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose j
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj) (sq_nonneg M)
  have hsum₀ : 0 ≤ ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) *
      ‖iteratedFDeriv ℝ k (fun p : (E →L[ℝ] F) × E => p.1) z‖ *
      ‖iteratedFDeriv ℝ (j - k) (fun p : (E →L[ℝ] F) × E => p.2) z‖ :=
    Finset.sum_nonneg (fun k _ => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (ContinuousMultilinearMap.opNorm_nonneg _))
      (ContinuousMultilinearMap.opNorm_nonneg _))
  exact hraw.trans ((mul_le_mul_of_nonneg_right hB hsum₀).trans
    (by simpa only [one_mul] using hsum))

end ContinuousFlexibility.Analysis
