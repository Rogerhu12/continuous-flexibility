module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The four blocks of the outer inverse

The core kernel and the deep Dirichlet inverse act on different `L²`
spaces.  Their coupling is rank one.  This file constructs the resulting
continuous linear map, rather than postulating a bounded assembled inverse,
and proves its operator bound with all powers of the flux scale explicit.

The intermediate product carries the maximum norm.  No Hilbert norm on
that product is used.  The individual core and tail spaces are Hilbert
spaces, as needed for their rank-one operators.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousLinearMap InnerProductSpace

section Blocks

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual bounded operator with the indicated four blocks. -/
def outerBlockMatrix (A : E →L[ℝ] E) (B : F →L[ℝ] E)
    (C : E →L[ℝ] F) (D : F →L[ℝ] F) : (E × F) →L[ℝ] (E × F) :=
  ((A.comp (fst ℝ E F)) + (B.comp (snd ℝ E F))).prod
    ((C.comp (fst ℝ E F)) + (D.comp (snd ℝ E F)))

theorem outerBlockMatrix_apply (A : E →L[ℝ] E) (B : F →L[ℝ] E)
    (C : E →L[ℝ] F) (D : F →L[ℝ] F) (x : E × F) :
    outerBlockMatrix A B C D x = (A x.1 + B x.2, C x.1 + D x.2) := by
  simp only [outerBlockMatrix, prod_apply, add_apply, comp_apply, coe_fst', coe_snd']

private theorem norm_comp_fst_le {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (A : E →L[ℝ] G) : ‖A.comp (fst ℝ E F)‖ ≤ ‖A‖ := by
  calc
    ‖A.comp (fst ℝ E F)‖ ≤ ‖A‖ * ‖fst ℝ E F‖ := A.opNorm_comp_le _
    _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left (norm_fst_le ℝ E F) (norm_nonneg A)
    _ = ‖A‖ := mul_one _

private theorem norm_comp_snd_le {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (A : F →L[ℝ] G) : ‖A.comp (snd ℝ E F)‖ ≤ ‖A‖ := by
  calc
    ‖A.comp (snd ℝ E F)‖ ≤ ‖A‖ * ‖snd ℝ E F‖ := A.opNorm_comp_le _
    _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left (norm_snd_le ℝ E F) (norm_nonneg A)
    _ = ‖A‖ := mul_one _

/-- Row-sum bound for the assembled operator in the maximum product norm. -/
theorem norm_outerBlockMatrix_le (A : E →L[ℝ] E) (B : F →L[ℝ] E)
    (C : E →L[ℝ] F) (D : F →L[ℝ] F) :
    ‖outerBlockMatrix A B C D‖ ≤ max (‖A‖ + ‖B‖) (‖C‖ + ‖D‖) := by
  unfold outerBlockMatrix
  rw [opNorm_prod, Prod.norm_def]
  exact max_le_max
    ((norm_add_le _ _).trans (add_le_add (norm_comp_fst_le A) (norm_comp_snd_le B)))
    ((norm_add_le _ _).trans (add_le_add (norm_comp_fst_le C) (norm_comp_snd_le D)))

end Blocks

section GreenBlocks

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The outer Green construction from its core block, deep Dirichlet block,
core left solution, and normalized deep Poisson solution.  In the kernel
construction `alpha = V(c) / λ` and `beta = U(c) V(c) / λ`. -/
def outerBlockOperator (C : E →L[ℝ] E) (D : F →L[ℝ] F)
    (u : E) (p : F) (alpha beta : ℝ) : (E × F) →L[ℝ] (E × F) :=
  outerBlockMatrix C (alpha • rankOne ℝ u p) (alpha • rankOne ℝ p u)
    (D + beta • rankOne ℝ p p)

theorem outerBlockOperator_apply (C : E →L[ℝ] E) (D : F →L[ℝ] F)
    (u : E) (p : F) (alpha beta : ℝ) (x : E × F) :
    outerBlockOperator C D u p alpha beta x =
      (C x.1 + alpha • (inner ℝ p x.2 • u),
        alpha • (inner ℝ u x.1 • p) + D x.2 + beta • (inner ℝ p x.2 • p)) := by
  simp only [outerBlockOperator, outerBlockMatrix_apply, smul_apply, rankOne_apply, add_apply,
    add_assoc]

/-- The deep/deep block is the Dirichlet inverse plus its rank-one correction. -/
theorem outerBlockOperator_tail_apply (C : E →L[ℝ] E) (D : F →L[ℝ] F)
    (u : E) (p : F) (alpha beta : ℝ) (g : F) :
    (outerBlockOperator C D u p alpha beta (0, g)).2 =
      D g + beta • (inner ℝ p g • p) := by
  rw [outerBlockOperator_apply]
  simp only [inner_zero_right, zero_smul, smul_zero, zero_add]

/-- A bound using only the norms of the actual four ingredients. -/
theorem norm_outerBlockOperator_le_rows (C : E →L[ℝ] E) (D : F →L[ℝ] F)
    (u : E) (p : F) (alpha beta : ℝ) :
    ‖outerBlockOperator C D u p alpha beta‖ ≤
      max (‖C‖ + |alpha| * (‖u‖ * ‖p‖))
        (|alpha| * (‖u‖ * ‖p‖) + ‖D‖ + |beta| * ‖p‖ ^ 2) := by
  have hD : ‖D + beta • rankOne ℝ p p‖ ≤ ‖D‖ + |beta| * ‖p‖ ^ 2 := by
    calc
      _ ≤ ‖D‖ + ‖beta • rankOne ℝ p p‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul, Real.norm_eq_abs, norm_rankOne, pow_two]
  have h := norm_outerBlockMatrix_le C (alpha • rankOne ℝ u p)
    (alpha • rankOne ℝ p u) (D + beta • rankOne ℝ p p)
  dsimp only [outerBlockOperator]
  refine h.trans (max_le_max ?_ ?_)
  · simpa only [norm_smul, Real.norm_eq_abs, norm_rankOne] using
      (le_refl (‖C‖ + |alpha| * (‖u‖ * ‖p‖)))
  · calc
      ‖alpha • rankOne ℝ p u‖ + ‖D + beta • rankOne ℝ p p‖
          ≤ ‖alpha • rankOne ℝ p u‖ + (‖D‖ + |beta| * ‖p‖ ^ 2) :=
        add_le_add le_rfl hD
      _ = _ := by rw [norm_smul, Real.norm_eq_abs, norm_rankOne]; ring

/-- The factors `√λ` on the two sides cancel the kernel factor `λ⁻¹`. -/
theorem outer_cross_scale_cancel {lam A K alpha : ℝ} (hlam : 0 < lam)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (u : E) (p : F)
    (halpha : |alpha| ≤ K / lam)
    (hu : ‖u‖ ≤ Real.sqrt lam * A * K) (hp : ‖p‖ ≤ Real.sqrt lam * A) :
    |alpha| * (‖u‖ * ‖p‖) ≤ A ^ 2 * K ^ 2 := by
  calc
    |alpha| * (‖u‖ * ‖p‖)
        ≤ (K / lam) * ((Real.sqrt lam * A * K) * (Real.sqrt lam * A)) :=
      mul_le_mul halpha
        (mul_le_mul hu hp (norm_nonneg p) (mul_nonneg (mul_nonneg
          (Real.sqrt_nonneg _) hA) hK))
        (mul_nonneg (norm_nonneg u) (norm_nonneg p)) (div_nonneg hK hlam.le)
    _ = (Real.sqrt lam ^ 2 / lam) * (A ^ 2 * K ^ 2) := by ring
    _ = A ^ 2 * K ^ 2 := by rw [Real.sq_sqrt hlam.le, div_self hlam.ne', one_mul]

/-- The two Poisson norms cancel the scale in the deep rank-one correction. -/
theorem outer_tail_scale_cancel {lam A K beta : ℝ} (hlam : 0 < lam)
    (hA : 0 ≤ A) (p : F) (hbeta : |beta| ≤ K ^ 2 / lam)
    (hp : ‖p‖ ≤ Real.sqrt lam * A) :
    |beta| * ‖p‖ ^ 2 ≤ A ^ 2 * K ^ 2 := by
  calc
    |beta| * ‖p‖ ^ 2 ≤ (K ^ 2 / lam) * (Real.sqrt lam * A) ^ 2 :=
      mul_le_mul hbeta (pow_le_pow_left₀ (norm_nonneg p) hp 2)
        (sq_nonneg _) (div_nonneg (sq_nonneg K) hlam.le)
    _ = (Real.sqrt lam ^ 2 / lam) * (A ^ 2 * K ^ 2) := by ring
    _ = A ^ 2 * K ^ 2 := by rw [Real.sq_sqrt hlam.le, div_self hlam.ne', one_mul]

/-- The outer inverse has a uniform bound independent of the flux scale.
The numerical hypotheses are the core mass/transfer and deep-tail bounds;
the bounded assembled operator is explicitly constructed above. -/
theorem norm_outerBlockOperator_le {lam A K d alpha beta : ℝ} (hlam : 0 < lam)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hd : 0 ≤ d)
    (C : E →L[ℝ] E) (D : F →L[ℝ] F) (u : E) (p : F)
    (hC : ‖C‖ ≤ A ^ 2 * K ^ 2) (hD : ‖D‖ ≤ d)
    (halpha : |alpha| ≤ K / lam) (hbeta : |beta| ≤ K ^ 2 / lam)
    (hu : ‖u‖ ≤ Real.sqrt lam * A * K) (hp : ‖p‖ ≤ Real.sqrt lam * A) :
    ‖outerBlockOperator C D u p alpha beta‖ ≤ d + 2 * A ^ 2 * K ^ 2 := by
  have hcross := outer_cross_scale_cancel hlam hA hK u p halpha hu hp
  have htail := outer_tail_scale_cancel hlam hA p hbeta hp
  refine (norm_outerBlockOperator_le_rows C D u p alpha beta).trans (max_le ?_ ?_)
  · nlinarith
  · nlinarith

end GreenBlocks

section Localization

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Exact localized norm of a rank-one term.  For real multiplication
localizers the adjoint is the same localizer. -/
theorem norm_outer_localized_rankOne (L M : H →L[ℝ] H) (p : H) (beta : ℝ) :
    ‖(L.comp (beta • rankOne ℝ p p)).comp M‖ =
      |beta| * (‖L p‖ * ‖M.adjoint p‖) := by
  rw [comp_smul, smul_comp, comp_rankOne, rankOne_comp, norm_smul,
    Real.norm_eq_abs, norm_rankOne]

/-- Two decays from the tail entrance dominate the required off-diagonal decay. -/
theorem outer_product_decay_le {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Real.exp (-s) * Real.exp (-t) ≤ Real.exp (-|s - t|) := by
  have habs : |s - t| ≤ s + t := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- The deep rank-one correction has the same cell-to-cell decay as the
Dirichlet Green kernel. -/
theorem norm_outer_localized_rankOne_le {A B beta s t : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (L M : H →L[ℝ] H) (p : H)
    (hL : ‖L p‖ ≤ A * Real.exp (-s))
    (hM : ‖M.adjoint p‖ ≤ B * Real.exp (-t)) :
    ‖(L.comp (beta • rankOne ℝ p p)).comp M‖ ≤
      |beta| * A * B * Real.exp (-|s - t|) := by
  rw [norm_outer_localized_rankOne]
  calc
    |beta| * (‖L p‖ * ‖M.adjoint p‖)
        ≤ |beta| * ((A * Real.exp (-s)) * (B * Real.exp (-t))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hL hM (norm_nonneg _) (mul_nonneg hA (Real.exp_pos _).le))
        (abs_nonneg beta)
    _ = (|beta| * A * B) * (Real.exp (-s) * Real.exp (-t)) := by ring
    _ ≤ (|beta| * A * B) * Real.exp (-|s - t|) :=
      mul_le_mul_of_nonneg_left (outer_product_decay_le hs ht)
        (mul_nonneg (mul_nonneg (abs_nonneg _) hA) hB)

end Localization

end ContinuousFlexibility.Radial
