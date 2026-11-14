module

public import ContinuousFlexibility.Radial.MatchingMatrixAlgebra
public import ContinuousFlexibility.Blueprint.Statements

/-!
# The inverse of the two-cut matching matrix

The selected diagonal margin and the entrywise perturbation bound imply
invertibility of the matching matrix. The operator estimate already proved
in MatchingMatrixAlgebra gives the stronger entry bound 2 / margin;
the statement layer asks only for 4 / margin.
-/

@[expose] public section

noncomputable section

open Matrix

namespace ContinuousFlexibility.Radial

/-- The two-cut entrywise perturbation bound implies the inverse entry bound.
No symmetry of D is needed for this estimate. -/
theorem matchingK_inverse_entry_bound_two
    (a b d : Fin 2 → ℝ) (D : Matrix (Fin 2) (Fin 2) ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hab : ∀ i, a i ^ 2 + b i ^ 2 = 1)
    (hdiag : ∀ i, δ ≤ |a i * d i - b i|)
    (hentry : ∀ i j, |D i j - (if i = j then d i else 0)| ≤ δ / 16) :
    IsUnit (matchingK a b D).det ∧
      ∀ i j, |((matchingK a b D)⁻¹) i j| ≤ 2 / δ := by
  let E : Matrix (Fin 2) (Fin 2) ℝ := D - Matrix.diagonal d
  have ha (i : Fin 2) : |a i| ≤ 1 := by
    have hi := hab i
    have hs := sq_abs (a i)
    nlinarith [sq_nonneg (b i), abs_nonneg (a i)]
  have hE (i j : Fin 2) : |E i j| ≤ δ / 16 := by
    simpa only [E, Matrix.sub_apply, Matrix.diagonal_apply] using hentry i j
  have hdecomp : D = Matrix.diagonal d + E := by
    dsimp only [E]
    abel
  have hsmall (x : Fin 2 → ℝ) :
      ‖(Matrix.diagonal a * E) *ᵥ x‖ ≤ δ / 2 * ‖x‖ := by
    apply (pi_norm_le_iff_of_nonneg
      (mul_nonneg (by positivity : 0 ≤ δ / 2) (norm_nonneg x))).2
    intro i
    have hx (k : Fin 2) : |x k| ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm x k
    have hterm (k : Fin 2) :
        |E i k * x k| ≤ δ / 16 * ‖x‖ := by
      rw [abs_mul]
      exact mul_le_mul (hE i k) (hx k) (abs_nonneg (x k))
        (by positivity : 0 ≤ δ / 16)
    rw [Real.norm_eq_abs, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_diagonal, Matrix.mulVec_apply_eq_sum,
      Fin.sum_univ_two]
    calc
      |a i * (E i 0 * x 0 + E i 1 * x 1)|
          = |a i| * |E i 0 * x 0 + E i 1 * x 1| := abs_mul _ _
      _ ≤ 1 * |E i 0 * x 0 + E i 1 * x 1| :=
        mul_le_mul_of_nonneg_right (ha i) (abs_nonneg _)
      _ = |E i 0 * x 0 + E i 1 * x 1| := one_mul _
      _ ≤ |E i 0 * x 0| + |E i 1 * x 1| := abs_add_le _ _
      _ ≤ δ / 16 * ‖x‖ + δ / 16 * ‖x‖ :=
        add_le_add (hterm 0) (hterm 1)
      _ ≤ δ / 2 * ‖x‖ := by
        nlinarith [mul_nonneg hδ.le (norm_nonneg x)]
  obtain ⟨_, hdet, hbound⟩ :=
    matchingK_lower_bound a b d E D hdecomp δ hδ hdiag hsmall
  refine ⟨hdet, ?_⟩
  intro i j
  have hj := hbound (Pi.single j (1 : ℝ))
  rw [Pi.norm_single, norm_one, mul_one] at hj
  calc
    |((matchingK a b D)⁻¹) i j|
        = ‖((matchingK a b D)⁻¹ *ᵥ Pi.single j (1 : ℝ)) i‖ := by
          rw [Matrix.mulVec_single_one, Matrix.col_apply, Real.norm_eq_abs]
    _ ≤ ‖(matchingK a b D)⁻¹ *ᵥ Pi.single j (1 : ℝ)‖ :=
      norm_le_pi_norm _ i
    _ ≤ 2 / δ := hj

end ContinuousFlexibility.Radial

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements
open ContinuousFlexibility.Radial

/-- The statement layer's product, expressed with the matrix constructor
so that multiplication cannot be inferred as pointwise multiplication. -/
theorem radialMatrixProduct_eq_matrix_mul (P Q : RadialMatrix) :
    radialMatrixProduct P Q =
      fun i j => (Matrix.of P * Matrix.of Q) i j := by
  funext i j
  simp only [radialMatrixProduct, Matrix.mul_apply, Matrix.of_apply]

/-- The matrix clauses of MatchedPieces supply a two-sided inverse with
the precise entry bound required by ActualMatchedRepresentation. -/
theorem MatchedPieces.exists_matchingMatrixInverse
    (D : ReferenceData) (M : RadialMatchingData D)
    (h : MatchedPieces D M) :
    ∃ Kinv : RadialMatrix,
      (∀ i j, |Kinv i j| ≤ 4 / M.margin) ∧
      radialMatrixProduct Kinv
        (fun i j => radialMatrixProduct M.A M.Db i j - M.B i j) =
          radialMatrixIdentity ∧
      radialMatrixProduct
        (fun i j => radialMatrixProduct M.A M.Db i j - M.B i j)
        Kinv = radialMatrixIdentity := by
  rcases h with
    ⟨_, _, _, _, hmargin, hdiag, hentry, _, _, hoff, hnorm⟩
  let a : Fin 2 → ℝ := fun i => M.A i i
  let b : Fin 2 → ℝ := fun i => M.B i i
  have hA : Matrix.of M.A = Matrix.diagonal a := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.of_apply, Matrix.diagonal_apply_eq, a]
    · simp only [Matrix.of_apply, Matrix.diagonal_apply_ne _ hij]
      exact (hoff i j hij).1
  have hB : Matrix.of M.B = Matrix.diagonal b := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.of_apply, Matrix.diagonal_apply_eq, b]
    · simp only [Matrix.of_apply, Matrix.diagonal_apply_ne _ hij]
      exact (hoff i j hij).2
  let K : Matrix (Fin 2) (Fin 2) ℝ := matchingK a b (Matrix.of M.Db)
  let I : Matrix (Fin 2) (Fin 2) ℝ := K⁻¹
  have hK (i j : Fin 2) :
      radialMatrixProduct M.A M.Db i j - M.B i j = K i j := by
    have hprod := congrFun (congrFun (radialMatrixProduct_eq_matrix_mul M.A M.Db) i) j
    rw [hprod]
    have hb : M.B i j = (Matrix.diagonal b) i j := by
      simpa only [Matrix.of_apply] using congrFun (congrFun hB i) j
    rw [hA, hb]
    exact (Matrix.sub_apply _ _ i j).symm
  obtain ⟨hdet, hbound⟩ :=
    matchingK_inverse_entry_bound_two a b M.D0 (Matrix.of M.Db) M.margin hmargin
      hnorm (fun i => (hdiag i).2.2.2) (by
        intro i j
        simpa only [Matrix.of_apply] using hentry i j)
  refine ⟨(fun i j => I i j), ?_, ?_, ?_⟩
  · intro i j
    exact (hbound i j).trans
      (div_le_div_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 4) hmargin.le)
  · funext i j
    have hleft : I * K = (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
      Matrix.nonsing_inv_mul K hdet
    have hij := congrFun (congrFun hleft i) j
    change (∑ k, I i k * (radialMatrixProduct M.A M.Db k j - M.B k j)) =
      (if i = j then 1 else 0)
    simp_rw [hK]
    simpa only [Matrix.mul_apply, Matrix.one_apply] using hij
  · funext i j
    have hright : K * I = (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
      Matrix.mul_nonsing_inv K hdet
    have hij := congrFun (congrFun hright i) j
    change (∑ k, (radialMatrixProduct M.A M.Db i k - M.B i k) * I k j) =
      (if i = j then 1 else 0)
    simp_rw [hK]
    simpa only [Matrix.mul_apply, Matrix.one_apply] using hij

end ContinuousFlexibility.Blueprint
