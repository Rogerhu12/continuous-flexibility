import ContinuousFlexibility.Analysis.N07aSchurOneHigh

/-!
# A Schur lift represents the same original operator

Rectangular angular blocks may take values in a stronger Hilbert space.
After Riesz realization, their scalar pairings determine every band.
A bounded inclusion into the original space then identifies the lifted
operator with the original one using the genuine strong band expansion.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped RealInnerProductSpace

variable {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

def n07aSchurLiftBlockForm (Q : ℕ → F →L[ℝ] F) (A : ℕ → ℕ → E →L[ℝ] F)
    (i : ℕ × ℕ) : E →ₗ[ℝ] F →ₗ[ℝ] ℝ :=
  (innerₗ F).compl₁₂ (A i.1 i.2).toLinearMap (Q i.1).toLinearMap

theorem n07aSchurLiftBlockForm_apply (Q : ℕ → F →L[ℝ] F)
    (A : ℕ → ℕ → E →L[ℝ] F) (i : ℕ × ℕ) (x : E) (y : F) :
    n07aSchurLiftBlockForm Q A i x y = ⟪A i.1 i.2 x, Q i.1 y⟫ := by
  simp only [n07aSchurLiftBlockForm, LinearMap.compl₁₂_apply,
    ContinuousLinearMap.coe_coe, innerₗ_apply_apply]

theorem n07aSchurLift_block
    (P : ℕ → E →L[ℝ] E) (Q : ℕ → F →L[ℝ] F)
    (A : ℕ → ℕ → E →L[ℝ] F) (K : E →L[ℝ] F)
    (hcomp : ∀ i j y, Q i (Q j y) = if i = j then Q j y else 0)
    (hsymm : ∀ i x y, ⟪Q i x, y⟫ = ⟪x, Q i y⟫)
    (hleft : ∀ l j x, Q l (A l j x) = A l j x)
    (hright : ∀ l j k x, A l j (P k x) = if j = k then A l j x else 0)
    (hK : ∀ x y, ⟪K x, y⟫ = ∑' i : ℕ × ℕ, ⟪A i.1 i.2 x, Q i.1 y⟫)
    (l j : ℕ) (x : E) : Q l (K (P j x)) = A l j x := by
  apply ext_inner_right ℝ
  intro y
  rw [hsymm, hK]
  have hzero (i : ℕ × ℕ) (hi : i ≠ (l, j)) :
      ⟪A i.1 i.2 (P j x), Q i.1 (Q l y)⟫ = 0 := by
    by_cases hl : i.1 = l
    · have hj : i.2 ≠ j := fun hj => hi (Prod.ext hl hj)
      rw [hright, if_neg hj, inner_zero_left]
    · rw [hcomp, if_neg hl, inner_zero_right]
  rw [tsum_eq_single (l, j) hzero]
  simp only [hright, hcomp, ite_true]
  rw [← hsymm, hleft]

theorem n07aSchurLift_eq_original
    (P : ℕ → E →L[ℝ] E) (Q : ℕ → F →L[ℝ] F) (S : ℕ → H →L[ℝ] H)
    (A : ℕ → ℕ → E →L[ℝ] F) (K : E →L[ℝ] F)
    (J : F →L[ℝ] H) (R : E →L[ℝ] H)
    (hsum : ∀ x, HasSum (fun j => P j x) x)
    (htotal : ∀ x : H, (∀ l, S l x = 0) → x = 0)
    (hinter : ∀ l y, S l (J y) = J (Q l y))
    (hblock : ∀ l j x, Q l (K (P j x)) = A l j x)
    (hactual : ∀ l j x, J (A l j x) = S l (R (P j x))) :
    ∀ x, J (K x) = R x := by
  have hband (j : ℕ) (x : E) : J (K (P j x)) = R (P j x) := by
    apply sub_eq_zero.mp
    apply htotal
    intro l
    rw [map_sub, hinter, hblock, hactual, sub_self]
  intro x
  have h₁ := (hsum x).mapL (J.comp K)
  have h₂ := (hsum x).mapL R
  simp only [ContinuousLinearMap.comp_apply, hband] at h₁
  exact h₁.unique h₂

end ContinuousFlexibility.Analysis
