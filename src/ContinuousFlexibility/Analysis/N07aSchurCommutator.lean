module

public import ContinuousFlexibility.Analysis.N07aSchurBilinear
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# The bounded frequency-difference operator of actual blocks

Each block is the original operator between two orthogonal projections,
multiplied by their frequency difference.  Schur summability constructs
one bounded operator, and testing against a single band identifies every
one of its blocks exactly.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def n07aCommutatorBlock (P : ℕ → H →L[ℝ] H) (R : H →L[ℝ] H) (l j : ℕ) : H →L[ℝ] H :=
  ((l : ℝ) - j) • ((P l).comp (R.comp (P j)))

theorem n07aCommutatorBlock_apply (P : ℕ → H →L[ℝ] H) (R : H →L[ℝ] H)
    (l j : ℕ) (x : H) :
    n07aCommutatorBlock P R l j x = ((l : ℝ) - j) • P l (R (P j x)) := rfl

def n07aCommutatorBlockForm (P : ℕ → H →L[ℝ] H) (R : H →L[ℝ] H)
    (i : ℕ × ℕ) : H →ₗ[ℝ] H →ₗ[ℝ] ℝ :=
  (innerₗ H).compl₁₂ (n07aCommutatorBlock P R i.1 i.2).toLinearMap (P i.1).toLinearMap

theorem n07aCommutatorBlockForm_apply (P : ℕ → H →L[ℝ] H) (R : H →L[ℝ] H)
    (i : ℕ × ℕ) (x y : H) :
    n07aCommutatorBlockForm P R i x y = ⟪n07aCommutatorBlock P R i.1 i.2 x, P i.1 y⟫ := rfl

theorem exists_n07aSchurCommutator
    (P : ℕ → H →L[ℝ] H) (R : H →L[ℝ] H) (a : ℕ → ℕ → ℝ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : ∀ l j, 0 ≤ a l j)
    (hrow : ∀ l, Summable (fun j => a l j) ∧ ∑' j, a l j ≤ A)
    (hcol : ∀ j, Summable (fun l => a l j) ∧ ∑' l, a l j ≤ B)
    (hP : ∀ x, Summable (fun j => ‖P j x‖ ^ 2) ∧ ∑' j, ‖P j x‖ ^ 2 ≤ ‖x‖ ^ 2)
    (hb : ∀ l j x, ‖n07aCommutatorBlock P R l j x‖ ≤ a l j * ‖P j x‖) :
    ∃ K : H →L[ℝ] H, ‖K‖ ≤ Real.sqrt (A * B) ∧
      ∀ x y, ⟪K x, y⟫ =
        ∑' i : ℕ × ℕ, ⟪n07aCommutatorBlock P R i.1 i.2 x, P i.1 y⟫ := by
  apply exists_n07aSchurRiesz (n07aCommutatorBlockForm P R)
    (fun j x => ‖P j x‖) (fun l y => ‖P l y‖) a
    hA hB ha hrow hcol (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _) hP hP
  intro i x y
  calc
    _ ≤ ‖n07aCommutatorBlock P R i.1 i.2 x‖ * ‖P i.1 y‖ := norm_inner_le_norm _ _
    _ ≤ (a i.1 i.2 * ‖P i.2 x‖) * ‖P i.1 y‖ :=
      mul_le_mul_of_nonneg_right (hb i.1 i.2 x) (norm_nonneg _)
    _ = _ := by ring

theorem n07aSchurCommutator_block
    (P : ℕ → H →L[ℝ] H) (R K : H →L[ℝ] H)
    (hcomp : ∀ i j x, P i (P j x) = if i = j then P j x else 0)
    (hsymm : ∀ i x y, ⟪P i x, y⟫ = ⟪x, P i y⟫)
    (hK : ∀ x y, ⟪K x, y⟫ =
      ∑' i : ℕ × ℕ, ⟪n07aCommutatorBlock P R i.1 i.2 x, P i.1 y⟫)
    (l j : ℕ) (x : H) : P l (K (P j x)) = n07aCommutatorBlock P R l j x := by
  apply ext_inner_right ℝ
  intro y
  rw [hsymm, hK]
  have hzero (i : ℕ × ℕ) (hi : i ≠ (l, j)) :
      ⟪n07aCommutatorBlock P R i.1 i.2 (P j x), P i.1 (P l y)⟫ = 0 := by
    by_cases hl : i.1 = l
    · have hj : i.2 ≠ j := fun hj => hi (Prod.ext hl hj)
      simp only [n07aCommutatorBlock_apply, hcomp, if_neg hj, map_zero, smul_zero, inner_zero_left]
    · rw [hcomp, if_neg hl, inner_zero_right]
  rw [tsum_eq_single (l, j) hzero]
  simp only [n07aCommutatorBlock_apply, hcomp, ite_true]
  rw [← hsymm]
  simp only [map_smul, hcomp, ite_true]

/-- Strong convergence is supplied by bounded maps of the original
orthogonal expansion.  The scalar Schur series is not used as a vector
series in this step. -/
theorem n07aCommutator_coordinate_identity
    (P : ℕ → H →L[ℝ] H) (R K : H →L[ℝ] H)
    (hsum : ∀ x, HasSum (fun j => P j x) x)
    (hblock : ∀ l j x, P l (K (P j x)) = n07aCommutatorBlock P R l j x)
    (x dx : H) (hd : ∀ j, P j dx = (j : ℝ) • P j x) (l : ℕ) :
    P l (R dx + K x) = (l : ℝ) • P l (R x) := by
  have ha := (hsum dx).mapL ((P l).comp R)
  simp only [ContinuousLinearMap.comp_apply, hd, map_smul] at ha
  have hb := (hsum x).mapL ((P l).comp K)
  simp only [ContinuousLinearMap.comp_apply, hblock, n07aCommutatorBlock_apply] at hb
  have hab := ha.add hb
  simp only [← add_smul, add_sub_cancel] at hab
  have hc := (hsum x).mapL ((l : ℝ) • ((P l).comp R))
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply] at hc
  simpa only [map_add] using hab.unique hc

end ContinuousFlexibility.Analysis
