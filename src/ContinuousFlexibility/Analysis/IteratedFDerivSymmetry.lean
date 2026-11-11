import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.GroupTheory.Perm.Sign

/-!
# Symmetry of the iterated derivative of a smooth real function

The power-series symmetry theorem in mathlib requires analyticity. Here
the scalar field is real, so symmetry of second derivatives and generation
of finite permutations by adjacent transpositions give the corresponding
result for a `C^∞` function.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Equiv Function
open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem iteratedFDeriv_cons_cons_eq (f : E → F) (n : ℕ)
    (x a b : E) (v : Fin n → E) :
    iteratedFDeriv ℝ (n + 2) f x (Fin.cons a (Fin.cons b v)) =
      fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ n f)) x a b v := by
  rw [iteratedFDeriv_succ_apply_left]
  simp only [Fin.cons_zero, Fin.tail_cons]
  rw [iteratedFDeriv_succ_eq_comp_left]
  rw [(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F).symm.comp_fderiv
    (f := fderiv ℝ (iteratedFDeriv ℝ n f)) (x := x)]
  rfl

private theorem iteratedFDeriv_cons_cons_swap {f : E → F}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (x a b : E) (v : Fin n → E) :
    iteratedFDeriv ℝ (n + 2) f x (Fin.cons a (Fin.cons b v)) =
      iteratedFDeriv ℝ (n + 2) f x (Fin.cons b (Fin.cons a v)) := by
  rw [iteratedFDeriv_cons_cons_eq, iteratedFDeriv_cons_cons_eq]
  have hn : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) :=
    hf.iteratedFDeriv_right (by simp)
  exact congrArg (fun A : E [×n]→L[ℝ] F => A v)
    (hn.contDiffAt.isSymmSndFDerivAt (by simp) a b)

private theorem iteratedFDeriv_comp_adjacent {f : E → F}
    (hf : ContDiff ℝ ∞ f) : ∀ (n : ℕ) (i : Fin n) (x : E) (v : Fin (n + 1) → E),
    iteratedFDeriv ℝ (n + 1) f x (v ∘ swap i.castSucc i.succ) =
      iteratedFDeriv ℝ (n + 1) f x v := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro x v
      change iteratedFDeriv ℝ (n + 2) f x (v ∘ swap (0 : Fin (n + 2)) 1) = _
      have hswap : v ∘ swap (0 : Fin (n + 2)) 1 =
          Fin.cons (v 1) (Fin.cons (v 0) (Fin.tail (Fin.tail v))) := by
        funext k
        refine Fin.cases ?_ (fun k => ?_) k
        · simp
        · refine Fin.cases ?_ (fun k => ?_) k
          · simp
          · simp [Function.comp_def, swap_apply_def, Fin.ext_iff, Fin.tail]
      have hcons : Fin.cons (v 0) (Fin.cons (v 1) (Fin.tail (Fin.tail v))) = v := by
        change Fin.cons (v 0) (Fin.cons (Fin.tail v 0) (Fin.tail (Fin.tail v))) = v
        rw [Fin.cons_self_tail, Fin.cons_self_tail]
      rw [hswap]
      exact (iteratedFDeriv_cons_cons_swap hf n x (v 1) (v 0)
        (Fin.tail (Fin.tail v))).trans (congrArg (iteratedFDeriv ℝ (n + 2) f x) hcons)
    · intro x v
      have hswap : v ∘ swap j.succ.castSucc j.succ.succ =
          Fin.cons (v 0) (Fin.tail v ∘ swap j.castSucc j.succ) := by
        funext k
        refine Fin.cases ?_ (fun k => ?_) k
        · simp [Function.comp_def, swap_apply_def, Fin.ext_iff]
        · change v (swap j.castSucc.succ j.succ.succ k.succ) =
            v ((swap j.castSucc j.succ k).succ)
          exact congrArg v
            ((Fin.succ_injective (n + 1)).map_swap j.castSucc j.succ k).symm
      have hn : DifferentiableAt ℝ (iteratedFDeriv ℝ (n + 1) f) x :=
        (hf.iteratedFDeriv_right (m := ∞) (by simp)).differentiable (by simp) x
      have hfun : (fun y => iteratedFDeriv ℝ (n + 1) f y
          (Fin.tail v ∘ swap j.castSucc j.succ)) =
          (fun y => iteratedFDeriv ℝ (n + 1) f y (Fin.tail v)) :=
        funext fun y => ih j y (Fin.tail v)
      rw [hswap, hn.iteratedFDeriv_succ_apply_left', hn.iteratedFDeriv_succ_apply_left']
      simp only [Fin.tail_cons, Fin.cons_zero]
      rw [hfun]

/-- Every iterated derivative of a globally smooth real function is invariant
under permutation of its arguments. No analyticity hypothesis is needed. -/
theorem iteratedFDeriv_comp_perm_of_contDiff {f : E → F}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : E) (v : Fin n → E) (σ : Perm (Fin n)) :
    iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v := by
  cases n with
  | zero => simp only [iteratedFDeriv_zero_apply]
  | succ n =>
    have hmem : σ ∈ Submonoid.closure
        (Set.range fun i : Fin n => swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    have hperm : ∀ w : Fin (n + 1) → E,
        iteratedFDeriv ℝ (n + 1) f x (w ∘ σ) = iteratedFDeriv ℝ (n + 1) f x w := by
      induction hmem using Submonoid.closure_induction with
      | mem τ hτ =>
        obtain ⟨i, rfl⟩ := hτ
        exact iteratedFDeriv_comp_adjacent hf n i x
      | one => intro w; rfl
      | mul τ υ _ _ hτ hυ =>
        intro w
        exact (hυ (w ∘ τ)).trans (hτ w)
    exact hperm v

/-- The bundled version of permutation symmetry for smooth real jets. -/
theorem domDomCongr_iteratedFDeriv_of_contDiff {f : E → F}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : E) (σ : Perm (Fin n)) :
    (iteratedFDeriv ℝ n f x).domDomCongr σ = iteratedFDeriv ℝ n f x := by
  ext v
  exact iteratedFDeriv_comp_perm_of_contDiff hf n x v σ

end ContinuousFlexibility.Analysis
