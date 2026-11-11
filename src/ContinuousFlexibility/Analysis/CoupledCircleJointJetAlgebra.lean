import ContinuousFlexibility.Analysis.ProjectiveMultilinearCalculus
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Joint jets of a kernel linear in its outer function

The same finite formula applies to ordinary circle composition and its
averaged derivative kernel. At each order the outer function is either
the base value or exactly one of the joint directions.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators

variable {X Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]

private theorem coupled_cons_update {n : ℕ} [DecidableEq (Fin n)] (x : X) (v : Fin n → X)
    (i : Fin n) (a : X) :
    (Fin.cons x (Function.update v i a) : Fin (n + 1) → X) =
      Function.update (Fin.cons x v : Fin (n + 1) → X) i.succ a := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Fin.cons_zero, Function.update_of_ne (Fin.succ_ne_zero i).symm]
  · simp only [Fin.cons_succ, Function.update_apply, Fin.succ_inj]

def coupledKernelFixFirst {n : ℕ} (A : X [×(n + 1)]→L[ℝ] Y) (x : X) :
    X [×n]→L[ℝ] Y where
  toMultilinearMap :=
    { toFun := fun v => A (Fin.cons x v)
      map_update_add' := by
        intro inst v i a b
        letI : DecidableEq (Fin n) := inst
        simpa only [← coupled_cons_update] using A.map_update_add (Fin.cons x v) i.succ a b
      map_update_smul' := by
        intro inst v i c a
        letI : DecidableEq (Fin n) := inst
        simpa only [← coupled_cons_update] using A.map_update_smul (Fin.cons x v) i.succ c a }
  cont := A.cont.comp (continuous_pi (fun i =>
    Fin.cases continuous_const (fun j => continuous_apply j) i))

theorem coupledKernelFixFirst_apply {n : ℕ} (A : X [×(n + 1)]→L[ℝ] Y)
    (x : X) (v : Fin n → X) : coupledKernelFixFirst A x v = A (Fin.cons x v) := rfl

def coupledKernelSlotPermutation {n : ℕ} (i : Fin (n + 1)) :
    Equiv.Perm (Fin (n + 1)) := (finSuccEquiv n).trans (finSuccEquiv' i).symm

theorem coupledKernelSlotPermutation_zero {n : ℕ} (i : Fin (n + 1)) :
    coupledKernelSlotPermutation i 0 = i := by
  simp only [coupledKernelSlotPermutation, Equiv.trans_apply, finSuccEquiv_zero,
    finSuccEquiv'_symm_none]

theorem coupledKernelSlotPermutation_succ {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    coupledKernelSlotPermutation i j.succ = i.succAbove j := by
  simp only [coupledKernelSlotPermutation, Equiv.trans_apply, finSuccEquiv_succ,
    finSuccEquiv'_symm_some]

def coupledKernelBaseJet {n : ℕ} (A : X [×(n + 1)]→L[ℝ] Y) (v : X) :
    (X × X) [×n]→L[ℝ] Y :=
  (coupledKernelFixFirst A v).compContinuousLinearMap
    (fun _ => ContinuousLinearMap.fst ℝ X X)

theorem coupledKernelBaseJet_apply {n : ℕ} (A : X [×(n + 1)]→L[ℝ] Y)
    (v : X) (w : Fin n → X × X) :
    coupledKernelBaseJet A v w = A (Fin.cons v (fun i => (w i).1)) := rfl

def coupledKernelDirectionJet {n : ℕ} (A : X [×(n + 1)]→L[ℝ] Y)
    (i : Fin (n + 1)) : (X × X) [×(n + 1)]→L[ℝ] Y :=
  (A.compContinuousLinearMap
    (Fin.cons (ContinuousLinearMap.snd ℝ X X)
      (fun _ : Fin n => ContinuousLinearMap.fst ℝ X X))).domDomCongr
        (coupledKernelSlotPermutation i)

theorem coupledKernelDirectionJet_apply {n : ℕ} (A : X [×(n + 1)]→L[ℝ] Y)
    (i : Fin (n + 1)) (w : Fin (n + 1) → X × X) :
    coupledKernelDirectionJet A i w =
      A (Fin.cons (w i).2 (fun j => (w (i.succAbove j)).1)) := by
  change A (fun j : Fin (n + 1) => ((Fin.cons (ContinuousLinearMap.snd ℝ X X)
    (fun _ : Fin n => ContinuousLinearMap.fst ℝ X X) : Fin (n + 1) → (X × X →L[ℝ] X)) j)
      (w (coupledKernelSlotPermutation i j))) = _
  congr 1
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Fin.cons_zero, coupledKernelSlotPermutation_zero,
      ContinuousLinearMap.coe_snd']
  · simp only [Fin.cons_succ, coupledKernelSlotPermutation_succ,
      ContinuousLinearMap.coe_fst']

variable [IsTopologicalAddGroup Y]

def coupledKernelJointJet (K : ∀ n : ℕ, X → X [×(n + 1)]→L[ℝ] Y) :
    ∀ n : ℕ, (X × X) → (X × X) [×n]→L[ℝ] Y
  | 0, z => coupledKernelBaseJet (K 0 z.1) z.2
  | n + 1, z => coupledKernelBaseJet (K (n + 1) z.1) z.2 +
      ∑ i : Fin (n + 1), coupledKernelDirectionJet (K n z.1) i

theorem coupledKernelJointJet_zero_apply
    (K : ∀ n : ℕ, X → X [×(n + 1)]→L[ℝ] Y)
    (z : X × X) (w : Fin 0 → X × X) :
    coupledKernelJointJet K 0 z w = K 0 z.1 (Fin.cons z.2 Fin.elim0) := by
  change K 0 z.1 (Fin.cons z.2 (fun i => (w i).1)) = _
  congr 2
  exact Subsingleton.elim _ _

theorem coupledKernelJointJet_succ_apply
    (K : ∀ n : ℕ, X → X [×(n + 1)]→L[ℝ] Y)
    (n : ℕ) (z : X × X) (w : Fin (n + 1) → X × X) :
    coupledKernelJointJet K (n + 1) z w =
      K (n + 1) z.1 (Fin.cons z.2 (fun i => (w i).1)) +
        ∑ i : Fin (n + 1), K n z.1
          (Fin.cons (w i).2 (fun j => (w (i.succAbove j)).1)) := by
  simp only [coupledKernelJointJet, add_apply, sum_apply, coupledKernelBaseJet_apply,
    coupledKernelDirectionJet_apply]

end ContinuousFlexibility.Analysis
