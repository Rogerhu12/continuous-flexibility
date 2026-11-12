import ContinuousFlexibility.Analysis.TameElementaryCalculus
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# A fixed directional derivative of a genuine smooth tame tower

The fixed direction occupies the last slot. New derivatives are prepended,
so the tower recurrence is inherited literally and needs no interchange
of directional derivatives.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

section Towers

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

def n07aMultilinearFixLast {n : ℕ} (B : E [×(n + 1)]→L[ℝ] F) (w : E) :
    E [×n]→L[ℝ] F where
  toMultilinearMap := (LinearMap.applyₗ w).compMultilinearMap B.toMultilinearMap.curryRight
  cont := by
    have hc : Continuous (fun v : Fin n → E =>
        Fin.snoc (α := fun _ : Fin (n + 1) => E) v w) := by
      apply continuous_pi
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using
          (continuous_const : Continuous (fun _ : Fin n → E => w))
      · simpa only [Fin.snoc_castSucc] using
          (continuous_apply j : Continuous (fun v : Fin n → E => v j))
    apply (B.cont.comp hc).congr
    intro v
    exact ((LinearMap.compMultilinearMap_apply _ _ _).trans
      ((LinearMap.applyₗ_apply_apply _ _).trans
        (MultilinearMap.curryRight_apply B.toMultilinearMap v w))).symm

@[simp] theorem n07aMultilinearFixLast_apply {n : ℕ}
    (B : E [×(n + 1)]→L[ℝ] F) (w : E) (v : Fin n → E) :
    n07aMultilinearFixLast B w v = B (Fin.snoc v w) := by
  exact (LinearMap.compMultilinearMap_apply _ _ _).trans
    ((LinearMap.applyₗ_apply_apply _ _).trans
      (MultilinearMap.curryRight_apply B.toMultilinearMap v w))

def n07aFixedDirectionTower {U : Set E} {f : E → F}
    (J : SmoothDirections U f) (w : E) :
    SmoothDirections U (fun x => J.D 1 x (Fin.snoc Fin.elim0 w)) where
  open_domain := J.open_domain
  D := fun n x => n07aMultilinearFixLast (J.D (n + 1) x) w
  zero := fun x _ => n07aMultilinearFixLast_apply (J.D 1 x) w Fin.elim0
  continuous := by
    intro n
    have hc : Continuous (fun z : E × (Fin n → E) =>
        (z.1, Fin.snoc (α := fun _ : Fin (n + 1) => E) z.2 w)) := by
      apply continuous_fst.prodMk
      apply continuous_pi
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using
          (continuous_const : Continuous (fun _ : E × (Fin n → E) => w))
      · simpa only [Fin.snoc_castSucc, Function.comp_def] using
          (continuous_apply j).comp continuous_snd
    simpa only [n07aMultilinearFixLast_apply, Function.comp_def] using
      (J.continuous (n + 1)).comp hc.continuousOn
        (fun z hz => ⟨hz.1, mem_univ _⟩)
  derivative := by
    intro n x hx v h
    simpa only [n07aMultilinearFixLast_apply, Fin.cons_snoc_eq_snoc_cons] using
      J.derivative (n + 1) x hx (Fin.snoc v w) h

@[simp] theorem n07aFixedDirectionTower_D_apply {U : Set E} {f : E → F}
    (J : SmoothDirections U f) (w : E) (n : ℕ) (x : E) (v : Fin n → E) :
    (n07aFixedDirectionTower J w).D n x v = J.D (n + 1) x (Fin.snoc v w) :=
  n07aMultilinearFixLast_apply (J.D (n + 1) x) w v

end Towers

private theorem n07a_prod_erase_eq_ite {n : ℕ} (f : Fin n → ℝ) (i : Fin n) :
    (∏ j ∈ Finset.univ.erase i, f j) = ∏ j, if j = i then 1 else f j := by
  classical
  symm
  rw [← Finset.mul_prod_erase Finset.univ (fun j => if j = i then (1 : ℝ) else f j)
    (Finset.mem_univ i)]
  simp only [ite_true, one_mul]
  apply Finset.prod_congr rfl
  intro j hj
  rw [ite_eq_right (Finset.mem_erase.mp hj).1]

private theorem n07a_prod_erase_snoc_last {E : Type*} {n : ℕ}
    (L : E → ℝ) (v : Fin n → E) (w : E) :
    (∏ j ∈ Finset.univ.erase (Fin.last n),
      L (Fin.snoc (α := fun _ : Fin (n + 1) => E) v w j)) = ∏ j, L (v j) := by
  rw [n07a_prod_erase_eq_ite, Fin.prod_univ_castSucc]
  simp

private theorem n07a_prod_erase_snoc_castSucc {E : Type*} {n : ℕ}
    (L : E → ℝ) (v : Fin n → E) (w : E) (i : Fin n) :
    (∏ j ∈ Finset.univ.erase i.castSucc,
      L (Fin.snoc (α := fun _ : Fin (n + 1) => E) v w j)) =
      (∏ j ∈ Finset.univ.erase i, L (v j)) * L w := by
  rw [n07a_prod_erase_eq_ite, Fin.prod_univ_castSucc, n07a_prod_erase_eq_ite]
  have hlast : Fin.last n ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
  simp [hlast]

theorem n07a_tameJetSize_snoc {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (k s loss base : ℕ) (x w : E) (v : Fin k → E) :
    tameJetSize p (k + 1) s loss base x (Fin.snoc v w) =
      p base w * tameJetSize p k s loss base x v +
        p (s + loss) w * ∏ i, p base (v i) := by
  classical
  unfold tameJetSize
  rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last,
    n07a_prod_erase_snoc_last, n07a_prod_erase_snoc_castSucc]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  ring

theorem n07a_tameJetSize_snoc_le {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (k s loss base : ℕ) (x w : E) (v : Fin k → E) :
    tameJetSize p (k + 1) s loss base x (Fin.snoc v w) ≤
      (p base w + p (s + loss) w) * tameJetSize p k s loss base x v := by
  have hprod : 0 ≤ ∏ i, p base (v i) := Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)
  have hsum : 0 ≤ ∑ i, p (s + loss) (v i) *
      ∏ j ∈ Finset.univ.erase i, p base (v j) :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (apply_nonneg _ _)
      (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)))
  have hp : (∏ i, p base (v i)) ≤ tameJetSize p k s loss base x v := by
    unfold tameJetSize
    nlinarith only [mul_nonneg (apply_nonneg (p (s + loss)) x) hprod, hsum]
  rw [n07a_tameJetSize_snoc, add_mul]
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hp (apply_nonneg (p (s + loss)) w))

theorem n07a_smoothTame_fixedDirection
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E} {f : E → F}
    (hf : SmoothTameOn p q U f) (w : E) :
    SmoothTameOn p q U (fun x => hf.choose.D 1 x (Fin.snoc Fin.elim0 w)) := by
  let J := hf.choose
  refine ⟨n07aFixedDirectionTower J w, ?_⟩
  intro k x₀ hx₀
  obtain ⟨loss, base, ε, hε, hbound⟩ := hf.choose_spec (k + 1) x₀ hx₀
  refine ⟨loss, base, ε, hε, ?_⟩
  intro s hs
  obtain ⟨C, hC, hCs⟩ := hbound s hs
  refine ⟨C * (p base w + p (s + loss) w),
    mul_nonneg hC (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)), ?_⟩
  intro x hx hnear v
  simp only [n07aFixedDirectionTower_D_apply]
  calc
    _ ≤ C * tameJetSize p (k + 1) s loss base x (Fin.snoc v w) := hCs x hx hnear _
    _ ≤ C * ((p base w + p (s + loss) w) * tameJetSize p k s loss base x v) :=
      mul_le_mul_of_nonneg_left (n07a_tameJetSize_snoc_le p k s loss base x w v) hC
    _ = _ := (mul_assoc _ _ _).symm

end ContinuousFlexibility.Analysis
