import ContinuousFlexibility.Analysis.SmoothDirectionsAngularJets
import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# Genuine jet formulas for a family that is linear in its fiber

At order n, a linear fiber contributes either the base fiber to the
n-th coefficient jet, or one fiber direction to an (n-1)-st coefficient
jet. The recursion below constructs algebraic multilinear maps before
any continuity or norm estimate is imposed. Scalar testing proves the
actual derivative recurrence, including affine variation of the fiber.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology BigOperators

variable {X Y G : Type*} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] [AddCommGroup G] [Module ℝ G]

abbrev LinearFiberJetData (X Y G : Type*)
    [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    [AddCommGroup G] [Module ℝ G] :=
  ∀ n : ℕ, MultilinearMap ℝ (fun _ : Fin n => X) (Y →ₗ[ℝ] G)

def linearFiberHead (A : LinearFiberJetData X Y G) :
    (X × Y) →ₗ[ℝ] LinearFiberJetData X Y G where
  toFun w n := (A (n + 1)).curryLeft w.1
  map_add' w v := by
    funext n
    exact (A (n + 1)).curryLeft.map_add w.1 v.1
  map_smul' c w := by
    funext n
    exact (A (n + 1)).curryLeft.map_smul c w.1

theorem linearFiberHead_apply (A : LinearFiberJetData X Y G)
    (w : X × Y) (n : ℕ) (v : Fin n → X) :
    linearFiberHead A w n v = A (n + 1) (Fin.cons w.1 v) :=
  MultilinearMap.curryLeft_apply _ _ _

theorem linearFiberHead_add (A B : LinearFiberJetData X Y G) (w : X × Y) :
    linearFiberHead (A + B) w = linearFiberHead A w + linearFiberHead B w := by
  funext n
  ext v
  simp only [linearFiberHead_apply, Pi.add_apply, MultilinearMap.add_apply]

theorem linearFiberHead_smul (c : ℝ) (A : LinearFiberJetData X Y G) (w : X × Y) :
    linearFiberHead (c • A) w = c • linearFiberHead A w := by
  funext n
  ext v
  simp only [linearFiberHead_apply, Pi.smul_apply, MultilinearMap.smul_apply]

private def linearFiberEvaluation (y : Y) : (Y →ₗ[ℝ] G) →ₗ[ℝ] G where
  toFun L := L y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def linearFiberMain (n : ℕ) (A : LinearFiberJetData X Y G) :
    Y →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin n => X × Y) G where
  toFun y := (linearFiberEvaluation y).compMultilinearMap
    ((A n).compLinearMap (fun _ => LinearMap.fst ℝ X Y))
  map_add' y z := by
    ext v
    exact (A n (fun i => (v i).1)).map_add y z
  map_smul' c y := by
    ext v
    exact (A n (fun i => (v i).1)).map_smul c y

theorem linearFiberMain_apply (n : ℕ) (A : LinearFiberJetData X Y G)
    (y : Y) (v : Fin n → X × Y) :
    linearFiberMain n A y v = A n (fun i => (v i).1) y := rfl

theorem linearFiberMain_add (n : ℕ) (A B : LinearFiberJetData X Y G) :
    linearFiberMain n (A + B) = linearFiberMain n A + linearFiberMain n B := by
  ext y v
  simp only [linearFiberMain_apply, Pi.add_apply, MultilinearMap.add_apply,
    LinearMap.add_apply]

theorem linearFiberMain_smul (n : ℕ) (c : ℝ) (A : LinearFiberJetData X Y G) :
    linearFiberMain n (c • A) = c • linearFiberMain n A := by
  ext y v
  simp only [linearFiberMain_apply, Pi.smul_apply, MultilinearMap.smul_apply,
    LinearMap.smul_apply]

/-- The part of the jet using one of the supplied fiber directions. -/
def linearFiberRemainder : (n : ℕ) → LinearFiberJetData X Y G →ₗ[ℝ]
    MultilinearMap ℝ (fun _ : Fin n => X × Y) G
  | 0 => 0
  | n + 1 =>
      { toFun A :=
          ((linearFiberRemainder n).comp (linearFiberHead A) +
            (linearFiberMain n A).comp (LinearMap.snd ℝ X Y)).uncurryLeft
        map_add' A B := by
          ext v
          simp only [LinearMap.uncurryLeft_apply, LinearMap.add_apply,
            MultilinearMap.add_apply, LinearMap.comp_apply, linearFiberHead_add,
            map_add, linearFiberMain_add]
          abel
        map_smul' c A := by
          ext v
          simp only [LinearMap.uncurryLeft_apply, LinearMap.add_apply,
            MultilinearMap.add_apply, LinearMap.comp_apply, linearFiberHead_smul,
            map_smul, linearFiberMain_smul, LinearMap.smul_apply,
            MultilinearMap.smul_apply, smul_add, RingHom.id_apply] }

theorem linearFiberRemainder_zero_apply (A : LinearFiberJetData X Y G)
    (v : Fin 0 → X × Y) : linearFiberRemainder 0 A v = 0 := rfl

theorem linearFiberRemainder_succ_apply (n : ℕ) (A : LinearFiberJetData X Y G)
    (v : Fin (n + 1) → X × Y) :
    linearFiberRemainder (n + 1) A v =
      linearFiberRemainder n (linearFiberHead A (v 0)) (Fin.tail v) +
        A n (fun i => (v i.succ).1) (v 0).2 := rfl

def linearFiberJet (n : ℕ) (A : LinearFiberJetData X Y G) (y : Y) :
    MultilinearMap ℝ (fun _ : Fin n => X × Y) G :=
  linearFiberMain n A y + linearFiberRemainder n A

theorem linearFiberJet_zero_apply (A : LinearFiberJetData X Y G)
    (y : Y) (v : Fin 0 → X × Y) :
    linearFiberJet 0 A y v = A 0 Fin.elim0 y := by
  simp only [linearFiberJet, MultilinearMap.add_apply, linearFiberMain_apply,
    linearFiberRemainder_zero_apply, add_zero]
  exact congrArg (fun w : Fin 0 → X => A 0 w y) (Subsingleton.elim _ _)

theorem linearFiberJet_succ_apply (n : ℕ) (A : LinearFiberJetData X Y G)
    (y : Y) (w : X × Y) (v : Fin n → X × Y) :
    linearFiberJet (n + 1) A y (Fin.cons w v) =
      linearFiberJet n (linearFiberHead A w) y v + A n (fun i => (v i).1) w.2 := by
  have hcons : (fun i : Fin (n + 1) => ((Fin.cons w v : Fin (n + 1) → X × Y) i).1) =
      Fin.cons w.1 (fun i => (v i).1) := by
    funext i
    cases i using Fin.cases <;> rfl
  simp only [linearFiberJet, MultilinearMap.add_apply, linearFiberMain_apply,
    linearFiberRemainder_succ_apply, Fin.cons_zero, Fin.cons_succ, Fin.tail_cons,
    hcons, linearFiberHead_apply]
  exact (add_assoc _ _ _).symm

theorem linearFiberRemainder_mem (V : Submodule ℝ G) (n : ℕ)
    (A : LinearFiberJetData X Y G)
    (hA : ∀ k (v : Fin k → X) (y : Y), A k v y ∈ V)
    (v : Fin n → X × Y) : linearFiberRemainder n A v ∈ V := by
  induction n generalizing A with
  | zero => exact V.zero_mem
  | succ n ih =>
      rw [linearFiberRemainder_succ_apply]
      exact V.add_mem
        (ih (linearFiberHead A (v 0))
          (fun k vs y => hA (k + 1) (Fin.cons (v 0).1 vs) y) (Fin.tail v))
        (hA n (fun i => (v i.succ).1) (v 0).2)

theorem linearFiberJet_mem (V : Submodule ℝ G) (n : ℕ)
    (A : LinearFiberJetData X Y G)
    (hA : ∀ k (v : Fin k → X) (y : Y), A k v y ∈ V)
    (y : Y) (v : Fin n → X × Y) : linearFiberJet n A y v ∈ V :=
  V.add_mem (hA n (fun i => (v i).1) y) (linearFiberRemainder_mem V n A hA v)

/-- The finite expansion preserves the order of every coefficient
direction. Exactly one fiber direction occurs in each summand. -/
theorem linearFiberRemainder_eq_sum (n : ℕ) (A : LinearFiberJetData X Y G)
    (v : Fin (n + 1) → X × Y) :
    linearFiberRemainder (n + 1) A v =
      ∑ i : Fin (n + 1), A n (fun j => (v (i.succAbove j)).1) (v i).2 := by
  induction n generalizing A with
  | zero =>
      rw [linearFiberRemainder_succ_apply, linearFiberRemainder_zero_apply, zero_add]
      change A 0 (fun i : Fin 0 => (v i.succ).1) (v 0).2 =
        ∑ i : Fin 1, A 0 (fun j : Fin 0 => (v (i.succAbove j)).1) (v i).2
      rw [Fin.sum_univ_one]
      exact congrArg (fun vs : Fin 0 → X => A 0 vs (v 0).2) (Subsingleton.elim _ _)
  | succ n ih =>
      calc
        linearFiberRemainder (n + 2) A v =
            (∑ i : Fin (n + 1), A (n + 1)
              (Fin.cons (v 0).1 (fun j => (v (i.succAbove j).succ).1)) (v i.succ).2) +
              A (n + 1) (fun j => (v j.succ).1) (v 0).2 := by
          rw [linearFiberRemainder_succ_apply, ih]
          simp only [linearFiberHead_apply, Fin.tail]
        _ = A (n + 1) (fun j => (v j.succ).1) (v 0).2 +
            ∑ i : Fin (n + 1), A (n + 1)
              (Fin.cons (v 0).1 (fun j => (v (i.succAbove j).succ).1)) (v i.succ).2 :=
          add_comm _ _
        _ = ∑ i : Fin (n + 2), A (n + 1)
            (fun j => (v (i.succAbove j)).1) (v i).2 := by
          rw [Fin.sum_univ_succ (fun i : Fin (n + 2) =>
            A (n + 1) (fun j => (v (i.succAbove j)).1) (v i).2)]
          apply congrArg₂ (fun a b : G => a + b)
          · rfl
          · apply Finset.sum_congr rfl
            intro i hi
            apply congrArg (fun vs : Fin (n + 1) → X => A (n + 1) vs (v i.succ).2)
            funext j
            cases j using Fin.cases with
            | zero => simp only [Fin.cons_zero, Fin.succ_succAbove_zero]
            | succ j => simp only [Fin.cons_succ, Fin.succ_succAbove_succ]

theorem linearFiberJet_eq_sum (n : ℕ) (A : LinearFiberJetData X Y G)
    (y : Y) (v : Fin (n + 1) → X × Y) :
    linearFiberJet (n + 1) A y v =
      A (n + 1) (fun i => (v i).1) y +
        ∑ i : Fin (n + 1), A n (fun j => (v (i.succAbove j)).1) (v i).2 := by
  rw [linearFiberJet, MultilinearMap.add_apply, linearFiberMain_apply,
    linearFiberRemainder_eq_sum]

theorem hasDerivAt_linearFiberRemainder
    (Q : G →ₗ[ℝ] ℝ) (n : ℕ)
    (A : ℝ → LinearFiberJetData X Y G) (B : LinearFiberJetData X Y G) {t : ℝ}
    (hA : ∀ k (v : Fin k → X) (y : Y),
      HasDerivAt (fun s => Q (A s k v y)) (Q (B k v y)) t)
    (v : Fin n → X × Y) :
    HasDerivAt (fun s => Q (linearFiberRemainder n (A s) v))
      (Q (linearFiberRemainder n B v)) t := by
  induction n generalizing A B with
  | zero =>
      simpa only [linearFiberRemainder_zero_apply, map_zero] using hasDerivAt_const t (0 : ℝ)
  | succ n ih =>
      have hhead := ih (fun s => linearFiberHead (A s) (v 0))
        (linearFiberHead B (v 0))
        (fun k vs y => hA (k + 1) (Fin.cons (v 0).1 vs) y) (Fin.tail v)
      have hmain := hA n (fun i => (v i.succ).1) (v 0).2
      simpa only [linearFiberRemainder_succ_apply, map_add] using hhead.fun_add hmain

/-- The line changes both the coefficient base point and the height
fiber. Only the actual scalar derivatives of the coefficient family are
assumed; the fiber product rule is proved here. -/
theorem hasDerivAt_linearFiberJet_affine
    (Q : G →ₗ[ℝ] ℝ) (n : ℕ) (A : ℝ → LinearFiberJetData X Y G)
    (y : Y) (w : X × Y) {t : ℝ}
    (hA : ∀ k (v : Fin k → X) (η : Y),
      HasDerivAt (fun s => Q (A s k v η))
        (Q (linearFiberHead (A t) w k v η)) t)
    (v : Fin n → X × Y) :
    HasDerivAt (fun s => Q (linearFiberJet n (A s) (y + s • w.2) v))
      (Q (linearFiberJet (n + 1) (A t) (y + t • w.2) (Fin.cons w v))) t := by
  have hy := hA n (fun i => (v i).1) y
  have hw := hA n (fun i => (v i).1) w.2
  have hr := hasDerivAt_linearFiberRemainder Q n A (linearFiberHead (A t) w) hA v
  have hd := (hy.fun_add ((hasDerivAt_id t).mul hw)).fun_add hr
  convert hd using 1
  · funext s
    change Q (A s n (fun i => (v i).1) (y + s • w.2) +
      linearFiberRemainder n (A s) v) = _
    simp only [map_add, map_smul, smul_eq_mul, Pi.mul_apply, id_eq]
  · rw [linearFiberJet_succ_apply]
    change Q (linearFiberHead (A t) w n (fun i => (v i).1) (y + t • w.2) +
      linearFiberRemainder n (linearFiberHead (A t) w) v +
      A t n (fun i => (v i).1) w.2) = _
    simp only [map_add, map_smul, smul_eq_mul, Pi.mul_apply, id_eq, one_mul]
    ring

end ContinuousFlexibility.Analysis
