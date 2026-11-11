import ContinuousFlexibility.Analysis.N01cJointJetContinuity
import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# Multilinear state-and-angle jets

A word records which slots differentiate the state and which slots
differentiate the angle. Its contribution is the actual state jet of
the appropriate angular derivative, times the remaining scalar slots.
The finite sum is a continuous multilinear map in the original
topological state space. Pure mixed slots recover exactly one word.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

inductive StateAngleWord : ℕ → Type
  | nil : StateAngleWord 0
  | state {n : ℕ} : StateAngleWord n → StateAngleWord (n + 1)
  | angle {n : ℕ} : StateAngleWord n → StateAngleWord (n + 1)
  deriving DecidableEq

instance : Unique (StateAngleWord 0) where
  default := .nil
  uniq w := by cases w; rfl

def StateAngleWord.succEquiv (n : ℕ) :
    StateAngleWord n ⊕ StateAngleWord n ≃ StateAngleWord (n + 1) where
  toFun := Sum.elim StateAngleWord.state StateAngleWord.angle
  invFun w := match w with | .state v => .inl v | .angle v => .inr v
  left_inv w := by cases w <;> rfl
  right_inv w := by cases w <;> rfl

def stateAngleWordFintype : (n : ℕ) → Fintype (StateAngleWord n)
  | 0 => inferInstance
  | n + 1 => by
      letI := stateAngleWordFintype n
      exact Fintype.ofEquiv (StateAngleWord n ⊕ StateAngleWord n) (StateAngleWord.succEquiv n)
attribute [instance] stateAngleWordFintype

def StateAngleWord.stateArity : {n : ℕ} → StateAngleWord n → ℕ
  | _, .nil => 0
  | _, .state w => w.stateArity + 1
  | _, .angle w => w.stateArity

def StateAngleWord.angleArity : {n : ℕ} → StateAngleWord n → ℕ
  | _, .nil => 0
  | _, .state w => w.angleArity
  | _, .angle w => w.angleArity + 1

theorem StateAngleWord.arity_sum {n : ℕ} (w : StateAngleWord n) :
    w.stateArity + w.angleArity = n := by
  induction w with
  | nil => rfl
  | state w ih => simp only [stateArity, angleArity]; omega
  | angle w ih => simp only [stateArity, angleArity]; omega

theorem sum_stateAngleWord_succ (n : ℕ) (f : StateAngleWord (n + 1) → ℝ) :
    (∑ w, f w) = (∑ w : StateAngleWord n, f (.state w)) +
      ∑ w : StateAngleWord n, f (.angle w) := by
  rw [← (StateAngleWord.succEquiv n).sum_comp]
  simp only [Fintype.sum_sum_type, StateAngleWord.succEquiv, Equiv.coe_fn_mk,
    Sum.elim_inl, Sum.elim_inr]

section Slots

variable {E : Type*}

def StateAngleWord.stateDirections : {n : ℕ} → (w : StateAngleWord n) →
    (Fin n → E × ℝ) → (Fin w.stateArity → E)
  | _, .nil, _ => Fin.elim0
  | _, .state w, v => Fin.cons (v 0).1 (w.stateDirections (Fin.tail v))
  | _, .angle w, v => w.stateDirections (Fin.tail v)

def StateAngleWord.angleFactor : {n : ℕ} → StateAngleWord n → (Fin n → E × ℝ) → ℝ
  | _, .nil, _ => 1
  | _, .state w, v => w.angleFactor (Fin.tail v)
  | _, .angle w, v => (v 0).2 * w.angleFactor (Fin.tail v)

variable [Zero E]

/-- The pure mixed slots corresponding to the word. Angle slots are the
actual unit angle direction, and state slots have zero angle component. -/
def StateAngleWord.pureSlots : {n : ℕ} → (w : StateAngleWord n) →
    (Fin w.stateArity → E) → (Fin n → E × ℝ)
  | _, .nil, _ => Fin.elim0
  | _, .state w, v => Fin.cons (v 0, 0) (w.pureSlots (Fin.tail v))
  | _, .angle w, v => Fin.cons (0, 1) (w.pureSlots v)

end Slots

section AlgebraicLift

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The word operation is linear in its actual state-multilinear
coefficient. Algebraic currying handles empty state or angle arities. -/
def stateAngleWordLinearLift : {n : ℕ} → (w : StateAngleWord n) →
    MultilinearMap ℝ (fun _ : Fin w.stateArity => E) ℝ →ₗ[ℝ]
      MultilinearMap ℝ (fun _ : Fin n => E × ℝ) ℝ
  | _, .nil =>
      { toFun := fun K => K.compLinearMap (fun _ => LinearMap.fst ℝ E ℝ)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  | _, .state w =>
      { toFun := fun K =>
          (((stateAngleWordLinearLift w).comp K.curryLeft).comp
            (LinearMap.fst ℝ E ℝ)).uncurryLeft
        map_add' := by
          intro K L
          ext v
          change stateAngleWordLinearLift w ((K + L).curryLeft (v 0).1) (Fin.tail v) = _
          have he : (K + L).curryLeft (v 0).1 = K.curryLeft (v 0).1 + L.curryLeft (v 0).1 := rfl
          rw [he, map_add]
          rfl
        map_smul' := by
          intro a K
          ext v
          change stateAngleWordLinearLift w ((a • K).curryLeft (v 0).1) (Fin.tail v) = _
          have he : (a • K).curryLeft (v 0).1 = a • K.curryLeft (v 0).1 := rfl
          rw [he, map_smul]
          rfl }
  | _, .angle w =>
      { toFun := fun K =>
          ((LinearMap.snd ℝ E ℝ).smulRight (stateAngleWordLinearLift w K)).uncurryLeft
        map_add' := by
          intro K L
          ext v
          change (v 0).2 • (stateAngleWordLinearLift w (K + L) (Fin.tail v)) = _
          rw [map_add]
          change (v 0).2 * (_ + _) = (v 0).2 * _ + (v 0).2 * _
          ring
        map_smul' := by
          intro a K
          ext v
          change (v 0).2 • (stateAngleWordLinearLift w (a • K) (Fin.tail v)) = _
          rw [map_smul]
          change (v 0).2 * (a * _) = a * ((v 0).2 * _)
          ring }

theorem stateAngleWordLinearLift_apply {n : ℕ} (w : StateAngleWord n)
    (K : MultilinearMap ℝ (fun _ : Fin w.stateArity => E) ℝ) (v : Fin n → E × ℝ) :
    stateAngleWordLinearLift w K v = K (w.stateDirections v) * w.angleFactor v := by
  induction w generalizing K with
  | nil =>
      change K (fun i : Fin 0 => (v i).1) = K Fin.elim0 * 1
      rw [mul_one]
      congr 1
      funext i
      exact i.elim0
  | state w ih =>
      change stateAngleWordLinearLift w (K.curryLeft (v 0).1) (Fin.tail v) = _
      rw [ih]
      rfl
  | angle w ih =>
      change (v 0).2 * stateAngleWordLinearLift w K (Fin.tail v) = _
      rw [ih]
      simp only [StateAngleWord.stateDirections, StateAngleWord.angleFactor]
      ring

end AlgebraicLift

section ContinuousLift

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

theorem continuous_stateAngleWord_stateDirections {n : ℕ} (w : StateAngleWord n) :
    Continuous (w.stateDirections : (Fin n → E × ℝ) → (Fin w.stateArity → E)) := by
  induction w with
  | nil => exact continuous_const
  | state w ih =>
      apply continuous_pi
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact continuous_fst.comp (continuous_apply 0)
      · exact ((continuous_apply j).comp ih).comp (continuous_pi (fun i => continuous_apply i.succ))
  | angle w ih => exact ih.comp (continuous_pi (fun i => continuous_apply i.succ))

theorem continuous_stateAngleWord_angleFactor {n : ℕ} (w : StateAngleWord n) :
    Continuous (w.angleFactor : (Fin n → E × ℝ) → ℝ) := by
  induction w with
  | nil => exact continuous_const
  | state w ih => exact ih.comp (continuous_pi (fun i => continuous_apply i.succ))
  | angle w ih => exact (continuous_snd.comp (continuous_apply 0)).mul
      (ih.comp (continuous_pi (fun i => continuous_apply i.succ)))

def stateAngleWordMultilinear {n : ℕ} (w : StateAngleWord n)
    (K : E [×w.stateArity]→L[ℝ] ℝ) : (E × ℝ) [×n]→L[ℝ] ℝ where
  toMultilinearMap := stateAngleWordLinearLift w K.toMultilinearMap
  cont := by
    simp only [stateAngleWordLinearLift_apply]
    exact (K.cont.comp (continuous_stateAngleWord_stateDirections w)).mul
      (continuous_stateAngleWord_angleFactor w)

@[simp] theorem stateAngleWordMultilinear_apply {n : ℕ} (w : StateAngleWord n)
    (K : E [×w.stateArity]→L[ℝ] ℝ) (v : Fin n → E × ℝ) :
    stateAngleWordMultilinear w K v = K (w.stateDirections v) * w.angleFactor v :=
  stateAngleWordLinearLift_apply w K.toMultilinearMap v

def continuousMultilinearFixHead {n : ℕ} (K : E [×(n + 1)]→L[ℝ] ℝ) (u : E) :
    E [×n]→L[ℝ] ℝ where
  toMultilinearMap := K.toMultilinearMap.curryLeft u
  cont := K.cont.comp (by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_const
    · exact continuous_apply j)

@[simp] theorem continuousMultilinearFixHead_apply {n : ℕ}
    (K : E [×(n + 1)]→L[ℝ] ℝ) (u : E) (v : Fin n → E) :
    continuousMultilinearFixHead K u v = K (Fin.cons u v) := rfl

theorem continuousMultilinearFixHead_zero {n : ℕ} (K : E [×(n + 1)]→L[ℝ] ℝ) :
    continuousMultilinearFixHead K 0 = 0 := by
  ext v
  exact K.map_coord_zero 0 (by rfl)

def stateAngleJet (K : ∀ b k : ℕ, E [×k]→L[ℝ] ℝ) (n : ℕ) :
    (E × ℝ) [×n]→L[ℝ] ℝ :=
  ∑ w : StateAngleWord n, stateAngleWordMultilinear w (K w.angleArity w.stateArity)

@[simp] theorem stateAngleJet_apply (K : ∀ b k : ℕ, E [×k]→L[ℝ] ℝ)
    (n : ℕ) (v : Fin n → E × ℝ) :
    stateAngleJet K n v = ∑ w : StateAngleWord n,
      K w.angleArity w.stateArity (w.stateDirections v) * w.angleFactor v := by
  simp only [stateAngleJet, ContinuousMultilinearMap.sum_apply, stateAngleWordMultilinear_apply]

theorem stateAngleJet_zero (K : ∀ b k : ℕ, E [×k]→L[ℝ] ℝ) (v : Fin 0 → E × ℝ) :
    stateAngleJet K 0 v = K 0 0 Fin.elim0 := by
  rw [stateAngleJet_apply, Fintype.sum_unique]
  exact mul_one _

theorem stateAngleJet_zero_family (n : ℕ) (v : Fin n → E × ℝ) :
    stateAngleJet (fun _ k => (0 : E [×k]→L[ℝ] ℝ)) n v = 0 := by
  simp only [stateAngleJet_apply, ContinuousMultilinearMap.zero_apply, zero_mul, Finset.sum_const_zero]

/-- The two choices for the new head slot. This exact recurrence will
also identify the true joint derivative of the finite sum. -/
theorem stateAngleJet_cons_apply (K : ∀ b k : ℕ, E [×k]→L[ℝ] ℝ)
    (n : ℕ) (u : E × ℝ) (v : Fin n → E × ℝ) :
    stateAngleJet K (n + 1) (Fin.cons u v) =
      stateAngleJet (fun b k => continuousMultilinearFixHead (K b (k + 1)) u.1) n v +
        u.2 * stateAngleJet (fun b k => K (b + 1) k) n v := by
  rw [stateAngleJet_apply, sum_stateAngleWord_succ]
  simp only [StateAngleWord.angleArity, StateAngleWord.stateArity,
    StateAngleWord.stateDirections, StateAngleWord.angleFactor, Fin.cons_zero, Fin.tail_cons,
    stateAngleJet_apply, continuousMultilinearFixHead_apply, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  ring

/-- Pure mixed slots recover the original state jet of the original
angular derivative, in the exact order specified by the word. -/
theorem stateAngleJet_pureSlots {n : ℕ} (w : StateAngleWord n)
    (K : ∀ b k : ℕ, E [×k]→L[ℝ] ℝ) (v : Fin w.stateArity → E) :
    stateAngleJet K n (w.pureSlots v) = K w.angleArity w.stateArity v := by
  induction w generalizing K with
  | nil =>
      rw [stateAngleJet_zero]
      congr 1
      funext i
      exact i.elim0
  | state w ih =>
      rw [StateAngleWord.pureSlots, stateAngleJet_cons_apply]
      simp only [zero_mul, add_zero]
      rw [ih]
      change K w.angleArity (w.stateArity + 1) (Fin.cons (v 0) (Fin.tail v)) = _
      rw [Fin.cons_self_tail]
      rfl
  | angle w ih =>
      rw [StateAngleWord.pureSlots, stateAngleJet_cons_apply]
      simp only [continuousMultilinearFixHead_zero, stateAngleJet_zero_family, one_mul, zero_add]
      exact ih _ _

end ContinuousLift

end ContinuousFlexibility.Analysis
