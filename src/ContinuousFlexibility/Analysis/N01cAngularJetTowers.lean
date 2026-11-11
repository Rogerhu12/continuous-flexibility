import ContinuousFlexibility.Analysis.N01cParameterCalculus
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Actual angular derivatives of a joint directional tower

Fixing the last slot preserves the genuine directional recurrence,
which prepends each new parameter direction. Applied to the constant
unit angle direction, this gives the actual iterated angular derivatives
of a jointly smooth state-and-angle function. Restricting the angle then
gives genuine state towers without putting a norm on the state space.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology

section FixedDirection

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- Fix the last slot of a continuous multilinear map. Only joint
continuity of its evaluations is used, so no norm on `E` is needed. -/
def continuousMultilinearFixLast {n : ℕ} (A : E [×(n + 1)]→L[ℝ] F) (w : E) :
    E [×n]→L[ℝ] F := by
  classical
  refine
    { toMultilinearMap := MultilinearMap.mk'
        (fun v => A (Fin.snoc v w)) ?_ ?_
      cont := A.cont.comp ?_ }
  · intro v i x y
    simp only [Fin.snoc_update, ContinuousMultilinearMap.map_update_add]
  · intro v i c x
    simp only [Fin.snoc_update, ContinuousMultilinearMap.map_update_smul]
  · apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using (continuous_const : Continuous (fun _ : Fin n → E => w))
    · simpa only [Fin.snoc_castSucc] using (continuous_apply j : Continuous (fun v : Fin n → E => v j))

@[simp] theorem continuousMultilinearFixLast_apply {n : ℕ}
    (A : E [×(n + 1)]→L[ℝ] F) (w : E) (v : Fin n → E) :
    continuousMultilinearFixLast A w v = A (Fin.snoc v w) := rfl

/-- Differentiation in one fixed direction is itself genuinely smooth.
The old direction is placed last, so the original tower's recurrence
can be used directly, without assuming symmetry of its jets. -/
def smoothDirections_fixedDirection {U : Set E} {f : E → F}
    (J : SmoothDirections U f) (w : E) :
    SmoothDirections U (fun x => projectiveFirstJetValue J.D x w) where
  open_domain := J.open_domain
  D n x := continuousMultilinearFixLast (J.D (n + 1) x) w
  zero := by
    intro x _
    change J.D 1 x (Fin.snoc (Fin.elim0 : Fin 0 → E) w) =
      J.D 1 x (Fin.cons w Fin.elim0)
    congr 1
    funext i
    fin_cases i
    rfl
  continuous := by
    intro n
    have hsnoc : Continuous (fun p : E × (Fin n → E) =>
        (Fin.snoc p.2 w : Fin (n + 1) → E)) := by
      apply continuous_pi
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using
          (continuous_const : Continuous (fun _ : E × (Fin n → E) => w))
      · simpa only [Fin.snoc_castSucc] using
          ((continuous_apply j).comp' (f := fun p : E × (Fin n → E) => p.2)
            continuous_snd)
    exact (J.continuous (n + 1)).comp
      (continuous_fst.prodMk hsnoc).continuousOn
      (fun p hp => ⟨hp.1, mem_univ _⟩)
  derivative := by
    intro n x hx v u
    simpa only [continuousMultilinearFixLast_apply, Fin.cons_snoc_eq_snoc_cons] using
      J.derivative (n + 1) x hx (Fin.snoc v w) u

@[simp] theorem smoothDirections_fixedDirection_D_apply {U : Set E} {f : E → F}
    (J : SmoothDirections U f) (w : E) (n : ℕ) (x : E) (v : Fin n → E) :
    (smoothDirections_fixedDirection J w).D n x v =
      J.D (n + 1) x (Fin.snoc v w) := rfl

end FixedDirection

section AngularDerivatives

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The unit angle slot is the genuine scalar derivative of the actual
angular slice, as follows directly from the defining difference quotient. -/
theorem _root_.ContinuousFlexibility.Statements.SmoothDirections.hasDerivAt_angle
    {U : Set E} {f : E × ℝ → ℝ}
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) f)
    {x : E} (hx : x ∈ U) (θ : ℝ) :
    HasDerivAt (fun α => f (x, α))
      (projectiveFirstJetValue J.D (x, θ) (0, 1)) θ := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have h := J.hasProjectiveJetsOn.hasLineDerivAt J.open_domain
    (show (x, θ) ∈ U ×ˢ (univ : Set ℝ) from ⟨hx, mem_univ _⟩)
    ((0 : E), (1 : ℝ))
  simpa only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
    Prod.smul_mk, Prod.mk_add_mk, zero_add, zero_smul, smul_zero,
    smul_eq_mul, mul_one, add_zero] using h

/-- Every actual angular derivative has a genuine joint state-and-angle
tower. Its recurrence appends unit-angle slots to the original tower. -/
def smoothDirections_angularIterate {U : Set E} {f : E × ℝ → ℝ}
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) f) :
    (b : ℕ) → SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun p => iteratedDeriv b (fun α => f (p.1, α)) p.2)
  | 0 => J.congr (fun p _ => by simp only [iteratedDeriv_zero])
  | b + 1 => by
      let K := smoothDirections_angularIterate J b
      refine (smoothDirections_fixedDirection K ((0 : E), 1)).congr ?_
      intro p hp
      change projectiveFirstJetValue K.D p (0, 1) =
        iteratedDeriv (b + 1) (fun α => f (p.1, α)) p.2
      rw [iteratedDeriv_succ]
      exact (K.hasDerivAt_angle hp.1 p.2).deriv.symm

@[simp] theorem smoothDirections_angularIterate_zero_D
    {U : Set E} {f : E × ℝ → ℝ}
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) f)
    (n : ℕ) (p : E × ℝ) (v : Fin n → E × ℝ) :
    (smoothDirections_angularIterate J 0).D n p v = J.D n p v := rfl

@[simp] theorem smoothDirections_angularIterate_succ_D
    {U : Set E} {f : E × ℝ → ℝ}
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) f)
    (b n : ℕ) (p : E × ℝ) (v : Fin n → E × ℝ) :
    (smoothDirections_angularIterate J (b + 1)).D n p v =
      (smoothDirections_angularIterate J b).D (n + 1) p
        (Fin.snoc v ((0 : E), 1)) := rfl

/-- Fixing the angle restricts the actual joint tower to the original
topological state. Every derivative pulls directions back by `v ↦ (v,0)`. -/
def smoothDirections_stateSlice {U : Set E} {f : E × ℝ → ℝ}
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) f) (θ : ℝ) :
    SmoothDirections U (fun x => f (x, θ)) where
  open_domain := by
    have he : (fun x : E => (x, θ)) ⁻¹' (U ×ˢ (univ : Set ℝ)) = U := by
      ext x
      simp only [mem_preimage, mem_prod, mem_univ, and_true]
    rw [← he]
    exact J.open_domain.preimage (continuous_id.prodMk continuous_const)
  D n x := (J.D n (x, θ)).compContinuousLinearMap
    (fun _ => ContinuousLinearMap.inl ℝ E ℝ)
  zero := by
    intro x hx
    change J.D 0 (x, θ) (fun i : Fin 0 => (Fin.elim0 i, (0 : ℝ))) = f (x, θ)
    have he : (fun i : Fin 0 => (Fin.elim0 i, (0 : ℝ))) =
        (Fin.elim0 : Fin 0 → E × ℝ) := by
      funext i
      exact i.elim0
    rw [he]
    exact J.zero (x, θ) ⟨hx, mem_univ _⟩
  continuous := by
    intro n
    exact (J.continuous n).comp
      ((continuous_fst.prodMk continuous_const).prodMk
        (continuous_pi (fun i => ((continuous_apply i).comp continuous_snd).prodMk
          continuous_const))).continuousOn
      (fun p hp => ⟨⟨hp.1, mem_univ _⟩, mem_univ _⟩)
  derivative := by
    intro n x hx v w
    have he : (fun i : Fin (n + 1) =>
        ((Fin.cons (α := fun _ : Fin (n + 1) => E) w v) i, (0 : ℝ))) =
        Fin.cons (α := fun _ : Fin (n + 1) => E × ℝ)
          (w, (0 : ℝ)) (fun i : Fin n => (v i, (0 : ℝ))) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    simpa only [HasProjectiveLineDerivAt,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearMap.inl_apply, Prod.smul_mk, Prod.mk_add_mk,
      smul_zero, add_zero, he] using
      J.derivative n (x, θ) ⟨hx, mem_univ _⟩ (fun i => (v i, 0)) (w, 0)

@[simp] theorem smoothDirections_stateSlice_D_apply {U : Set E} {f : E × ℝ → ℝ}
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) f)
    (θ : ℝ) (n : ℕ) (x : E) (v : Fin n → E) :
    (smoothDirections_stateSlice J θ).D n x v = J.D n (x, θ) (fun i => (v i, 0)) := rfl

/-- The actual `b`-th angle derivative at a fixed angle has a genuine
state tower. This is the interface used in physical radial composition. -/
def smoothDirections_angularStateSlice {U : Set E} {f : E × ℝ → ℝ}
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) f) (b : ℕ) (θ : ℝ) :
    SmoothDirections U (fun x => iteratedDeriv b (fun α => f (x, α)) θ) :=
  smoothDirections_stateSlice (smoothDirections_angularIterate J b) θ

end AngularDerivatives

end ContinuousFlexibility.Analysis
