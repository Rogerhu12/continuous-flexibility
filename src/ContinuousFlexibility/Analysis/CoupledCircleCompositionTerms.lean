import ContinuousFlexibility.Analysis.CoupledCirclePointwiseBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Terms in the angular jets of circle composition

The order attached to a derivative of the inner chart is one less than
its angular derivative order. With this convention both parts of the
chain rule increase the total budget by one. No inverse chart or lower
bound on its derivative is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem coupled_sum_update_succ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (o : ι → ℕ) (i : ι) :
    (∑ j, Function.update o i (o i + 1) j) = (∑ j, o j) + 1 := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have h := Finset.sum_update_of_mem (Finset.mem_univ i) o (o i)
  rw [Function.update_eq_self] at h
  omega

structure CoupledCircleCompositionTerm (k : ℕ) where
  outerOrder : ℕ
  baseFactors : ℕ
  baseOrder : Fin baseFactors → ℕ
  directionOrder : Fin k → ℕ

namespace CoupledCircleCompositionTerm

variable {k : ℕ}

def order (t : CoupledCircleCompositionTerm k) : ℕ :=
  t.outerOrder + (∑ i, t.baseOrder i) + ∑ i, t.directionOrder i

def evaluate (t : CoupledCircleCompositionTerm k) (v ψ : ℝ → ℝ)
    (w : Fin k → ℝ → ℝ) (θ : ℝ) : ℝ :=
  iteratedDeriv t.outerOrder v (θ + ψ θ) *
    (∏ i, iteratedDeriv (t.baseOrder i + 1) ψ θ) *
    ∏ i, iteratedDeriv (t.directionOrder i) (w i) θ

theorem evaluate_contDiff (t : CoupledCircleCompositionTerm k)
    {v ψ : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hψ : ContDiff ℝ ∞ ψ)
    {w : Fin k → ℝ → ℝ} (hw : ∀ i, ContDiff ℝ ∞ (w i)) :
    ContDiff ℝ ∞ (t.evaluate v ψ w) :=
  (((spaces_contDiff_iteratedDeriv hv _).comp (contDiff_id.add hψ)).mul
    (contDiff_prod (fun i _ => spaces_contDiff_iteratedDeriv hψ _))).mul
      (contDiff_prod (fun i _ => spaces_contDiff_iteratedDeriv (hw i) _))

theorem evaluate_periodic (t : CoupledCircleCompositionTerm k)
    {v ψ : ℝ → ℝ} (hv : Function.Periodic v Real.pi)
    (hψ : Function.Periodic ψ Real.pi) {w : Fin k → ℝ → ℝ}
    (hw : ∀ i, Function.Periodic (w i) Real.pi) :
    Function.Periodic (t.evaluate v ψ w) Real.pi := by
  intro θ
  have hc : (θ + Real.pi) + ψ (θ + Real.pi) = (θ + ψ θ) + Real.pi := by
    rw [hψ θ]
    ring
  change
    iteratedDeriv t.outerOrder v ((θ + Real.pi) + ψ (θ + Real.pi)) *
        (∏ i, iteratedDeriv (t.baseOrder i + 1) ψ (θ + Real.pi)) *
        (∏ i, iteratedDeriv (t.directionOrder i) (w i) (θ + Real.pi)) =
      iteratedDeriv t.outerOrder v (θ + ψ θ) *
        (∏ i, iteratedDeriv (t.baseOrder i + 1) ψ θ) *
        (∏ i, iteratedDeriv (t.directionOrder i) (w i) θ)
  rw [hc, spaces_periodic_iteratedDeriv hv t.outerOrder (θ + ψ θ)]
  congr 1
  · congr 1
    exact Finset.prod_congr rfl (fun i _ =>
      spaces_periodic_iteratedDeriv hψ (t.baseOrder i + 1) θ)
  · exact Finset.prod_congr rfl (fun i _ =>
      spaces_periodic_iteratedDeriv (hw i) (t.directionOrder i) θ)

def chainIdentity (t : CoupledCircleCompositionTerm k) : CoupledCircleCompositionTerm k :=
  { t with outerOrder := t.outerOrder + 1 }

def chainBase (t : CoupledCircleCompositionTerm k) : CoupledCircleCompositionTerm k where
  outerOrder := t.outerOrder + 1
  baseFactors := t.baseFactors + 1
  baseOrder := Fin.cons 0 t.baseOrder
  directionOrder := t.directionOrder

def baseDerivative (t : CoupledCircleCompositionTerm k) (i : Fin t.baseFactors) :
    CoupledCircleCompositionTerm k :=
  { t with baseOrder := Function.update t.baseOrder i (t.baseOrder i + 1) }

def directionDerivative (t : CoupledCircleCompositionTerm k) (i : Fin k) :
    CoupledCircleCompositionTerm k :=
  { t with directionOrder := Function.update t.directionOrder i (t.directionOrder i + 1) }

@[simp] theorem chainIdentity_order (t : CoupledCircleCompositionTerm k) :
    t.chainIdentity.order = t.order + 1 := by
  simp only [order, chainIdentity]
  omega

@[simp] theorem chainBase_order (t : CoupledCircleCompositionTerm k) :
    t.chainBase.order = t.order + 1 := by
  simp only [order, chainBase, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, zero_add]
  omega

@[simp] theorem baseDerivative_order (t : CoupledCircleCompositionTerm k) (i : Fin t.baseFactors) :
    (t.baseDerivative i).order = t.order + 1 := by
  simp only [order, baseDerivative, coupled_sum_update_succ]
  omega

@[simp] theorem directionDerivative_order (t : CoupledCircleCompositionTerm k) (i : Fin k) :
    (t.directionDerivative i).order = t.order + 1 := by
  simp only [order, directionDerivative, coupled_sum_update_succ]
  omega

def initial (r k : ℕ) : CoupledCircleCompositionTerm k where
  outerOrder := r
  baseFactors := 0
  baseOrder := Fin.elim0
  directionOrder := fun _ => 0

@[simp] theorem initial_order (r k : ℕ) : (initial r k).order = r := by
  simp only [order, initial, Fin.sum_univ_zero, Finset.sum_const_zero, add_zero]

theorem initial_evaluate (r k : ℕ) (v ψ : ℝ → ℝ) (w : Fin k → ℝ → ℝ) (θ : ℝ) :
    (initial r k).evaluate v ψ w θ = iteratedDeriv r v (θ + ψ θ) * ∏ i, w i θ := by
  simp only [evaluate, initial, Fin.prod_univ_zero, mul_one, iteratedDeriv_zero]

private theorem iteratedDeriv_hasDerivAt {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (θ : ℝ) :
    HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f θ) θ := by
  rw [iteratedDeriv_succ]
  exact ((spaces_contDiff_iteratedDeriv hf n).differentiable (by simp) θ).hasDerivAt

private theorem product_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    (o : ι → ℕ) (f : ι → ℝ → ℝ) (i : ι) (n : ℕ) (θ : ℝ) :
    (∏ j, iteratedDeriv (Function.update o i n j) (f j) θ) =
      iteratedDeriv n (f i) θ * ∏ j ∈ Finset.univ.erase i, iteratedDeriv (o j) (f j) θ := by
  have he : (fun j => iteratedDeriv (Function.update o i n j) (f j) θ) =
      Function.update (fun j => iteratedDeriv (o j) (f j) θ) i (iteratedDeriv n (f i) θ) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hj]
  rw [he, Finset.prod_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]

private theorem product_hasDerivAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (o : ι → ℕ) {f : ι → ℝ → ℝ} (hf : ∀ i, ContDiff ℝ ∞ (f i)) (θ : ℝ) :
    HasDerivAt (fun x => ∏ i, iteratedDeriv (o i) (f i) x)
      (∑ i, ∏ j, iteratedDeriv (Function.update o i (o i + 1) j) (f j) θ) θ := by
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (fun i _ => iteratedDeriv_hasDerivAt (hf i) (o i) θ)
  simp only [smul_eq_mul] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [product_update, mul_comm]

theorem evaluate_deriv (t : CoupledCircleCompositionTerm k)
    {v ψ : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hψ : ContDiff ℝ ∞ ψ)
    {w : Fin k → ℝ → ℝ} (hw : ∀ i, ContDiff ℝ ∞ (w i)) (θ : ℝ) :
    deriv (t.evaluate v ψ w) θ =
      t.chainIdentity.evaluate v ψ w θ + t.chainBase.evaluate v ψ w θ +
        (∑ i, (t.baseDerivative i).evaluate v ψ w θ) +
        ∑ i, (t.directionDerivative i).evaluate v ψ w θ := by
  have harg := (hasDerivAt_id θ).add (iteratedDeriv_hasDerivAt hψ 0 θ)
  simp only [iteratedDeriv_zero] at harg
  have hout := (iteratedDeriv_hasDerivAt hv t.outerOrder (θ + ψ θ)).comp θ harg
  have hbase := product_hasDerivAt (fun i => t.baseOrder i + 1) (fun _ => hψ) θ
  have hdir := product_hasDerivAt t.directionOrder hw θ
  have h := (hout.mul hbase).mul hdir
  change HasDerivAt (t.evaluate v ψ w) _ θ at h
  rw [h.deriv]
  have horders (i : Fin t.baseFactors) :
      (fun j => Function.update t.baseOrder i (t.baseOrder i + 1) j + 1) =
        Function.update (fun j => t.baseOrder j + 1) i (t.baseOrder i + 1 + 1) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hj]
  have hsumBase :
      iteratedDeriv t.outerOrder v (θ + ψ θ) *
        (∑ i, ∏ j, iteratedDeriv
          (Function.update (fun j => t.baseOrder j + 1) i (t.baseOrder i + 1 + 1) j) ψ θ) *
        (∏ i, iteratedDeriv (t.directionOrder i) (w i) θ) =
        ∑ i, (t.baseDerivative i).evaluate v ψ w θ := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [evaluate, baseDerivative]
    rw [← horders i]
  have hsumDir :
      iteratedDeriv t.outerOrder v (θ + ψ θ) *
        (∏ i, iteratedDeriv (t.baseOrder i + 1) ψ θ) *
        (∑ i, ∏ j, iteratedDeriv
          (Function.update t.directionOrder i (t.directionOrder i + 1) j) (w j) θ) =
        ∑ i, (t.directionDerivative i).evaluate v ψ w θ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  rw [← hsumBase, ← hsumDir]
  simp only [evaluate, chainIdentity, chainBase, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, zero_add, Function.comp_apply,
    Pi.add_apply, Pi.mul_apply, id_eq]
  ring

end CoupledCircleCompositionTerm

end ContinuousFlexibility.Statements
