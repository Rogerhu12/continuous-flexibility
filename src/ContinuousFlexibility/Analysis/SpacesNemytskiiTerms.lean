module

public import ContinuousFlexibility.Analysis.SpacesNemytskiiWeights
public import ContinuousFlexibility.Analysis.MaterialCylinderPointwise
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Terms in a normalized composition jet

A term records the derivatives of the repeated base function and of each
direction. Its radial coefficient retains exactly the power of `H`
determined by the number of factors. This records the derivative budget
needed for a fixed-loss tame estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

theorem spacesRadialMultiplier_zero (T : MaterialData) (α : ℝ) :
    SpacesRadialMultiplier T α (fun _ => 0) := by
  refine ⟨contDiff_const, fun n => ⟨0, le_rfl, fun x => ?_⟩⟩
  change |iteratedDeriv n (0 : ℝ → ℝ) x| ≤ 0 * T.H (T.radius x) ^ α
  simp only [iteratedDeriv_const_zero, abs_zero, zero_mul, le_refl]

def spacesJetOrderSucc (radial : Bool) (o : ℕ × ℕ) : ℕ × ℕ :=
  if radial then (o.1 + 1, o.2) else (o.1, o.2 + 1)

theorem spacesJetOrderSucc_total (radial : Bool) (o : ℕ × ℕ) :
    (spacesJetOrderSucc radial o).1 + (spacesJetOrderSucc radial o).2 = o.1 + o.2 + 1 := by
  cases radial <;> simp only [spacesJetOrderSucc, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem spaces_jet_order_sum_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    (o : ι → ℕ × ℕ) (i : ι) (radial : Bool) :
    (∑ j, ((Function.update o i (spacesJetOrderSucc radial (o i)) j).1 +
      (Function.update o i (spacesJetOrderSucc radial (o i)) j).2)) =
        (∑ j, ((o j).1 + (o j).2)) + 1 := by
  let f (j : ι) := (o j).1 + (o j).2
  have he : (fun j => (Function.update o i (spacesJetOrderSucc radial (o i)) j).1 +
      (Function.update o i (spacesJetOrderSucc radial (o i)) j).2) =
      Function.update f i (f i + 1) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self, spacesJetOrderSucc_total, f]
    · simp only [Function.update_of_ne hj, f]
  rw [he, Finset.sum_update_of_mem (Finset.mem_univ i)]
  have h := Finset.sum_update_of_mem (Finset.mem_univ i) f (f i)
  rw [Function.update_eq_self] at h
  change (f i + 1) + ∑ j ∈ Finset.univ \ {i}, f j = (∑ j, f j) + 1
  omega

structure SpacesNemytskiiTerm (T : MaterialData) (γ : ℝ) (k : ℕ) where
  baseFactors : ℕ
  coefficient : ℝ → ℝ
  coefficient_mem : SpacesRadialMultiplier T ((((k + baseFactors : ℕ) : ℝ) - 1) * γ) coefficient
  baseOrder : Fin baseFactors → ℕ × ℕ
  directionOrder : Fin k → ℕ × ℕ

namespace SpacesNemytskiiTerm

variable {T : MaterialData} {γ : ℝ} {k : ℕ}

def order (t : SpacesNemytskiiTerm T γ k) : ℕ :=
  (∑ i, ((t.baseOrder i).1 + (t.baseOrder i).2)) +
    ∑ i, ((t.directionOrder i).1 + (t.directionOrder i).2)

def evaluate (t : SpacesNemytskiiTerm T γ k) (F : ℝ → ℝ) (u : PolarPoint → ℝ)
    (v : Fin k → PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  t.coefficient p.1 * iteratedDeriv (k + t.baseFactors) F (T.H (T.radius p.1) ^ γ * u p) *
    (∏ i, mixedDerivative (t.baseOrder i).1 (t.baseOrder i).2 u p) *
    ∏ i, mixedDerivative (t.directionOrder i).1 (t.directionOrder i).2 (v i) p

theorem evaluate_contDiff {D : ReferenceData} (hT : IsMaterialData D T)
    (t : SpacesNemytskiiTerm T γ k) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    {u : PolarPoint → ℝ} (hu : ContDiff ℝ ∞ u)
    {v : Fin k → PolarPoint → ℝ} (hv : ∀ i, ContDiff ℝ ∞ (v i)) :
    ContDiff ℝ ∞ (t.evaluate F u v) := by
  have hH : ContDiff ℝ ∞ (fun p : PolarPoint => T.H (T.radius p.1) ^ γ) :=
    (spacesRadialMultiplier_materialH hT γ).contDiff.comp contDiff_fst
  exact (((t.coefficient_mem.contDiff.comp contDiff_fst).mul
    ((spaces_scalar_contDiff_iteratedDeriv hF _).comp (hH.mul hu))).mul
      (contDiff_prod (fun i _ => contDiff_mixedDerivative hu _ _))).mul
        (contDiff_prod (fun i _ => contDiff_mixedDerivative (hv i) _ _))

def coefficientDerivative (t : SpacesNemytskiiTerm T γ k) (radial : Bool) :
    SpacesNemytskiiTerm T γ k where
  baseFactors := t.baseFactors
  coefficient := if radial then deriv t.coefficient else fun _ => 0
  coefficient_mem := by
    cases radial
    · exact spacesRadialMultiplier_zero T _
    · exact t.coefficient_mem.deriv
  baseOrder := t.baseOrder
  directionOrder := t.directionOrder

@[simp] theorem coefficientDerivative_order (t : SpacesNemytskiiTerm T γ k) (radial : Bool) :
    (t.coefficientDerivative radial).order = t.order := rfl

def addBaseFactor {D : ReferenceData} (hT : IsMaterialData D T)
    (t : SpacesNemytskiiTerm T γ k) (o : ℕ × ℕ) (A : ℝ → ℝ)
    (hA : SpacesRadialMultiplier T γ A) : SpacesNemytskiiTerm T γ k where
  baseFactors := t.baseFactors + 1
  coefficient := fun x => t.coefficient x * A x
  coefficient_mem := by
    have he : ((((k + t.baseFactors : ℕ) : ℝ) - 1) * γ) + γ =
        (((k + (t.baseFactors + 1) : ℕ) : ℝ) - 1) * γ := by
      push_cast
      ring
    exact he ▸ t.coefficient_mem.mul hT hA
  baseOrder := Fin.cons o t.baseOrder
  directionOrder := t.directionOrder

theorem addBaseFactor_order {D : ReferenceData} (hT : IsMaterialData D T)
    (t : SpacesNemytskiiTerm T γ k) (o : ℕ × ℕ) (A : ℝ → ℝ)
    (hA : SpacesRadialMultiplier T γ A) :
    (t.addBaseFactor hT o A hA).order = t.order + (o.1 + o.2) := by
  simp only [order, addBaseFactor, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  omega

def baseDerivative (t : SpacesNemytskiiTerm T γ k) (i : Fin t.baseFactors) (radial : Bool) :
    SpacesNemytskiiTerm T γ k where
  baseFactors := t.baseFactors
  coefficient := t.coefficient
  coefficient_mem := t.coefficient_mem
  baseOrder := Function.update t.baseOrder i (spacesJetOrderSucc radial (t.baseOrder i))
  directionOrder := t.directionOrder

theorem baseDerivative_order (t : SpacesNemytskiiTerm T γ k) (i : Fin t.baseFactors) (radial : Bool) :
    (t.baseDerivative i radial).order = t.order + 1 := by
  simp only [order, baseDerivative, spaces_jet_order_sum_update]
  omega

def directionDerivative (t : SpacesNemytskiiTerm T γ k) (i : Fin k) (radial : Bool) :
    SpacesNemytskiiTerm T γ k where
  baseFactors := t.baseFactors
  coefficient := t.coefficient
  coefficient_mem := t.coefficient_mem
  baseOrder := t.baseOrder
  directionOrder := Function.update t.directionOrder i (spacesJetOrderSucc radial (t.directionOrder i))

theorem directionDerivative_order (t : SpacesNemytskiiTerm T γ k) (i : Fin k) (radial : Bool) :
    (t.directionDerivative i radial).order = t.order + 1 := by
  simp only [order, directionDerivative, spaces_jet_order_sum_update]
  omega

def initial {D : ReferenceData} (hT : IsMaterialData D T) (γ : ℝ) (k : ℕ) :
    SpacesNemytskiiTerm T γ k where
  baseFactors := 0
  coefficient := fun x => T.H (T.radius x) ^ (((k : ℝ) - 1) * γ)
  coefficient_mem := by simpa only [Nat.add_zero] using spacesRadialMultiplier_materialH hT (((k : ℝ) - 1) * γ)
  baseOrder := Fin.elim0
  directionOrder := fun _ => (0, 0)

@[simp] theorem initial_order {D : ReferenceData} (hT : IsMaterialData D T) (γ : ℝ) (k : ℕ) :
    (initial hT γ k).order = 0 := by simp only [order, initial, Fin.sum_univ_zero, add_zero, Finset.sum_const_zero]

theorem initial_evaluate {D : ReferenceData} (hT : IsMaterialData D T) (γ : ℝ) (k : ℕ)
    (F : ℝ → ℝ) (u : PolarPoint → ℝ) (v : Fin k → PolarPoint → ℝ) (p : PolarPoint) :
    (initial hT γ k).evaluate F u v p =
      T.H (T.radius p.1) ^ (((k : ℝ) - 1) * γ) * iteratedDeriv k F (T.H (T.radius p.1) ^ γ * u p) *
        ∏ i, v i p := by
  simp only [evaluate, initial, Nat.add_zero, Fin.prod_univ_zero, mul_one,
    mixedDerivative, iteratedDeriv_zero, Prod.mk.eta]

end SpacesNemytskiiTerm

end ContinuousFlexibility.Statements
