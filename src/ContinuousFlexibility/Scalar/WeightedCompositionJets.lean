import ContinuousFlexibility.Scalar.WeightedProductJets
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Finite chain rules for the actual mixed cylinder derivatives

The term data are chosen before the scalar function and the input field.
Each differentiation either hits the outer scalar derivative or one of the
inner jets. This records the full chain rule with coefficient one, including
repeated terms, and retains the exact total spatial order of every term.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem composition_iteratedDeriv_contDiff {F : ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (n : ℕ) : ContDiff ℝ ∞ (iteratedDeriv n F) := by
  rw [iteratedDeriv_eq_iterate]
  exact hF.iterate_deriv n

theorem mixedComposition_fderiv_chain {F : ℝ → ℝ} {u : PolarPoint → ℝ}
    (hF : ContDiff ℝ ∞ F) (hu : ContDiff ℝ ∞ u) (n : ℕ) (p v : PolarPoint) :
    fderiv ℝ (fun q => iteratedDeriv n F (u q)) p v =
      iteratedDeriv (n + 1) F (u p) * fderiv ℝ u p v := by
  have hn := composition_iteratedDeriv_contDiff hF n
  rw [fderiv_fun_comp (x := p) (hn.differentiable (by simp) (u p))
    (hu.differentiable (by simp) p), ContinuousLinearMap.comp_apply,
    fderiv_eq_smul_deriv, smul_eq_mul, iteratedDeriv_succ]
  exact mul_comm _ _

private theorem mixedComposition_fderiv_term
    {F : ℝ → ℝ} {u : PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F)
    (hu : ContDiff ℝ ∞ u) {n : ℕ} (g : Fin n → PolarPoint → ℝ)
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) (p v : PolarPoint) :
    fderiv ℝ (fun q => iteratedDeriv n F (u q) * ∏ i, g i q) p v =
      iteratedDeriv (n + 1) F (u p) * fderiv ℝ u p v * (∏ i, g i p) +
        ∑ i, iteratedDeriv n F (u p) * fderiv ℝ (g i) p v *
          ∏ j ∈ Finset.univ.erase i, g j p := by
  have hc : ContDiff ℝ ∞ (fun q => iteratedDeriv n F (u q)) := by
    simpa only [Function.comp_def] using (composition_iteratedDeriv_contDiff hF n).comp hu
  have hp : ContDiff ℝ ∞ (fun q => ∏ i, g i q) :=
    contDiff_prod (fun i _ => hg i)
  rw [fderiv_fun_mul (hc.differentiable (by simp) p) (hp.differentiable (by simp) p)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [mixedComposition_fderiv_chain hF hu,
    mixedProduct_fderiv_prod g (fun i => (hg i).differentiable (by simp) p),
    Finset.mul_sum]
  simp_rw [← mul_assoc]
  ring

/-- Universal finite chain-rule data for mixed derivatives of a scalar
composition. The outer derivative order is the number of inner jet factors. -/
structure MixedCompositionLeibniz (a b : ℕ) where
  Index : Type
  [fintype : Fintype Index]
  arity : Index → ℕ
  radial : (t : Index) → Fin (arity t) → ℕ
  angular : (t : Index) → Fin (arity t) → ℕ
  radial_order : ∀ t, (∑ i, radial t i) = a
  angular_order : ∀ t, (∑ i, angular t i) = b
  formula : ∀ F : ℝ → ℝ, ContDiff ℝ ∞ F →
    ∀ u : PolarPoint → ℝ, ContDiff ℝ ∞ u → ∀ p,
      mixedDerivative a b (fun q => F (u q)) p =
        ∑ t, iteratedDeriv (arity t) F (u p) *
          ∏ i, mixedDerivative (radial t i) (angular t i) u p

attribute [instance] MixedCompositionLeibniz.fintype

private def mixedCompositionLeibniz_zero : MixedCompositionLeibniz 0 0 where
  Index := Unit
  fintype := inferInstance
  arity := fun _ => 0
  radial := fun _ => Fin.elim0
  angular := fun _ => Fin.elim0
  radial_order := by intro t; simp
  angular_order := by intro t; simp
  formula := by
    intro F _ u _ p
    simp only [mixedDerivative, iteratedDeriv_zero, Fin.prod_univ_zero, mul_one,
      Fintype.sum_unique]

/-- Differentiate one coordinate of the finite chain rule. A missing index
hits the outer derivative, and an inner index hits its corresponding jet. -/
def MixedCompositionLeibniz.step {a b : ℕ} (e : MixedCompositionLeibniz a b)
    (radial : Bool) :
    MixedCompositionLeibniz (a + if radial then 1 else 0) (b + if radial then 0 else 1) where
  Index := (t : e.Index) × Option (Fin (e.arity t))
  fintype := inferInstance
  arity := fun t => match t.2 with
    | none => e.arity t.1 + 1
    | some _ => e.arity t.1
  radial := fun t => match t.2 with
    | none => Fin.cons (if radial then 1 else 0) (e.radial t.1)
    | some i => fun j => e.radial t.1 j + if j = i then (if radial then 1 else 0) else 0
  angular := fun t => match t.2 with
    | none => Fin.cons (if radial then 0 else 1) (e.angular t.1)
    | some i => fun j => e.angular t.1 j + if j = i then (if radial then 0 else 1) else 0
  radial_order := by
    rintro ⟨t, hit⟩
    cases hit with
    | none => simp [Fin.sum_univ_succ, e.radial_order, Nat.add_comm]
    | some i => simp [Finset.sum_add_distrib, e.radial_order]
  angular_order := by
    rintro ⟨t, hit⟩
    cases hit with
    | none => simp [Fin.sum_univ_succ, e.angular_order, Nat.add_comm]
    | some i => simp [Finset.sum_add_distrib, e.angular_order]
  formula := by
    classical
    intro F hF u hu p
    let g : (t : e.Index) → Fin (e.arity t) → PolarPoint → ℝ :=
      fun t i => mixedDerivative (e.radial t i) (e.angular t i) u
    have hgs (t : e.Index) (i : Fin (e.arity t)) : ContDiff ℝ ∞ (g t i) :=
      contDiff_mixedDerivative hu (e.radial t i) (e.angular t i)
    have hterm (t : e.Index) :
        ContDiff ℝ ∞ (fun q => iteratedDeriv (e.arity t) F (u q) * ∏ i, g t i q) :=
      ((composition_iteratedDeriv_contDiff hF (e.arity t)).comp hu).mul
        (contDiff_prod (fun i _ => hgs t i))
    have heq : mixedDerivative a b (fun q => F (u q)) =
        fun q => ∑ t : e.Index, iteratedDeriv (e.arity t) F (u q) * ∏ i, g t i q :=
      funext (e.formula F hF u hu)
    have hcomp : ContDiff ℝ ∞ (fun q => F (u q)) := by
      simpa only [Function.comp_def] using hF.comp hu
    rw [← mixedProduct_axis_jet hcomp a b radial p, heq]
    rw [fderiv_fun_sum (fun t _ => (hterm t).differentiable (by simp) p)]
    simp only [sum_apply]
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro t _
    rw [Fintype.sum_option, mixedComposition_fderiv_term hF hu (g t) (hgs t)]
    apply congrArg₂ (fun x y : ℝ => x + y)
    · simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have hfirst : fderiv ℝ u p (if radial then (1, 0) else (0, 1)) =
          mixedDerivative (if radial then 1 else 0) (if radial then 0 else 1) u p := by
        have hzero : mixedDerivative 0 0 u = u := by
          funext q
          simp only [mixedDerivative, iteratedDeriv_zero]
        simpa only [hzero, Nat.zero_add] using mixedProduct_axis_jet hu 0 0 radial p
      rw [hfirst]
      simp only [g]
      ring
    · apply Finset.sum_congr rfl
      intro i _
      change iteratedDeriv (e.arity t) F (u p) *
          fderiv ℝ (mixedDerivative (e.radial t i) (e.angular t i) u) p
            (if radial then (1, 0) else (0, 1)) *
          (∏ j ∈ Finset.univ.erase i, g t j p) = _
      rw [mixedProduct_axis_jet hu (e.radial t i) (e.angular t i) radial p]
      rw [← Finset.mul_prod_erase Finset.univ
        (fun j => mixedDerivative
          (e.radial t j + if j = i then (if radial then 1 else 0) else 0)
          (e.angular t j + if j = i then (if radial then 0 else 1) else 0) u p)
        (Finset.mem_univ i)]
      rw [mul_assoc]
      apply congrArg (fun z : ℝ => iteratedDeriv (e.arity t) F (u p) * z)
      apply congrArg₂ (fun x y : ℝ => x * y)
      · simp
      · apply Finset.prod_congr rfl
        intro j hj
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        simp only [if_neg hji, Nat.add_zero, g]

/-- The all-order mixed chain rule, constructed independently of both functions. -/
def mixedCompositionLeibniz (a b : ℕ) : MixedCompositionLeibniz a b := by
  induction a with
  | zero =>
      induction b with
      | zero => exact mixedCompositionLeibniz_zero
      | succ b ih => exact ih.step false
  | succ a ih => exact ih.step true

/-- Every positive spatial order supplies at least one inner jet factor. -/
theorem MixedCompositionLeibniz.arity_pos {a b : ℕ} (e : MixedCompositionLeibniz a b)
    (hab : 0 < a + b) (t : e.Index) : 0 < e.arity t := by
  by_contra h
  have hn : e.arity t = 0 := by omega
  have hr := e.radial_order t
  have ha := e.angular_order t
  have he : IsEmpty (Fin (e.arity t)) := by rw [hn]; infer_instance
  letI := he
  simp only [Finset.univ_eq_empty, Finset.sum_empty] at hr ha
  omega

end ContinuousFlexibility.Statements
