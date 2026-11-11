import ContinuousFlexibility.Analysis.N01cPhysicalFlowRadialRecursion
import ContinuousFlexibility.Scalar.WeightedProductJets

/-!
# Actual coordinate words for physical Lie derivatives

A word evaluates an actual iterated Fréchet derivative on coordinate
directions. Differentiating one factor prepends exactly one direction.
The product rule retains repeated terms with coefficient one, so its
finite indices carry the original distribution of spatial orders.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

/-- The ordered coordinate slots of one actual speed jet. -/
structure PhysicalLieWord where
  order : ℕ
  axes : Fin order → Fin 2

namespace PhysicalLieWord

def empty : PhysicalLieWord := ⟨0, Fin.elim0⟩

def prepend (j : Fin 2) (w : PhysicalLieWord) : PhysicalLieWord :=
  ⟨w.order + 1, Fin.cons j w.axes⟩

def radialOrder (w : PhysicalLieWord) : ℕ :=
  ∑ i, if w.axes i = 0 then 1 else 0

def angularOrder (w : PhysicalLieWord) : ℕ :=
  ∑ i, if w.axes i = 0 then 0 else 1

def eval (w : PhysicalLieWord) (f : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  iteratedFDeriv ℝ w.order f p (fun i => cylinderBasisVector (w.axes i))

theorem eval_empty (f : PolarPoint → ℝ) (p : PolarPoint) :
    empty.eval f p = f p := by
  simp only [eval, empty, iteratedFDeriv_zero_apply]

theorem radialOrder_add_angularOrder (w : PhysicalLieWord) :
    w.radialOrder + w.angularOrder = w.order := by
  classical
  rw [radialOrder, angularOrder, ← Finset.sum_add_distrib]
  calc
    _ = ∑ _ : Fin w.order, (1 : ℕ) := Finset.sum_congr rfl (fun i _ => by
      by_cases hi : w.axes i = 0 <;> simp only [hi, if_true, if_false, zero_add, add_zero])
    _ = w.order := by simp

theorem radialOrder_le (w : PhysicalLieWord) : w.radialOrder ≤ w.order := by
  rw [← w.radialOrder_add_angularOrder]
  omega

theorem angularOrder_le (w : PhysicalLieWord) : w.angularOrder ≤ w.order := by
  rw [← w.radialOrder_add_angularOrder]
  omega

theorem radialOrder_prepend (j : Fin 2) (w : PhysicalLieWord) :
    (prepend j w).radialOrder = (if j = 0 then 1 else 0) + w.radialOrder := by
  simp only [radialOrder, prepend, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem angularOrder_prepend (j : Fin 2) (w : PhysicalLieWord) :
    (prepend j w).angularOrder = (if j = 0 then 0 else 1) + w.angularOrder := by
  simp only [angularOrder, prepend, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem eval_eq_mixedDerivative
    {Ω : Set PolarPoint} {f : PolarPoint → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (w : PhysicalLieWord) {p : PolarPoint} (hp : p ∈ Ω) :
    w.eval f p = mixedDerivative w.radialOrder w.angularOrder f p :=
  iteratedFDeriv_cylinderBasis_eq_mixedDerivative hΩ hf w.order hp w.axes

theorem contDiffOn_eval
    {Ω : Set PolarPoint} {f : PolarPoint → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) (w : PhysicalLieWord) :
    ContDiffOn ℝ ∞ (w.eval f) Ω := by
  intro p hp
  have hj : ContDiffAt ℝ ∞ (iteratedFDeriv ℝ w.order f) p :=
    (hf.contDiffAt (hΩ.mem_nhds hp)).iteratedFDeriv_right (by simp)
  exact ((contDiff_multilinearEvaluation w.order).contDiffAt.comp p
    (hj.prodMk contDiffAt_const)).contDiffWithinAt

/-- The derivative is a genuine next jet, with the new coordinate first. -/
theorem fderiv_eval
    {Ω : Set PolarPoint} {f : PolarPoint → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (w : PhysicalLieWord) (j : Fin 2) {p : PolarPoint} (hp : p ∈ Ω) :
    fderiv ℝ (w.eval f) p (cylinderBasisVector j) = (prepend j w).eval f p := by
  have hj : DifferentiableAt ℝ (iteratedFDeriv ℝ w.order f) p :=
    ((hf.contDiffAt (hΩ.mem_nhds hp)).iteratedFDeriv_right
      (m := ∞) (by simp)).differentiableAt (by simp)
  have hv : (fun i : Fin (w.order + 1) =>
      cylinderBasisVector (Fin.cons j w.axes i)) =
      Fin.cons (cylinderBasisVector j) (fun i => cylinderBasisVector (w.axes i)) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero]
    · simp only [Fin.cons_succ]
  simpa only [eval, prepend, hv, Fin.tail_cons, Fin.cons_zero] using
    (hj.iteratedFDeriv_succ_apply_left'
      (m := Fin.cons (cylinderBasisVector j) (fun i => cylinderBasisVector (w.axes i)))).symm

end PhysicalLieWord

/-- One differentiation chooses exactly one factor. -/
def physicalLieHit {n : ℕ} (w : Fin n → PhysicalLieWord) (j : Fin 2)
    (i : Fin n) : Fin n → PhysicalLieWord :=
  fun l => if l = i then PhysicalLieWord.prepend j (w l) else w l

theorem physicalLieHit_order {n : ℕ} (w : Fin n → PhysicalLieWord)
    (j : Fin 2) (i l : Fin n) :
    (physicalLieHit w j i l).order = (w l).order + if l = i then 1 else 0 := by
  by_cases h : l = i <;> simp only [physicalLieHit, h, if_true, if_false,
    PhysicalLieWord.prepend, Nat.add_zero]

theorem physicalLieHit_total_order {n : ℕ} (w : Fin n → PhysicalLieWord)
    (j : Fin 2) (i : Fin n) :
    (∑ l, (physicalLieHit w j i l).order) = (∑ l, (w l).order) + 1 := by
  simp only [physicalLieHit_order, Finset.sum_add_distrib]
  simp

theorem contDiffOn_physicalLieMonomial
    {Ω : Set PolarPoint} {f : PolarPoint → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    {n : ℕ} (w : Fin n → PhysicalLieWord) :
    ContDiffOn ℝ ∞ (fun q => ∏ i, (w i).eval f q) Ω := by
  apply contDiffOn_prod
  intro i _
  exact PhysicalLieWord.contDiffOn_eval hΩ hf (w i)

/-- Exact product differentiation, without combining repeated terms. -/
theorem fderiv_physicalLieMonomial
    {Ω : Set PolarPoint} {f : PolarPoint → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    {n : ℕ} (w : Fin n → PhysicalLieWord) (j : Fin 2)
    {p : PolarPoint} (hp : p ∈ Ω) :
    fderiv ℝ (fun q => ∏ i, (w i).eval f q) p (cylinderBasisVector j) =
      ∑ i : Fin n, ∏ l, (physicalLieHit w j i l).eval f p := by
  classical
  rw [mixedProduct_fderiv_prod (fun i => (w i).eval f)
    (fun i => ((PhysicalLieWord.contDiffOn_eval hΩ hf (w i)).contDiffAt
      (hΩ.mem_nhds hp)).differentiableAt (by simp))]
  apply Finset.sum_congr rfl
  intro i _
  rw [PhysicalLieWord.fderiv_eval hΩ hf (w i) j hp]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun l => (physicalLieHit w j i l).eval f p) (Finset.mem_univ i)]
  apply congrArg₂ (fun a b : ℝ => a * b)
  · simp only [physicalLieHit, if_pos rfl]
  · apply Finset.prod_congr rfl
    intro l hl
    simp only [physicalLieHit, if_neg (Finset.mem_erase.mp hl).1]

/-- Differentiating a finite family of monomials records both the old term
and the factor that was hit. -/
theorem fderiv_physicalLieSum
    {I : Type*} [Fintype I] (arity : I → ℕ)
    (words : ∀ t, Fin (arity t) → PhysicalLieWord)
    {Ω : Set PolarPoint} {f : PolarPoint → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (j : Fin 2) {p : PolarPoint} (hp : p ∈ Ω) :
    fderiv ℝ (fun q => ∑ t : I, ∏ i, (words t i).eval f q) p (cylinderBasisVector j) =
      ∑ ti : (Σ t : I, Fin (arity t)), ∏ l,
        (physicalLieHit (words ti.1) j ti.2 l).eval f p := by
  classical
  rw [fderiv_fun_sum (fun t _ => ((contDiffOn_physicalLieMonomial hΩ hf (words t)).contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp))]
  simp only [sum_apply]
  rw [Fintype.sum_sigma (fun ti : (Σ t : I, Fin (arity t)) =>
    ∏ l, (physicalLieHit (words ti.1) j ti.2 l).eval f p)]
  exact Finset.sum_congr rfl (fun t _ => fderiv_physicalLieMonomial hΩ hf (words t) j hp)

end ContinuousFlexibility.Analysis
