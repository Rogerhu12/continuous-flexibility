import ContinuousFlexibility.Analysis.N07aFiniteStateProduct
import ContinuousFlexibility.Analysis.N07aSampleEnvelopes

/-!
# Finite monomials with an unspent spatial-order budget

An expression retains all grading factors until its complete finite
formula is known. Its nonnegative sampled coefficients are subpower.
The one-high estimate is applied once, after the expression is assembled.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped BigOperators

structure N07aJetBudgetExpression (T : MaterialData) {S : PhysicalSpacesData}
    (K : CanonicalData S) (budget : ℕ) where
  Index : Type
  finite : Fintype Index
  arity : Index → ℕ
  order : ∀ i, Fin (arity i) → ℕ
  order_le : ∀ i, (∑ j, order i j) ≤ budget
  coeff : Index → ℕ → ℝ
  coeff_subpower : ∀ i, N07aSampleSubpower T K (coeff i)
  coeff_nonneg : ∀ i m, 0 ≤ coeff i m

namespace N07aJetBudgetExpression

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S} {a b : ℕ}

def eval {E : Type*} [AddCommGroup E] [Module ℝ E]
    (e : N07aJetBudgetExpression T K a) (p : ℕ → Seminorm ℝ E) (d : ℕ)
    (z : E) (m : ℕ) : ℝ :=
  letI := e.finite
  ∑ i, e.coeff i m * ∏ j, (1 + p (e.order i j + d) z)

theorem eval_nonneg {E : Type*} [AddCommGroup E] [Module ℝ E]
    (e : N07aJetBudgetExpression T K a) (p : ℕ → Seminorm ℝ E) (d : ℕ)
    (z : E) (m : ℕ) : 0 ≤ e.eval p d z m := by
  letI := e.finite
  exact Finset.sum_nonneg fun i _ => mul_nonneg (e.coeff_nonneg i m)
    (Finset.prod_nonneg fun j _ => add_nonneg zero_le_one (apply_nonneg _ _))

def regrade (e : N07aJetBudgetExpression T K a) (h : a ≤ b) :
    N07aJetBudgetExpression T K b where
  Index := e.Index
  finite := e.finite
  arity := e.arity
  order := e.order
  order_le i := (e.order_le i).trans h
  coeff := e.coeff
  coeff_subpower := e.coeff_subpower
  coeff_nonneg := e.coeff_nonneg

@[simp] theorem eval_regrade {E : Type*} [AddCommGroup E] [Module ℝ E]
    (e : N07aJetBudgetExpression T K a) (h : a ≤ b)
    (p : ℕ → Seminorm ℝ E) (d : ℕ) (z : E) (m : ℕ) :
    (e.regrade h).eval p d z m = e.eval p d z m := rfl

def zero (T : MaterialData) {S : PhysicalSpacesData} (K : CanonicalData S) (a : ℕ) :
    N07aJetBudgetExpression T K a where
  Index := Empty
  finite := inferInstance
  arity := Empty.elim
  order := fun i => Empty.elim i
  order_le := fun i => Empty.elim i
  coeff := fun i => Empty.elim i
  coeff_subpower := fun i => Empty.elim i
  coeff_nonneg := fun i => Empty.elim i

@[simp] theorem eval_zero {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (d : ℕ) (z : E) (m : ℕ) :
    (zero T K a).eval p d z m = 0 := by simp [eval, zero]

def constant (e : ℕ → ℝ) (he : N07aSampleSubpower T K e) (he0 : ∀ m, 0 ≤ e m) :
    N07aJetBudgetExpression T K 0 where
  Index := Unit
  finite := inferInstance
  arity := fun _ => 0
  order := fun _ => Fin.elim0
  order_le := fun _ => by simp
  coeff := fun _ => e
  coeff_subpower := fun _ => he
  coeff_nonneg := fun _ => he0

@[simp] theorem eval_constant {E : Type*} [AddCommGroup E] [Module ℝ E]
    (e : ℕ → ℝ) (he : N07aSampleSubpower T K e) (he0 : ∀ m, 0 ≤ e m)
    (p : ℕ → Seminorm ℝ E) (d : ℕ) (z : E) (m : ℕ) :
    (constant e he he0).eval p d z m = e m := by simp [eval, constant]

/-- Append the untouched grading factors of one chain-rule term. -/
def appendFactors (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (e : N07aJetBudgetExpression T K a) {k : ℕ} (order : Fin k → ℕ)
    (c : ℕ → ℝ) (hc : N07aSampleSubpower T K c) (hc0 : ∀ m, 0 ≤ c m) :
    N07aJetBudgetExpression T K (a + ∑ j, order j) where
  Index := e.Index
  finite := e.finite
  arity := fun i => e.arity i + k
  order := fun i => Fin.addCases (e.order i) order
  order_le i := by
    simpa only [Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]
      using Nat.add_le_add_right (e.order_le i) (∑ j, order j)
  coeff := fun i m => e.coeff i m * c m
  coeff_subpower i := N07aSampleSubpower.mul hD hT (e.coeff_subpower i) hc
  coeff_nonneg i m := mul_nonneg (e.coeff_nonneg i m) (hc0 m)

theorem eval_appendFactors {E : Type*} [AddCommGroup E] [Module ℝ E]
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (e : N07aJetBudgetExpression T K a) {k : ℕ} (order : Fin k → ℕ)
    (c : ℕ → ℝ) (hc : N07aSampleSubpower T K c) (hc0 : ∀ m, 0 ≤ c m)
    (p : ℕ → Seminorm ℝ E) (d : ℕ) (z : E) (m : ℕ) :
    (e.appendFactors hD hT order c hc hc0).eval p d z m =
      e.eval p d z m * (c m * ∏ j, (1 + p (order j + d) z)) := by
  letI := e.finite
  simp only [eval, appendFactors, Fin.prod_univ_add,
    Fin.addCases_left, Fin.addCases_right, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A finite sum uses the disjoint union of its monomial indices. -/
def sum {ι : Type} [Fintype ι] (e : ι → N07aJetBudgetExpression T K a) :
    N07aJetBudgetExpression T K a := by
  letI (i : ι) := (e i).finite
  exact {
    Index := Σ i, (e i).Index
    finite := inferInstance
    arity := fun i => (e i.1).arity i.2
    order := fun i => (e i.1).order i.2
    order_le := fun i => (e i.1).order_le i.2
    coeff := fun i => (e i.1).coeff i.2
    coeff_subpower := fun i => (e i.1).coeff_subpower i.2
    coeff_nonneg := fun i => (e i.1).coeff_nonneg i.2 }

theorem eval_sum {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type} [Fintype ι] (e : ι → N07aJetBudgetExpression T K a)
    (p : ℕ → Seminorm ℝ E) (d : ℕ) (z : E) (m : ℕ) :
    (sum e).eval p d z m = ∑ i, (e i).eval p d z m := by
  letI (i : ι) := (e i).finite
  simp only [eval, sum, Fintype.sum_sigma]

/-- One common low order and loss estimate every finite expression at
every budget. The number of monomials enters only the sampled envelope. -/
theorem oneHigh
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hIp : HasSmoothing p) (d : ℕ) :
    ∃ low loss : ℕ, ∀ (s : ℕ) (e : N07aJetBudgetExpression T K s),
      ∃ b : ℕ → ℝ, N07aSampleSubpower T K b ∧ (∀ m, 0 ≤ b m) ∧
        ∀ z, p low z ≤ 1 → ∀ m, e.eval p d z m ≤ b m * (1 + p (s + loss) z) := by
  obtain ⟨low, loss, hprod⟩ := n07a_finite_state_product p hp hIp d
  refine ⟨low, loss, fun s e => ?_⟩
  letI := e.finite
  choose C hC hCb using fun i => hprod (e.arity i) (e.order i) s (e.order_le i)
  let b : ℕ → ℝ := fun m => ∑ i, e.coeff i m * C i
  have hb : N07aSampleSubpower T K b :=
    N07aSampleSubpower.finset_sum hD hT Finset.univ
      (fun i m => e.coeff i m * C i)
      (fun i _ => N07aSampleSubpower.mul hD hT (e.coeff_subpower i)
        (N07aSampleSubpower.const hD hT (C i)))
  have hb0 (m : ℕ) : 0 ≤ b m :=
    Finset.sum_nonneg fun i _ => mul_nonneg (e.coeff_nonneg i m) (hC i)
  refine ⟨b, hb, hb0, fun z hz m => ?_⟩
  calc
    e.eval p d z m ≤ ∑ i, e.coeff i m * (C i * (1 + p (s + loss) z)) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hCb i z hz)
        (e.coeff_nonneg i m)
    _ = b m * (1 + p (s + loss) z) := by
      simp only [b, Finset.sum_mul, mul_assoc]

end N07aJetBudgetExpression

end ContinuousFlexibility.Analysis
