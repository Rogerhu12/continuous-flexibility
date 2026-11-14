module

public import ContinuousFlexibility.Analysis.N01cStateAngleIdentification
public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno

/-!
# Selecting and restricting actual state-angle slots

The Boolean word uses the original order of the slots. Restriction along
an ordered-partition embedding preserves those actual slots, and its
state and angle arities add exactly over the partition. No permutation
or symmetry premise is needed for the pure-slot identification.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Function
open scoped BigOperators

namespace StateAngleWord

/-- True records a state slot; false records a unit angle slot. -/
def isState : {n : ℕ} → StateAngleWord n → Fin n → Bool
  | _, .nil => Fin.elim0
  | _, .state w => Fin.cons true w.isState
  | _, .angle w => Fin.cons false w.isState

/-- Construct a word without changing the order of the selected slots. -/
def ofBool : {n : ℕ} → (Fin n → Bool) → StateAngleWord n
  | 0, _ => .nil
  | n + 1, b => if b 0 then .state (ofBool (Fin.tail b))
    else .angle (ofBool (Fin.tail b))

@[simp] theorem isState_ofBool {n : ℕ} (b : Fin n → Bool) :
    (ofBool b).isState = b := by
  induction n with
  | zero =>
      funext i
      exact i.elim0
  | succ n ih =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        cases hb : b 0 <;>
        simp only [ofBool, hb, Bool.false_eq_true, if_false, if_true, isState,
          Fin.cons_zero, Fin.cons_succ, ih, Fin.tail]

@[simp] theorem ofBool_isState {n : ℕ} (w : StateAngleWord n) :
    ofBool w.isState = w := by
  induction w with
  | nil => rfl
  | state w ih =>
      simpa only [isState, ofBool, Fin.cons_zero, if_true, Fin.tail_cons] using
        congrArg StateAngleWord.state ih
  | angle w ih =>
      simpa only [isState, ofBool, Fin.cons_zero, Bool.false_eq_true, if_false,
        Fin.tail_cons] using congrArg StateAngleWord.angle ih

/-- Restrict the word along the actual index map of a partition block. -/
def restrict {n k : ℕ} (w : StateAngleWord n) (e : Fin k → Fin n) :
    StateAngleWord k :=
  ofBool (w.isState ∘ e)

@[simp] theorem isState_restrict {n k : ℕ} (w : StateAngleWord n)
    (e : Fin k → Fin n) (i : Fin k) :
    (w.restrict e).isState i = w.isState (e i) := by
  simp only [restrict, isState_ofBool, comp_apply]

theorem stateArity_eq_sum {n : ℕ} (w : StateAngleWord n) :
    w.stateArity = ∑ i : Fin n, if w.isState i then 1 else 0 := by
  induction w with
  | nil => simp only [stateArity, Fin.sum_univ_zero]
  | state w ih =>
      simp only [stateArity, Fin.sum_univ_succ, isState, Fin.cons_zero, if_true,
        Fin.cons_succ, ← ih]
      omega
  | angle w ih =>
      simp only [stateArity, Fin.sum_univ_succ, isState, Fin.cons_zero,
        Bool.false_eq_true, if_false, Fin.cons_succ, zero_add, ← ih]

theorem angleArity_eq_sum {n : ℕ} (w : StateAngleWord n) :
    w.angleArity = ∑ i : Fin n, if w.isState i then 0 else 1 := by
  induction w with
  | nil => simp only [angleArity, Fin.sum_univ_zero]
  | state w ih =>
      simp only [angleArity, Fin.sum_univ_succ, isState, Fin.cons_zero, if_true,
        Fin.cons_succ, zero_add, ← ih]
  | angle w ih =>
      simp only [angleArity, Fin.sum_univ_succ, isState, Fin.cons_zero,
        Bool.false_eq_true, if_false, Fin.cons_succ, ← ih]
      omega

/-- Exact parameter-order budget over the actual partition blocks. -/
theorem sum_restrict_stateArity {n : ℕ} (w : StateAngleWord n)
    (c : _root_.OrderedFinpartition n) :
    (∑ i : Fin c.length, (w.restrict (c.emb i)).stateArity) = w.stateArity := by
  simp_rw [stateArity_eq_sum, isState_restrict]
  exact c.sum_sigma_eq_sum (fun i => if w.isState i then (1 : ℕ) else 0)

/-- Exact angular-order budget over the same partition blocks. -/
theorem sum_restrict_angleArity {n : ℕ} (w : StateAngleWord n)
    (c : _root_.OrderedFinpartition n) :
    (∑ i : Fin c.length, (w.restrict (c.emb i)).angleArity) = w.angleArity := by
  simp_rw [angleArity_eq_sum, isState_restrict]
  exact c.sum_sigma_eq_sum (fun i => if w.isState i then (0 : ℕ) else 1)

section PureSlots

variable {E : Type*} [Zero E]

/-- The actual tuple has zero angle component in each state slot and
the unit angle direction in each angle slot. -/
def IsPure {n : ℕ} (w : StateAngleWord n) (v : Fin n → E × ℝ) : Prop :=
  (∀ i, w.isState i = true → (v i).2 = 0) ∧
    ∀ i, w.isState i = false → v i = (0, 1)

theorem isPure_pureSlots {n : ℕ} (w : StateAngleWord n)
    (v : Fin w.stateArity → E) : w.IsPure (w.pureSlots v) := by
  induction w with
  | nil =>
      constructor <;> intro i <;> exact i.elim0
  | state w ih =>
      rcases ih (Fin.tail v) with ⟨hs, ha⟩
      constructor
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · intro _
          rfl
        · exact hs j
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [isState, Fin.cons_zero, Bool.true_eq_false, false_implies]
        · exact ha j
  | angle w ih =>
      rcases ih v with ⟨hs, ha⟩
      constructor
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [isState, Fin.cons_zero, Bool.false_eq_true, false_implies]
        · exact hs j
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · intro _
          rfl
        · exact ha j

theorem pureSlots_stateDirections {n : ℕ} (w : StateAngleWord n)
    (v : Fin n → E × ℝ) (hv : w.IsPure v) :
    w.pureSlots (w.stateDirections v) = v := by
  induction w with
  | nil =>
      funext i
      exact i.elim0
  | state w ih =>
      have ht : w.IsPure (Fin.tail v) :=
        ⟨fun i hi => hv.1 i.succ hi, fun i hi => hv.2 i.succ hi⟩
      have he := ih (Fin.tail v) ht
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · apply Prod.ext
        · rfl
        · exact (hv.1 0 rfl).symm
      · exact congrFun he j
  | angle w ih =>
      have ht : w.IsPure (Fin.tail v) :=
        ⟨fun i hi => hv.1 i.succ hi, fun i hi => hv.2 i.succ hi⟩
      have he := ih (Fin.tail v) ht
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (hv.2 0 rfl).symm
      · exact congrFun he j

theorem angleFactor_eq_one {n : ℕ} (w : StateAngleWord n)
    (v : Fin n → E × ℝ) (hv : w.IsPure v) : w.angleFactor v = 1 := by
  induction w with
  | nil => rfl
  | state w ih =>
      exact ih (Fin.tail v)
        ⟨fun i hi => hv.1 i.succ hi, fun i hi => hv.2 i.succ hi⟩
  | angle w ih =>
      change (v 0).2 * w.angleFactor (Fin.tail v) = 1
      rw [hv.2 0 rfl, ih (Fin.tail v)
        ⟨fun i hi => hv.1 i.succ hi, fun i hi => hv.2 i.succ hi⟩]
      exact one_mul 1

theorem IsPure.restrict {n k : ℕ} {w : StateAngleWord n}
    {v : Fin n → E × ℝ} (hv : w.IsPure v) (e : Fin k → Fin n) :
    (w.restrict e).IsPure (v ∘ e) := by
  constructor
  · intro i hi
    exact hv.1 (e i) (by simpa only [isState_restrict] using hi)
  · intro i hi
    exact hv.2 (e i) (by simpa only [isState_restrict] using hi)

/-- A partition block recovers the original pure slots in their actual
embedding order. Its state directions are the corresponding subsequence. -/
theorem restrict_pureSlots {n k : ℕ} (w : StateAngleWord n)
    (e : Fin k → Fin n) (v : Fin w.stateArity → E) :
    (w.restrict e).pureSlots
        ((w.restrict e).stateDirections (w.pureSlots v ∘ e)) = w.pureSlots v ∘ e :=
  (w.restrict e).pureSlots_stateDirections _ ((w.isPure_pureSlots v).restrict e)

/-- The Boolean selection used in the actual forcing expansion. -/
theorem ofBool_isPure {n : ℕ} (b : Fin n → Bool) (v : Fin n → E) :
    (ofBool b).IsPure (fun i => if b i then (v i, 0) else (0, 1)) := by
  constructor
  · intro i hi
    have hb : b i = true := by simpa only [isState_ofBool] using hi
    simp only [hb, if_true]
  · intro i hi
    have hb : b i = false := by simpa only [isState_ofBool] using hi
    simp only [hb, Bool.false_eq_true, if_false]

/-- Every extracted state direction is an original state-slot value. -/
theorem stateDirections_mem_range {n : ℕ} (w : StateAngleWord n)
    (v : Fin n → E × ℝ) (i : Fin w.stateArity) :
    ∃ j : Fin n, w.isState j = true ∧ w.stateDirections v i = (v j).1 := by
  induction w with
  | nil => exact i.elim0
  | state w ih =>
      refine Fin.cases ?_ (fun k => ?_) i
      · exact ⟨0, rfl, rfl⟩
      · rcases ih (Fin.tail v) k with ⟨j, hj, he⟩
        exact ⟨j.succ, hj, he⟩
  | angle w ih =>
      rcases ih (Fin.tail v) i with ⟨j, hj, he⟩
      exact ⟨j.succ, hj, he⟩

end PureSlots

end StateAngleWord

section GenuineJets

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Apply the genuine mixed-slot identity directly to a Boolean choice. -/
theorem smoothDirections_joint_selectedSlots
    {U : Set E} {g : E × ℝ → ℝ}
    (J : Statements.SmoothDirections (U ×ˢ (Set.univ : Set ℝ)) g)
    (Ja : ∀ b : ℕ, ∀ θ : ℝ, Statements.SmoothDirections U
      (fun x => iteratedDeriv b (fun η => g (x, η)) θ))
    {n : ℕ} (b : Fin n → Bool) {x : E} (hx : x ∈ U)
    (θ : ℝ) (v : Fin n → E) :
    J.D n (x, θ) (fun i => if b i then (v i, 0) else (0, 1)) =
      (Ja (StateAngleWord.ofBool b).angleArity θ).D (StateAngleWord.ofBool b).stateArity x
          ((StateAngleWord.ofBool b).stateDirections
            (fun i => if b i then (v i, 0) else (0, 1))) := by
  have he := (StateAngleWord.ofBool b).pureSlots_stateDirections _
    (StateAngleWord.ofBool_isPure b v)
  exact (congrArg (fun u : Fin n → E × ℝ => J.D n (x, θ) u) he.symm).trans
    (smoothDirections_joint_pureSlots J Ja (StateAngleWord.ofBool b) hx θ _)

/-- Further angular differentiation preserves the original order of all
state slots and adds only to the angular arity. -/
theorem iteratedDeriv_stateJet_angle_shift
    {U : Set E} {f : E × PolarPoint → ℝ}
    (hU : IsOpen U) (hf : IsFiniteAffineTimeSmooth U f)
    (J : ∀ b : ℕ, ∀ q : PolarPoint, Statements.SmoothDirections U
      (fun x => iteratedDeriv b (fun η => f (x, (q.1, η))) q.2))
    (a b k : ℕ) {x : E} (hx : x ∈ U) (t θ : ℝ) (v : Fin k → E) :
    iteratedDeriv a (fun η => (J b (t, η)).D k x v) θ =
      (J (b + a) (t, θ)).D k x v := by
  induction a generalizing θ with
  | zero => rfl
  | succ a ih =>
      have he : iteratedDeriv a (fun η => (J b (t, η)).D k x v) =
          fun η => (J (b + a) (t, η)).D k x v := funext ih
      rw [iteratedDeriv_succ, he]
      exact (deriv_stateJet_angle hU hf J k (b + a) x hx t θ v).trans
        (congrArg (fun j : ℕ => (J j (t, θ)).D k x v) (Nat.add_assoc b a 1))

/-- The actual angular derivative of an arbitrarily interleaved
state/angle jet is the corresponding actual angular-state jet. -/
theorem iteratedDeriv_joint_selectedSlots
    {U : Set E} {g : E × ℝ → ℝ}
    (J : Statements.SmoothDirections (U ×ˢ (Set.univ : Set ℝ)) g)
    (Ja : ∀ b : ℕ, ∀ θ : ℝ, Statements.SmoothDirections U
      (fun x => iteratedDeriv b (fun η => g (x, η)) θ))
    {n : ℕ} (b : Fin n → Bool) (a : ℕ) {x : E} (hx : x ∈ U)
    (θ : ℝ) (v : Fin n → E) :
    iteratedDeriv a
        (fun η => J.D n (x, η) (fun i => if b i then (v i, 0) else (0, 1))) θ =
      (Ja ((StateAngleWord.ofBool b).angleArity + a) θ).D (StateAngleWord.ofBool b).stateArity x
          ((StateAngleWord.ofBool b).stateDirections
            (fun i => if b i then (v i, 0) else (0, 1))) := by
  have he : (fun η => J.D n (x, η) (fun i => if b i then (v i, 0) else (0, 1))) =
      fun η => (Ja (StateAngleWord.ofBool b).angleArity η).D (StateAngleWord.ofBool b).stateArity x
          ((StateAngleWord.ofBool b).stateDirections
            (fun i => if b i then (v i, 0) else (0, 1))) :=
    funext (fun η => smoothDirections_joint_selectedSlots J Ja b hx η v)
  rw [he]
  exact iteratedDeriv_stateJet_angle_shift (Ja 0 0).open_domain
    (isFiniteAffineTimeSmooth_of_jointSmoothDirections J)
    (fun b q => Ja b q.2) a (StateAngleWord.ofBool b).angleArity
    (StateAngleWord.ofBool b).stateArity hx (0 : ℝ) θ _

end GenuineJets

end ContinuousFlexibility.Analysis
