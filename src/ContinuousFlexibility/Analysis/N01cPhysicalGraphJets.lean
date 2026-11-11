import ContinuousFlexibility.Analysis.N01cPhysicalFlowGraph
import ContinuousFlexibility.Analysis.N01cStateAngleGraphBudget

/-!
# Actual ordered-partition words of the state-flow graph

Every block keeps the original order of its state and angular slots.
The state projection is the identity at order one and zero at higher
orders. Its size is therefore controlled by the original directions,
while its angular component is the actual angular-state flow jet.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

namespace StateAngleWord

def angleBlock : (b : ℕ) → StateAngleWord b
  | 0 => .nil
  | b + 1 => .angle (angleBlock b)

def prependStates {n : ℕ} (w : StateAngleWord n) : (k : ℕ) → StateAngleWord (n + k)
  | 0 => w
  | k + 1 => .state (w.prependStates k)

def stateThenAngle (k b : ℕ) : StateAngleWord (b + k) :=
  (angleBlock b).prependStates k

@[simp] theorem angleBlock_stateArity (b : ℕ) : (angleBlock b).stateArity = 0 := by
  induction b with
  | zero => rfl
  | succ b ih => exact ih

@[simp] theorem angleBlock_angleArity (b : ℕ) : (angleBlock b).angleArity = b := by
  induction b with
  | zero => rfl
  | succ b ih => simpa only [angleBlock, angleArity, ih]

@[simp] theorem prependStates_stateArity {n : ℕ} (w : StateAngleWord n) (k : ℕ) :
    (w.prependStates k).stateArity = w.stateArity + k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [prependStates, stateArity, ih, Nat.add_assoc]

@[simp] theorem prependStates_angleArity {n : ℕ} (w : StateAngleWord n) (k : ℕ) :
    (w.prependStates k).angleArity = w.angleArity := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

@[simp] theorem stateThenAngle_stateArity (k b : ℕ) :
    (stateThenAngle k b).stateArity = k := by
  simp only [stateThenAngle, prependStates_stateArity, angleBlock_stateArity, Nat.zero_add]

@[simp] theorem stateThenAngle_angleArity (k b : ℕ) :
    (stateThenAngle k b).angleArity = b := by
  simp only [stateThenAngle, prependStates_angleArity, angleBlock_angleArity]

theorem pureSlots_fst_seminorm_le
    {X : Type*} [AddCommGroup X] [Module ℝ X] {n : ℕ}
    (w : StateAngleWord n) (p : Seminorm ℝ X) {B : ℝ} (hB : 0 ≤ B)
    (v : Fin w.stateArity → X) (hv : ∀ i, p (v i) ≤ B) :
    ∀ i, p ((w.pureSlots v i).1) ≤ B := by
  induction w generalizing v with
  | nil => intro i; exact i.elim0
  | state w ih =>
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hv 0
      · exact ih (Fin.tail v) (fun j => hv j.succ) j
  | angle w ih =>
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [pureSlots, Fin.cons_zero, map_zero] using hB
      · exact ih v hv j

end StateAngleWord

section GenuineGraph

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {U : Set X} {Θ : X × ℝ → ℝ}

/-- A block of the genuine graph derivative, evaluated in the original
partition-embedding order. -/
def stateFlowPartitionSlot
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) Θ)
    {n : ℕ} (input : StateAngleWord n) (c : OrderedFinpartition n)
    (q : X × ℝ) (v : Fin input.stateArity → X) (i : Fin c.length) : X × ℝ :=
  (smoothDirections_stateFlowGraph J).D (c.partSize i) q
    (input.pureSlots v ∘ c.emb i)

theorem smoothDirections_stateFlowGraph_fst_seminorm_le
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) Θ)
    {n : ℕ} (hn : 0 < n) (q : X × ℝ) (p : Seminorm ℝ X)
    {B : ℝ} (hB : 0 ≤ B) (v : Fin n → X × ℝ)
    (hv : ∀ i, p (v i).1 ≤ B) :
    p (((smoothDirections_stateFlowGraph J).D n q v).1) ≤ B := by
  cases n with
  | zero => omega
  | succ n =>
      cases n with
      | zero =>
          rw [smoothDirections_stateFlowGraph_D_one]
          exact hv 0
      | succ n =>
          rw [smoothDirections_stateFlowGraph_D_succ_succ]
          simpa only [map_zero] using hB

theorem stateFlowPartitionSlot_fst_seminorm_le
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) Θ)
    {n : ℕ} (input : StateAngleWord n) (c : OrderedFinpartition n)
    (q : X × ℝ) (v : Fin input.stateArity → X)
    (p : Seminorm ℝ X) {B : ℝ} (hB : 0 ≤ B) (hv : ∀ i, p (v i) ≤ B)
    (i : Fin c.length) :
    p (stateFlowPartitionSlot J input c q v i).1 ≤ B :=
  smoothDirections_stateFlowGraph_fst_seminorm_le J (c.partSize_pos i) q p hB
    (input.pureSlots v ∘ c.emb i)
    (fun j => input.pureSlots_fst_seminorm_le p hB v hv (c.emb i j))

/-- The angular coordinate is the actual flow jet with exactly the
restricted block's state and angle orders. -/
theorem stateFlowPartitionSlot_snd
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) Θ)
    (Ja : ∀ b : ℕ, ∀ θ : ℝ, SmoothDirections U
      (fun x => iteratedDeriv b (fun η => Θ (x, η)) θ))
    {n : ℕ} (input : StateAngleWord n) (c : OrderedFinpartition n)
    {x : X} (hx : x ∈ U) (θ : ℝ) (v : Fin input.stateArity → X)
    (i : Fin c.length) :
    (stateFlowPartitionSlot J input c (x, θ) v i).2 =
      (Ja (input.restrict (c.emb i)).angleArity θ).D (input.restrict (c.emb i)).stateArity x
          ((input.restrict (c.emb i)).stateDirections (input.pureSlots v ∘ c.emb i)) := by
  rw [stateFlowPartitionSlot, smoothDirections_stateFlowGraph_D_apply]
  change J.D (c.partSize i) (x, θ) (input.pureSlots v ∘ c.emb i) = _
  calc
    _ = J.D (c.partSize i) (x, θ)
        ((input.restrict (c.emb i)).pureSlots
          ((input.restrict (c.emb i)).stateDirections (input.pureSlots v ∘ c.emb i))) :=
      congrArg (fun u : Fin (c.partSize i) → X × ℝ => J.D (c.partSize i) (x, θ) u)
        (input.restrict_pureSlots (c.emb i) v).symm
    _ = _ := smoothDirections_joint_pureSlots J Ja (input.restrict (c.emb i)) hx θ _

variable [LocallyConvexSpace ℝ X]

/-- The actual chain formula is a finite sum over partitions and then
over the outer state-angle choices. The outer angle value is unrestricted. -/
theorem stateFlow_composition_D_pureSlots
    {f : X × ℝ → ℝ}
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) Θ)
    (K : SmoothDirections (U ×ˢ (univ : Set ℝ)) f)
    (Ka : ∀ b : ℕ, ∀ θ : ℝ, SmoothDirections U
      (fun x => iteratedDeriv b (fun η => f (x, η)) θ))
    {n : ℕ} (input : StateAngleWord n) {x : X} (hx : x ∈ U)
    (θ : ℝ) (v : Fin input.stateArity → X) :
    (smoothDirections_realCompTVS (smoothDirections_stateFlowGraph J) K
      (fun q hq => ⟨hq.1, mem_univ _⟩)).D n (x, θ) (input.pureSlots v) =
      ∑ c : OrderedFinpartition n, ∑ output : StateAngleWord c.length,
        (Ka output.angleArity (Θ (x, θ))).D output.stateArity x
          (output.stateDirections (stateFlowPartitionSlot J input c (x, θ) v)) *
            output.angleFactor (stateFlowPartitionSlot J input c (x, θ) v) := by
  rw [smoothDirections_realCompTVS_D_apply]
  apply Finset.sum_congr rfl
  intro c _
  have hh := smoothDirections_joint_D_eq_stateAngleJet K Ka c.length x hx
    (Θ (x, θ)) (stateFlowPartitionSlot J input c (x, θ) v)
  simpa only [stateAngleJet_apply, stateFlowPartitionSlot] using hh

end GenuineGraph

end ContinuousFlexibility.Analysis
