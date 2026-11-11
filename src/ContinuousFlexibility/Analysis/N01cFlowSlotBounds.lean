import ContinuousFlexibility.Analysis.N01cStateAngleSelections
import ContinuousFlexibility.Analysis.N01cFlowForcingExpansion
import ContinuousFlexibility.Analysis.N01cStateSeminorms

/-!
# Seminorms of the actual selected forcing slots

The state identity contributes only in singleton blocks. Thus every
selected state direction is either an original direction or zero.
The one-high expression on their unit ball is bounded by a single
aggregate of the original directions. Finite parameter prefixes are
chosen without changing the base.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open ContinuousFlexibility.Statements
open scoped BigOperators

section PrefixConstants

/-- Uniformize finitely many parameter orders while keeping the spatial
order outside the choice of the additive loss. -/
theorem n01c_finiteOrderPrefix
    (P : ℕ → ℕ → ℕ → ℝ → Prop) (loss : ℕ)
    (hmono : ∀ (k s h h' : ℕ) (B B' : ℝ), h ≤ h' → 0 < B → B ≤ B' →
      P k s h B → P k s h' B')
    (hP : ∀ k : ℕ, ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ P k s (s + loss + d) B) :
    ∀ K : ℕ, ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ k : ℕ, k ≤ K → P k (s + K) (s + loss + d) B := by
  classical
  choose d hd using hP
  intro K
  let dK : ℕ := K + ∑ i : Fin (K + 1), d i
  refine ⟨dK, fun s => ?_⟩
  choose c hc hcb using (fun i : Fin (K + 1) => hd i (s + K))
  let B : ℝ := 1 + ∑ i : Fin (K + 1), c i
  have hsum : 0 ≤ ∑ i : Fin (K + 1), c i :=
    Finset.sum_nonneg (fun i _ => (hc i).le)
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B, hB, fun k hk => ?_⟩
  let i : Fin (K + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
  have hdi : d i ≤ ∑ j : Fin (K + 1), d j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)
  have hci : c i ≤ B :=
    (Finset.single_le_sum (fun j _ => (hc j).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))
  exact hmono k (s + K) ((s + K) + loss + d i) (s + loss + dK)
    (c i) B (by dsimp only [dK]; omega) (hc i) hci (hcb i)

end PrefixConstants

section ScalarSlots

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- The parameter identity jet has no new direction at any other order. -/
theorem seminorm_flowParameterIdentityJet_fst_le
    (p : Seminorm ℝ F) (L : E →ₗ[ℝ] F) {n : ℕ} (v : Fin n → E)
    {M : ℝ} (hM : 0 ≤ M) (hv : ∀ i, p (L (v i)) ≤ M) :
    p (L ((flowParameterIdentityJet n v).1)) ≤ M := by
  cases n with
  | zero => simpa only [flowParameterIdentityJet, ContinuousMultilinearMap.zero_apply, Prod.fst_zero, map_zero] using hM
  | succ n =>
      cases n with
      | zero => exact hv 0
      | succ n =>
          simpa only [flowParameterIdentityJet, ContinuousMultilinearMap.zero_apply, Prod.fst_zero, map_zero] using hM

end ScalarSlots

section SelectedSlots

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- The Boolean word associated with an actual forcing choice. -/
def FlowForcingChoice.stateWord {N : ℕ} (ω : FlowForcingChoice N) :
    StateAngleWord ω.1.length :=
  StateAngleWord.ofBool (fun i => decide (i ∈ ω.2))

/-- Actual selected state directions after a finite affine pullback. -/
def flowForcingStateDirections {N : ℕ} (ω : FlowForcingChoice N)
    (L : E →L[ℝ] F) (v : Fin N → E) : Fin ω.stateWord.stateArity → F :=
  ω.stateWord.stateDirections
    (fun i => if decide (i ∈ ω.2) then
      (L ((flowParameterIdentityJet (ω.1.partSize i) (v ∘ ω.1.emb i)).1), 0)
      else (0, 1))

theorem flowForcingStateDirections_seminorm_le {N : ℕ}
    (ω : FlowForcingChoice N) (L : E →L[ℝ] F) (v : Fin N → E)
    (p : Seminorm ℝ F) {M : ℝ} (hM : 0 ≤ M)
    (hv : ∀ i, p (L (v i)) ≤ M) :
    ∀ i, p (flowForcingStateDirections ω L v i) ≤ M := by
  intro i
  obtain ⟨j, hj, he⟩ := ω.stateWord.stateDirections_mem_range
    (fun j => if decide (j ∈ ω.2) then
      (L ((flowParameterIdentityJet (ω.1.partSize j) (v ∘ ω.1.emb j)).1), 0)
      else (0, 1)) i
  have hselected : decide (j ∈ ω.2) = true := by
    simpa only [FlowForcingChoice.stateWord, StateAngleWord.isState_ofBool] using hj
  change p (ω.stateWord.stateDirections _ i) ≤ M
  rw [he]
  simp only [hselected, if_true, Prod.fst_mk]
  exact seminorm_flowParameterIdentityJet_fst_le p L.toLinearMap (v ∘ ω.1.emb j)
    hM (fun k => hv (ω.1.emb j k))

theorem flowForcingStateDirections_stateArity_le {N : ℕ} (ω : FlowForcingChoice N) :
    ω.stateWord.stateArity ≤ N := by
  have hsum := ω.stateWord.arity_sum
  have hlen := ω.1.length_le
  omega

end SelectedSlots

section UnitBall

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem oneHighVariationWeight_le_unitAggregate
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (x : E) {k : ℕ} (v : Fin k → E)
    (hv : ∀ i, p base (v i) ≤ 1) :
    oneHighVariationWeight p base high x v ≤
      (1 + p high x) + ∑ i, p high (v i) := by
  unfold oneHighVariationWeight
  apply add_le_add
  · apply mul_le_of_le_one_right (by positivity)
    exact Finset.prod_le_one (fun i _ => apply_nonneg _ _) (fun i _ => hv i)
  · apply Finset.sum_le_sum
    intro i _
    apply mul_le_of_le_one_right (apply_nonneg _ _)
    exact Finset.prod_le_one (fun j _ => apply_nonneg _ _) (fun j _ => hv j)

/-- Repeated selection is harmless: its finite multiplicity is a scalar
constant and does not consume additional spatial derivative orders. -/
theorem oneHighVariationWeight_le_selectedAggregate
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (x : E)
    {k n : ℕ} (v : Fin k → E) (u : Fin n → E)
    (hv : ∀ i, p base (v i) ≤ 1)
    (hhigh : ∀ i, p high (v i) ≤ ∑ j, p high (u j)) :
    oneHighVariationWeight p base high x v ≤
      ((k : ℝ) + 1) * ((1 + p high x) + ∑ j, p high (u j)) := by
  have hsum : ∑ i, p high (v i) ≤ (k : ℝ) * ∑ j, p high (u j) := by
    calc
      _ ≤ ∑ _i : Fin k, ∑ j, p high (u j) := Finset.sum_le_sum (fun i _ => hhigh i)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply (oneHighVariationWeight_le_unitAggregate p base high x v hv).trans
  have hx : 0 ≤ p high x := apply_nonneg _ _
  have hu : 0 ≤ ∑ j, p high (u j) := Finset.sum_nonneg (fun j _ => apply_nonneg _ _)
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  nlinarith

end UnitBall

end ContinuousFlexibility.Analysis
