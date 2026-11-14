module

public import ContinuousFlexibility.Analysis.N01cVolterraStateJets
public import Mathlib.Order.Preorder.Finite

/-!
# Isolating the genuine highest variation in the flow composition

A nontrivial ordered partition has only strictly smaller blocks. The
unique single-block partition therefore contains the sole highest
variation, and it occurs linearly through the first angular speed jet.
All other terms are exactly the previously defined lower-order forcing.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open scoped BigOperators

namespace OrderedFinpartition

def singleBlock (n : ℕ) (hn : 0 < n) : _root_.OrderedFinpartition n where
  length := 1
  partSize _ := n
  partSize_pos _ := hn
  emb _ := id
  emb_strictMono _ := strictMono_id
  parts_strictMono := Subsingleton.strictMono _
  disjoint i _ j _ hij := False.elim (hij (Subsingleton.elim _ _))
  cover x := ⟨0, x, rfl⟩

theorem sum_partSize {n : ℕ} (c : _root_.OrderedFinpartition n) :
    ∑ i : Fin c.length, c.partSize i = n := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using Fintype.card_congr c.equivSigma

theorem eq_singleBlock_of_length_eq_one {n : ℕ}
    (c : _root_.OrderedFinpartition n) (hn : 0 < n) (hl : c.length = 1) :
    c = singleBlock n hn := by
  have hs := sum_partSize c
  rcases c with ⟨l, sizes, hp, emb, hm, ho, hd, hc⟩
  dsimp only at hl hs
  subst l
  have hs0 : sizes 0 = n := by simpa only [Fin.sum_univ_one] using hs
  have heq : sizes = fun _ : Fin 1 => n := by
    funext i
    simpa only [show i = 0 from Subsingleton.elim _ _] using hs0
  subst sizes
  have hemb : emb = fun (_ : Fin 1) (j : Fin n) => j := by
    funext i
    exact (hm i).eq_id
  subst emb
  rfl

/-- Every block outside the one-block partition has strictly smaller size. -/
theorem partSize_lt_of_ne_singleBlock {n : ℕ}
    (c : _root_.OrderedFinpartition n) (hn : 0 < n)
    (hc : c ≠ singleBlock n hn) (i : Fin c.length) :
    c.partSize i < n := by
  classical
  by_contra hlt
  have hsize : c.partSize i = n := le_antisymm (c.partSize_le i) (Nat.le_of_not_gt hlt)
  have hsum := sum_partSize c
  have herase : ∑ j ∈ Finset.univ.erase i, c.partSize j = 0 := by
    have he := Finset.sum_erase_add Finset.univ c.partSize (Finset.mem_univ i)
    omega
  have hall (j : Fin c.length) : j = i := by
    by_contra hji
    have hb : c.partSize j ≤ ∑ k ∈ Finset.univ.erase i, c.partSize k :=
      Finset.single_le_sum (fun k _ => Nat.zero_le _) (Finset.mem_erase.mpr
        ⟨hji, Finset.mem_univ j⟩)
    have hp := c.partSize_pos j
    omega
  have hcard : Fintype.card (Fin c.length) ≤ 1 :=
    Fintype.card_le_one_iff.mpr (fun j k => (hall j).trans (hall k).symm)
  have hlength : c.length = 1 := by
    simp only [Fintype.card_fin] at hcard
    have hpos := c.length_pos hn
    omega
  exact hc (eq_singleBlock_of_length_eq_one c hn hlength)

end OrderedFinpartition

section HighestTerm

variable {E Y : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]

/-- Changing only the highest input jet changes the ordered-partition
composition only through the first outer differential. -/
theorem orderedPartition_sum_highest_difference {n : ℕ} (hn : 0 < n)
    (O : ∀ k : ℕ, Y [×k]→L[ℝ] ℝ)
    (A B : ∀ k : ℕ, E [×k]→L[ℝ] Y)
    (hAB : ∀ k, k < n → A k = B k) (v : Fin n → E) :
    (∑ c : _root_.OrderedFinpartition n,
      O c.length (fun i => A (c.partSize i) (v ∘ c.emb i))) -
      (∑ c : _root_.OrderedFinpartition n,
        O c.length (fun i => B (c.partSize i) (v ∘ c.emb i))) =
      O 1 (fun _ : Fin 1 => A n v - B n v) := by
  classical
  let c₀ := OrderedFinpartition.singleBlock n hn
  rw [← Finset.sum_sub_distrib]
  have hs : (∑ c : _root_.OrderedFinpartition n,
      (O c.length (fun i => A (c.partSize i) (v ∘ c.emb i)) -
        O c.length (fun i => B (c.partSize i) (v ∘ c.emb i)))) =
      O c₀.length (fun i => A (c₀.partSize i) (v ∘ c₀.emb i)) -
        O c₀.length (fun i => B (c₀.partSize i) (v ∘ c₀.emb i)) := by
    apply Finset.sum_eq_single c₀
    · intro c _ hc
      apply sub_eq_zero.mpr
      congr 1
      funext i
      rw [hAB _ (OrderedFinpartition.partSize_lt_of_ne_singleBlock c hn hc i)]
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  rw [hs]
  change O 1 (fun _ : Fin 1 => A n v) - O 1 (fun _ : Fin 1 => B n v) = _
  let L : Y →L[ℝ] ℝ :=
    (ContinuousMultilinearMap.ofSubsingleton ℝ Y ℝ (0 : Fin 1)).symm (O 1)
  exact (map_sub L (A n v) (B n v)).symm

end HighestTerm

section Flow

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The exact top-order term is the actual first angular speed
differential times the current variation. Everything else depends on
strictly lower variations. -/
theorem flowJetComposition_eq_linear_add_truncated
    {U : Set E} {G : E × PolarPoint → ℝ}
    (J : ContinuousTimeSpeedTower U G) (Θ : E × ℝ → ℝ)
    (B : ∀ k : ℕ, ContinuousStateVariation U k)
    {n : ℕ} (hn : 0 < n) (p : E × ℝ) (v : Fin n → E) :
    (∑ c : _root_.OrderedFinpartition n,
      J.D c.length (flowTrajectoryGraph Θ p)
        (fun i => flowGraphVariationSlot (c.partSize i) ((B (c.partSize i)).value p)
          (v ∘ c.emb i))) =
      speedAlongFlowAngularJet J Θ p * (B n).value p v +
        truncatedFlowForcing J Θ (fun k (_ : k < n) => B k) p v := by
  let A : ∀ k : ℕ, E [×k]→L[ℝ] (E × ℝ) :=
    fun k => flowGraphVariationSlot k ((B k).value p)
  let A₀ : ∀ k : ℕ, E [×k]→L[ℝ] (E × ℝ) := fun k =>
    flowGraphVariationSlot k
      ((lowerStateVariation (fun j (_ : j < n) => B j) k).value p)
  have he := orderedPartition_sum_highest_difference hn
    (fun k => J.D k (flowTrajectoryGraph Θ p)) A A₀
    (fun k hk => by
      dsimp only [A, A₀]
      rw [lowerStateVariation_of_lt _ hk]) v
  have hdiff : A n v - A₀ n v = (0, (B n).value p v) := by
    dsimp only [A, A₀]
    rw [lowerStateVariation_self]
    change (flowParameterIdentityJet n v + (0, (B n).value p v)) -
      (flowParameterIdentityJet n v + 0) = _
    simp only [add_zero, add_sub_cancel_left]
  have hlinear :
      J.D 1 (flowTrajectoryGraph Θ p) (fun _ : Fin 1 => (0, (B n).value p v)) =
        speedAlongFlowAngularJet J Θ p * (B n).value p v := by
    let L : (E × ℝ) →L[ℝ] ℝ :=
      (ContinuousMultilinearMap.ofSubsingleton ℝ (E × ℝ) ℝ (0 : Fin 1)).symm
        (J.D 1 (flowTrajectoryGraph Θ p))
    have hsmul := map_smul L ((B n).value p v) (0, 1)
    have hp : (B n).value p v • ((0 : E), (1 : ℝ)) = ((0 : E), (B n).value p v) := by simp
    rw [hp] at hsmul
    simpa only [L, ContinuousMultilinearMap.ofSubsingleton_symm_apply_apply,
      speedAlongFlowAngularJet, smul_eq_mul, mul_comm] using hsmul
  rw [hdiff, hlinear] at he
  rw [truncatedFlowForcing_apply]
  change _ - _ = _ at he
  linarith

end Flow

end ContinuousFlexibility.Analysis
