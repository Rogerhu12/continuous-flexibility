module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsMixedBlocks
public import ContinuousFlexibility.Analysis.N04PositiveGeometryInversePartitionBudget

/-!
# One weighted term of the actual parameterized inverse recurrence

Only original state singletons pass through the identity coordinate.
All remaining genuine inverse blocks save one spatial order. The exact
partition budget therefore preserves both the spatial coefficient one
and a single positive-parameter height factor.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open scoped ContDiff BigOperators

theorem n04PositiveGeometry_selectedWord_stateArity {n : ℕ} (s : Finset (Fin n)) :
    (StateAngleWord.ofBool (fun i => decide (i ∈ s))).stateArity = s.card := by
  classical
  rw [StateAngleWord.stateArity_eq_sum]
  simp only [StateAngleWord.isState_ofBool, decide_eq_true_eq]
  calc
    _ = ∑ i ∈ s, if i ∈ s then (1 : ℕ) else 0 :=
      (Finset.sum_subset (Finset.subset_univ s)
        (fun i _ hi => if_neg hi)).symm
    _ = s.card := by simp

theorem n04PositiveGeometry_selectedWord_angleArity {n : ℕ} (s : Finset (Fin n)) :
    (StateAngleWord.ofBool (fun i => decide (i ∈ s))).angleArity =
      (Finset.univ \ s).card := by
  classical
  rw [StateAngleWord.angleArity_eq_sum]
  simp only [StateAngleWord.isState_ofBool, decide_eq_true_eq]
  have houtside (i : Fin n) (_hi : i ∈ Finset.univ)
      (hnot : i ∉ Finset.univ \ s) : (if i ∈ s then (0 : ℕ) else 1) = 0 := by
    have hi : i ∈ s := by
      by_contra hs
      exact hnot (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hs⟩)
    exact if_pos hi
  calc
    _ = ∑ i ∈ Finset.univ \ s, if i ∈ s then (0 : ℕ) else 1 :=
      (Finset.sum_subset (Finset.sdiff_subset) houtside).symm
    _ = ∑ _i ∈ Finset.univ \ s, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact if_neg (Finset.mem_sdiff.mp hi).2
    _ = _ := by simp

private theorem inverse_prod_selected_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) :
    (∏ i, if i ∈ s then 1 else f i) = ∏ i ∈ Finset.univ \ s, f i := by
  symm
  calc
    _ = ∏ i ∈ Finset.univ \ s, if i ∈ s then 1 else f i := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (if_neg (Finset.mem_sdiff.mp hi).2).symm
    _ = ∏ i, if i ∈ s then 1 else f i := by
      apply Finset.prod_subset Finset.sdiff_subset
      intro i _ hnot
      have hi : i ∈ s := by
        by_contra hs
        exact hnot (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hs⟩)
      exact if_pos hi

variable {P V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- This is one actual term in the inverse recurrence, before any
seminorm normalization. Its spatial exponent is the original total
weighted order minus one, independently of the number of blocks. -/
theorem n04PositiveGeometry_inverseSelectedTerm_weighted_bound
    {f g : P × V → V} {x : P × V} (hg : ContDiffAt ℝ ∞ g x)
    {n : ℕ} (w : StateAngleWord n) (c : OrderedFinpartition n) (hc : 2 ≤ c.length)
    (s : Finset (Fin c.length))
    (hidentity : ∀ i ∈ s, (w.restrict (c.emb i)).stateArity = 1 ∧
      (w.restrict (c.emb i)).angleArity = 0)
    (C d : ℕ) (hC : 1 ≤ C)
    {M K H t : ℝ} (hM : 1 ≤ M) (hK : 1 ≤ K)
    (hH : 0 ≤ H) (hHM : H ≤ M) (ht : 1 ≤ t)
    (houter : ‖n04PositiveGeometry_projectedJet (fun i => decide (i ∈ s)) f
        (n04PositiveGeometry_fiberLift g x)‖ ≤
      M * parameterHeightWeight H s.card *
        t ^ ((Finset.univ \ s).card + C * s.card - 1))
    (hinner : ∀ i ∉ s,
      ‖n04PositiveGeometry_projectedJet (w.isState ∘ c.emb i) g x‖ ≤
        K * M ^ d * parameterHeightWeight H (w.restrict (c.emb i)).stateArity *
          t ^ ((w.restrict (c.emb i)).angleArity +
            C * (w.restrict (c.emb i)).stateArity - 1)) :
    ‖n04PositiveGeometry_inverseSelectedTerm w.isState f g x c s‖ ≤
      K ^ n * M ^ (d * n + n + 2) * parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + C * w.stateArity - 1) := by
  classical
  let κ : Fin c.length → ℕ := fun i => (w.restrict (c.emb i)).stateArity
  let β : Fin c.length → ℕ := fun i => (w.restrict (c.emb i)).angleArity
  let q : Finset (Fin c.length) := Finset.univ \ s
  let cost : Fin c.length → ℕ := fun i => β i + C * κ i - 1
  let Q : ℝ := K * M ^ d
  have hM₀ : 0 ≤ M := zero_le_one.trans hM
  have ht₀ : 0 ≤ t := zero_le_one.trans ht
  have hQ : 1 ≤ Q := by
    exact one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hM)
  have hQ₀ : 0 ≤ Q := zero_le_one.trans hQ
  have hpart (i : Fin c.length) (_hi : i ∈ Finset.univ) : 0 < κ i + β i := by
    rw [show κ i + β i = c.partSize i from (w.restrict (c.emb i)).arity_sum]
    exact c.partSize_pos i
  have hcost : (q.card + C * s.card - 1) + (∑ i ∈ q, cost i) =
      w.angleArity + C * w.stateArity - 1 := by
    have he := n04PositiveGeometry_inversePartition_cost Finset.univ s
      (Finset.subset_univ s) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ κ β C hC hpart hidentity
    simpa only [q, cost, κ, β, w.sum_restrict_stateArity c,
      w.sum_restrict_angleArity c] using he
  have hheight : parameterHeightWeight H s.card * (∏ i ∈ q, parameterHeightWeight H (κ i)) ≤
      M ^ (c.length + 1) * parameterHeightWeight H w.stateArity := by
    have hh := n04PositiveGeometry_inversePartition_height Finset.univ s
      (Finset.subset_univ s) κ (fun i hi => (hidentity i hi).1) hH hHM hM
    simpa only [q, κ, Finset.card_univ, Fintype.card_fin, w.sum_restrict_stateArity c] using hh
  have hqn : q.card ≤ n :=
    (Finset.card_le_card Finset.sdiff_subset).trans
      (by simpa only [Finset.card_univ, Fintype.card_fin] using c.length_le)
  have hprod : (∏ i, ‖n04PositiveGeometry_inverseSelectedBlock w.isState g x c s i‖) ≤
      Q ^ q.card * (∏ i ∈ q, parameterHeightWeight H (κ i)) * t ^ (∑ i ∈ q, cost i) := by
    calc
      _ ≤ ∏ i, if i ∈ s then 1 else Q * parameterHeightWeight H (κ i) * t ^ cost i := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro i _
        by_cases hi : i ∈ s
        · rw [if_pos hi]
          exact n04PositiveGeometry_inverseSelectedBlock_state_norm_le hg w.isState c s i hi
        · rw [if_neg hi]
          exact (n04PositiveGeometry_inverseSelectedBlock_space_norm_le hg w.isState c s i hi).trans
            (hinner i hi)
      _ = ∏ i ∈ q, Q * parameterHeightWeight H (κ i) * t ^ cost i :=
        inverse_prod_selected_one s _
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
        simp only [Finset.prod_const]
  have houter₀ : 0 ≤ M * parameterHeightWeight H s.card * t ^ (q.card + C * s.card - 1) :=
    mul_nonneg (mul_nonneg hM₀ (parameterHeightWeight_nonneg hH _)) (pow_nonneg ht₀ _)
  have hheight₀ : 0 ≤ parameterHeightWeight H w.stateArity := parameterHeightWeight_nonneg hH _
  have hpoly : M * Q ^ q.card * M ^ (c.length + 1) ≤ K ^ n * M ^ (d * n + n + 2) := by
    calc
      _ ≤ M * Q ^ n * M ^ (n + 1) := mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hQ hqn) hM₀)
        (pow_le_pow_right₀ hM (Nat.add_le_add_right c.length_le 1))
        (pow_nonneg hM₀ _) (mul_nonneg hM₀ (pow_nonneg hQ₀ _))
      _ = _ := by
        dsimp only [Q]
        rw [mul_pow, ← pow_mul,
          show d * n + n + 2 = (d * n + (n + 1)) + 1 by omega,
          pow_add, pow_add, pow_one]
        ring
  calc
    _ ≤ ‖n04PositiveGeometry_projectedJet (fun i => decide (i ∈ s)) f
        (n04PositiveGeometry_fiberLift g x)‖ *
        ∏ i, ‖n04PositiveGeometry_inverseSelectedBlock w.isState g x c s i‖ :=
      c.norm_compAlongOrderedFinpartition_le _ _
    _ ≤ (M * parameterHeightWeight H s.card * t ^ (q.card + C * s.card - 1)) *
        (Q ^ q.card * (∏ i ∈ q, parameterHeightWeight H (κ i)) * t ^ (∑ i ∈ q, cost i)) :=
      mul_le_mul houter hprod (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) houter₀
    _ = (M * Q ^ q.card) *
        (parameterHeightWeight H s.card * ∏ i ∈ q, parameterHeightWeight H (κ i)) *
          t ^ (w.angleArity + C * w.stateArity - 1) := by
      rw [← hcost, pow_add]
      ring
    _ ≤ (M * Q ^ q.card) *
        (M ^ (c.length + 1) * parameterHeightWeight H w.stateArity) *
          t ^ (w.angleArity + C * w.stateArity - 1) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hheight (mul_nonneg hM₀ (pow_nonneg hQ₀ _)))
        (pow_nonneg ht₀ _)
    _ = (M * Q ^ q.card * M ^ (c.length + 1)) *
        parameterHeightWeight H w.stateArity * t ^ (w.angleArity + C * w.stateArity - 1) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpoly hheight₀) (pow_nonneg ht₀ _)

end ContinuousFlexibility.Analysis
