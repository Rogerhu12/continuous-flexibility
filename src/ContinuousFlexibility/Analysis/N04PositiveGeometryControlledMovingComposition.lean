import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsMixedComposition
import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsMixedTerm

/-!
# A moving point with the original finite state budget

The exact composition formula discards every selected state block
except an original singleton. Thus the outer field is evaluated only
through the original state prefix. Each other block saves one spatial
order, which pays exactly for its outer spatial derivative.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open scoped ContDiff BigOperators

private theorem moving_prod_selected_one
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

variable {P V Z : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

private theorem movingSelectedTerm_bound
    {f : P × V → Z} {g : P × V → V} {x : P × V} (hg : ContDiffAt ℝ ∞ g x)
    {n : ℕ} (hn : 0 < n) (w : StateAngleWord n) (c : OrderedFinpartition n)
    (s : Finset (Fin c.length))
    (hidentity : ∀ i ∈ s, (w.restrict (c.emb i)).stateArity = 1 ∧
      (w.restrict (c.emb i)).angleArity = 0)
    (C : ℕ) (hC : 1 ≤ C) {M H t : ℝ}
    (hM : 1 ≤ M) (hH : 0 ≤ H) (hHM : H ≤ M) (ht : 1 ≤ t)
    (houter : ‖n04PositiveGeometry_projectedJet (fun i => decide (i ∈ s)) f
        (n04PositiveGeometry_fiberLift g x)‖ ≤
      M * parameterHeightWeight H s.card * t ^ ((Finset.univ \ s).card + C * s.card))
    (hinner : ∀ i ∉ s,
      ‖n04PositiveGeometry_projectedJet (w.isState ∘ c.emb i) g x‖ ≤
        M * parameterHeightWeight H (w.restrict (c.emb i)).stateArity *
          t ^ ((w.restrict (c.emb i)).angleArity +
            C * (w.restrict (c.emb i)).stateArity - 1)) :
    ‖n04PositiveGeometry_inverseSelectedTerm w.isState f g x c s‖ ≤
      M ^ (2 * n + 2) * parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + C * w.stateArity) := by
  classical
  let κ : Fin c.length → ℕ := fun i => (w.restrict (c.emb i)).stateArity
  let β : Fin c.length → ℕ := fun i => (w.restrict (c.emb i)).angleArity
  let q : Finset (Fin c.length) := Finset.univ \ s
  let cost : Fin c.length → ℕ := fun i => β i + C * κ i - 1
  have hM₀ : 0 ≤ M := zero_le_one.trans hM
  have ht₀ : 0 ≤ t := zero_le_one.trans ht
  have hcpos : 0 < c.length := c.length_pos hn
  have hpart (i : Fin c.length) (_hi : i ∈ Finset.univ) : 0 < κ i + β i := by
    rw [show κ i + β i = c.partSize i from (w.restrict (c.emb i)).arity_sum]
    exact c.partSize_pos i
  have hminus : (q.card + C * s.card - 1) + (∑ i ∈ q, cost i) =
      w.angleArity + C * w.stateArity - 1 := by
    have he := n04PositiveGeometry_inversePartition_cost Finset.univ s
      (Finset.subset_univ s) ⟨⟨0, hcpos⟩, Finset.mem_univ _⟩ κ β C hC hpart hidentity
    simpa only [q, cost, κ, β, w.sum_restrict_stateArity c,
      w.sum_restrict_angleArity c] using he
  have houterpos : 1 ≤ q.card + C * s.card := by
    by_cases hs : s.Nonempty
    · have hsc : 0 < s.card := Finset.card_pos.mpr hs
      have hmul : s.card ≤ C * s.card := by
        simpa only [one_mul] using Nat.mul_le_mul_right s.card hC
      omega
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      simpa only [q, he, Finset.sdiff_empty, Finset.card_univ, Fintype.card_fin,
        Finset.card_empty, Nat.mul_zero, Nat.add_zero] using hcpos
  have htotalpos : 1 ≤ w.angleArity + C * w.stateArity := by
    have hmul : w.stateArity ≤ C * w.stateArity := by
      simpa only [one_mul] using Nat.mul_le_mul_right w.stateArity hC
    have ha := w.arity_sum
    omega
  have hcost : (q.card + C * s.card) + (∑ i ∈ q, cost i) =
      w.angleArity + C * w.stateArity := by omega
  have hheight : parameterHeightWeight H s.card * (∏ i ∈ q, parameterHeightWeight H (κ i)) ≤
      M ^ (c.length + 1) * parameterHeightWeight H w.stateArity := by
    have hh := n04PositiveGeometry_inversePartition_height Finset.univ s
      (Finset.subset_univ s) κ (fun i hi => (hidentity i hi).1) hH hHM hM
    simpa only [q, κ, Finset.card_univ, Fintype.card_fin, w.sum_restrict_stateArity c] using hh
  have hqn : q.card ≤ n :=
    (Finset.card_le_card Finset.sdiff_subset).trans
      (by simpa only [Finset.card_univ, Fintype.card_fin] using c.length_le)
  have hprod : (∏ i, ‖n04PositiveGeometry_inverseSelectedBlock w.isState g x c s i‖) ≤
      M ^ q.card * (∏ i ∈ q, parameterHeightWeight H (κ i)) * t ^ (∑ i ∈ q, cost i) := by
    calc
      _ ≤ ∏ i, if i ∈ s then 1 else M * parameterHeightWeight H (κ i) * t ^ cost i := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro i _
        by_cases hi : i ∈ s
        · rw [if_pos hi]
          exact n04PositiveGeometry_inverseSelectedBlock_state_norm_le hg w.isState c s i hi
        · rw [if_neg hi]
          exact (n04PositiveGeometry_inverseSelectedBlock_space_norm_le hg w.isState c s i hi).trans
            (hinner i hi)
      _ = ∏ i ∈ q, M * parameterHeightWeight H (κ i) * t ^ cost i :=
        moving_prod_selected_one s _
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
        simp only [Finset.prod_const]
  have houter₀ : 0 ≤ M * parameterHeightWeight H s.card * t ^ (q.card + C * s.card) :=
    mul_nonneg (mul_nonneg hM₀ (parameterHeightWeight_nonneg hH _)) (pow_nonneg ht₀ _)
  have hpoly : M * M ^ q.card * M ^ (c.length + 1) ≤ M ^ (2 * n + 2) := by
    calc
      _ ≤ M * M ^ n * M ^ (n + 1) := mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM hqn) hM₀)
        (pow_le_pow_right₀ hM (Nat.add_le_add_right c.length_le 1))
        (pow_nonneg hM₀ _) (mul_nonneg hM₀ (pow_nonneg hM₀ _))
      _ = _ := by
        rw [show 2 * n + 2 = (n + (n + 1)) + 1 by omega, pow_succ, pow_add]
        ring
  calc
    _ ≤ ‖n04PositiveGeometry_projectedJet (fun i => decide (i ∈ s)) f
        (n04PositiveGeometry_fiberLift g x)‖ *
        ∏ i, ‖n04PositiveGeometry_inverseSelectedBlock w.isState g x c s i‖ :=
      c.norm_compAlongOrderedFinpartition_le _ _
    _ ≤ (M * parameterHeightWeight H s.card * t ^ (q.card + C * s.card)) *
        (M ^ q.card * (∏ i ∈ q, parameterHeightWeight H (κ i)) * t ^ (∑ i ∈ q, cost i)) :=
      mul_le_mul houter hprod (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) houter₀
    _ = (M * M ^ q.card) *
        (parameterHeightWeight H s.card * ∏ i ∈ q, parameterHeightWeight H (κ i)) *
          t ^ (w.angleArity + C * w.stateArity) := by
      rw [← hcost, pow_add]
      ring
    _ ≤ (M * M ^ q.card) *
        (M ^ (c.length + 1) * parameterHeightWeight H w.stateArity) *
          t ^ (w.angleArity + C * w.stateArity) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hheight (mul_nonneg hM₀ (pow_nonneg hM₀ _)))
        (pow_nonneg ht₀ _)
    _ = (M * M ^ q.card * M ^ (c.length + 1)) *
        parameterHeightWeight H w.stateArity * t ^ (w.angleArity + C * w.stateArity) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpoly (parameterHeightWeight_nonneg hH _)) (pow_nonneg ht₀ _)

/-- Actual composition retains the original finite state prefix and
the exact spatial-plus-state cost. Its only new factor is polynomial
in the common material bound. The output may be any normed space. -/
theorem n04PositiveGeometry_movingPoint_polynomial_envelope (n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧
    ∀ (M H t : ℝ), 1 ≤ M → 0 ≤ H → H ≤ M → 1 ≤ t →
    ∀ (K C : ℕ), 1 ≤ C → ∀ (f : P × V → Z) (g : P × V → V) (x : P × V),
      ContDiffAt ℝ ∞ f (n04PositiveGeometry_fiberLift g x) →
      ContDiffAt ℝ ∞ g x →
      (∀ j, 0 < j → j ≤ n → ∀ w : StateAngleWord j, w.stateArity ≤ K →
        ‖n04PositiveGeometry_projectedJet w.isState f (n04PositiveGeometry_fiberLift g x)‖ ≤
          M * parameterHeightWeight H w.stateArity * t ^ (w.angleArity + C * w.stateArity)) →
      (∀ j, 0 < j → j ≤ n → ∀ w : StateAngleWord j, w.stateArity ≤ K →
        ‖n04PositiveGeometry_projectedJet w.isState g x‖ ≤
          M * parameterHeightWeight H w.stateArity * t ^ (w.angleArity + C * w.stateArity - 1)) →
      0 < n → ∀ w : StateAngleWord n, w.stateArity ≤ K →
        ‖n04PositiveGeometry_projectedJet w.isState (f ∘ n04PositiveGeometry_fiberLift g) x‖ ≤
          A * M ^ (2 * n + 2) * parameterHeightWeight H w.stateArity *
            t ^ (w.angleArity + C * w.stateArity) := by
  classical
  let N : ℝ := ∑ c : OrderedFinpartition n, (Fintype.card (Finset (Fin c.length)) : ℝ)
  have hN : 0 ≤ N := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  refine ⟨1 + N, le_add_of_nonneg_right hN, ?_⟩
  intro M H t hM hH hHM ht K C hC f g x hf hg houter hinner hn w hw
  let R : ℝ := M ^ (2 * n + 2) * parameterHeightWeight H w.stateArity *
    t ^ (w.angleArity + C * w.stateArity)
  have hR : 0 ≤ R := mul_nonneg
    (mul_nonneg (pow_nonneg (zero_le_one.trans hM) _) (parameterHeightWeight_nonneg hH _))
    (pow_nonneg (zero_le_one.trans ht) _)
  have hterm (c : OrderedFinpartition n) (s : Finset (Fin c.length)) :
      ‖n04PositiveGeometry_inverseSelectedTerm w.isState f g x c s‖ ≤ R := by
    by_cases hid : ∀ i ∈ s, (w.restrict (c.emb i)).stateArity = 1 ∧
      (w.restrict (c.emb i)).angleArity = 0
    · have hs : s.card ≤ w.stateArity := by
        calc
          _ = ∑ i ∈ s, (w.restrict (c.emb i)).stateArity := by
            symm
            calc
              _ = ∑ _i ∈ s, (1 : ℕ) := Finset.sum_congr rfl (fun i hi => (hid i hi).1)
              _ = _ := by simp
          _ ≤ ∑ i, (w.restrict (c.emb i)).stateArity :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
              (fun _ _ _ => Nat.zero_le _)
          _ = _ := w.sum_restrict_stateArity c
      have hout := houter c.length (c.length_pos hn) c.length_le
        (StateAngleWord.ofBool (fun i => decide (i ∈ s)))
        (by simpa only [n04PositiveGeometry_selectedWord_stateArity] using hs.trans hw)
      have hout' : ‖n04PositiveGeometry_projectedJet (fun i => decide (i ∈ s)) f
          (n04PositiveGeometry_fiberLift g x)‖ ≤
          M * parameterHeightWeight H s.card * t ^ ((Finset.univ \ s).card + C * s.card) := by
        simpa only [StateAngleWord.isState_ofBool, n04PositiveGeometry_selectedWord_stateArity,
          n04PositiveGeometry_selectedWord_angleArity] using hout
      apply movingSelectedTerm_bound hg hn w c s hid C hC hM hH hHM ht hout'
      intro i _hi
      have hki : (w.restrict (c.emb i)).stateArity ≤ K :=
        ((Finset.single_le_sum
          (fun j _ => Nat.zero_le (w.restrict (c.emb j)).stateArity) (Finset.mem_univ i)).trans_eq
            (w.sum_restrict_stateArity c)).trans hw
      have hh := hinner (c.partSize i) (c.partSize_pos i) (c.partSize_le i)
        (w.restrict (c.emb i)) hki
      have he : (w.restrict (c.emb i)).isState = w.isState ∘ c.emb i := by
        funext j
        exact StateAngleWord.isState_restrict w (c.emb i) j
      simpa only [he] using hh
    · push_neg at hid
      obtain ⟨i, hi, hbad⟩ := hid
      rw [n04PositiveGeometry_inverseSelectedTerm_eq_zero hg w c s i hi hbad, norm_zero]
      exact hR
  calc
    _ ≤ ∑ c : OrderedFinpartition n, ∑ s : Finset (Fin c.length),
        ‖n04PositiveGeometry_inverseSelectedTerm w.isState f g x c s‖ :=
      n04PositiveGeometry_movingPoint_projected_norm_terms hf hg w.isState
    _ ≤ ∑ c : OrderedFinpartition n, (Fintype.card (Finset (Fin c.length)) : ℝ) * R := by
      apply Finset.sum_le_sum
      intro c _
      exact (Finset.sum_le_sum (fun s _ => hterm c s)).trans_eq
        (by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul])
    _ = N * R := (Finset.sum_mul _ _ _).symm
    _ ≤ (1 + N) * R := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hR
    _ = _ := by dsimp only [R]; ring

end ContinuousFlexibility.Analysis
